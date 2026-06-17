// SPDX-License-Identifier: MIT
//
// Morok — modular LLVM IR obfuscator.
//
// morok/passes/FunctionCallObfuscate.cpp
//
// Each eligible direct call/invoke to an external function `f(args)` becomes
//   buf = <inline, per-site decryption of the encrypted symbol name>
//   p   = dlsym(RTLD_DEFAULT, buf); p(args)
// so the static import/call edge to `f` disappears.  The symbol name is never a
// readable string and is never recovered by a single shared routine: each site
// gets its own cloaked symbol (ir::emitCloakedSymbol), so cracking one site does
// not crack the rest.  Only declared (external) symbols are redirected —
// locally-defined functions stay direct, since dlsym would not resolve them.
// On Linux x86_64 direct calls use an exception-mediated resolver: the site
// publishes a hash-guarded pending request and deliberately faults; the SIGSEGV
// handler resolves the pointer and resumes at the indirect-call continuation.

#include "morok/passes/FunctionCallObfuscate.hpp"

#include "morok/core/KnuthHash.hpp"
#include "morok/ir/SymbolCloak.hpp"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/TargetParser/Triple.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <vector>

using namespace llvm;

namespace morok::passes {

namespace {

constexpr std::uint32_t kMaxCallsPerModule = 256;
constexpr std::uint64_t kFnvOffset = 0xCBF29CE484222325ULL;
constexpr std::uint64_t kFnvPrime = 0x100000001B3ULL;

struct ExceptionRuntime {
    GlobalVariable *hash = nullptr;
    GlobalVariable *name = nullptr;
    GlobalVariable *out = nullptr;
    GlobalVariable *cont = nullptr;
};

bool eligible(CallBase *cb) {
    if (!isa<CallInst>(cb) && !isa<InvokeInst>(cb))
        return false;
    if (cb->isInlineAsm() || cb->hasOperandBundles())
        return false;
    if (auto *ci = dyn_cast<CallInst>(cb))
        if (ci->isMustTailCall())
            return false;
    Function *callee = cb->getCalledFunction();
    if (!callee || !callee->isDeclaration() || callee->isIntrinsic())
        return false;
    if (callee->getName().starts_with("llvm.") ||
        callee->getName().starts_with("morok.") || callee->getName() == "dlsym")
        return false;
    return true;
}

std::vector<Value *> argsOf(CallBase &cb) {
    std::vector<Value *> args;
    args.reserve(cb.arg_size());
    for (Use &arg : cb.args())
        args.push_back(arg.get());
    return args;
}

Value *rotl64(IRBuilder<> &B, Value *V, unsigned Amount) {
    auto *I64 = Type::getInt64Ty(B.getContext());
    return B.CreateOr(B.CreateShl(V, ConstantInt::get(I64, Amount)),
                      B.CreateLShr(V, ConstantInt::get(I64, 64 - Amount)),
                      "morok.fco.ptr.rot");
}

std::uint64_t hashName(StringRef Name) {
    std::uint64_t H = kFnvOffset;
    for (unsigned char C : Name.bytes()) {
        H ^= C;
        H *= kFnvPrime;
    }
    return H ? H : kFnvPrime;
}

bool useExceptionCalls(const Triple &TT) {
    return TT.isOSLinux() && TT.getArch() == Triple::x86_64;
}

Value *constIp(Module &M, std::uint64_t V) {
    return ConstantInt::get(M.getDataLayout().getIntPtrType(M.getContext()), V);
}

Value *gepI8(IRBuilder<> &B, Module &M, Value *Base, Value *Off,
             const Twine &Name = "") {
    return B.CreateInBoundsGEP(Type::getInt8Ty(M.getContext()), Base, Off, Name);
}

GlobalVariable *ptrGlobal(Module &M, StringRef Name) {
    if (auto *GV = M.getGlobalVariable(Name, /*AllowInternal=*/true))
        return GV;
    auto *Ptr = PointerType::getUnqual(M.getContext());
    auto *GV = new GlobalVariable(M, Ptr, /*isConstant=*/false,
                                  GlobalValue::PrivateLinkage,
                                  ConstantPointerNull::get(Ptr), Name);
    GV->setDSOLocal(true);
    return GV;
}

GlobalVariable *i64Global(Module &M, StringRef Name) {
    if (auto *GV = M.getGlobalVariable(Name, /*AllowInternal=*/true))
        return GV;
    auto *I64 = Type::getInt64Ty(M.getContext());
    auto *GV = new GlobalVariable(M, I64, /*isConstant=*/false,
                                  GlobalValue::PrivateLinkage,
                                  ConstantInt::get(I64, 0), Name);
    GV->setDSOLocal(true);
    GV->setAlignment(Align(8));
    return GV;
}

FunctionCallee dlsymDecl(Module &M) {
    auto *Ptr = PointerType::getUnqual(M.getContext());
    return M.getOrInsertFunction("dlsym",
                                 FunctionType::get(Ptr, {Ptr, Ptr}, false));
}

FunctionCallee sigactionDecl(Module &M) {
    auto *I32 = Type::getInt32Ty(M.getContext());
    auto *Ptr = PointerType::getUnqual(M.getContext());
    return M.getOrInsertFunction(
        "sigaction", FunctionType::get(I32, {I32, Ptr, Ptr}, false));
}

void zeroBytes(IRBuilder<> &B, Module &M, AllocaInst *Action,
               std::uint64_t Bytes) {
    auto *I8 = Type::getInt8Ty(M.getContext());
    for (std::uint64_t I = 0; I != Bytes; ++I)
        B.CreateStore(ConstantInt::get(I8, 0),
                      gepI8(B, M, Action, constIp(M, I)));
}

Value *runtimeHashName(IRBuilder<> &B, Module &M, Function *Fn, Value *Name) {
    LLVMContext &Ctx = M.getContext();
    auto *I8 = Type::getInt8Ty(Ctx);
    auto *I64 = Type::getInt64Ty(Ctx);

    BasicBlock *Entry = B.GetInsertBlock();
    BasicBlock *Loop = BasicBlock::Create(Ctx, "morok.fco.ex.hash.loop", Fn);
    BasicBlock *Body = BasicBlock::Create(Ctx, "morok.fco.ex.hash.body", Fn);
    BasicBlock *Done = BasicBlock::Create(Ctx, "morok.fco.ex.hash.done", Fn);
    B.CreateBr(Loop);

    IRBuilder<> LB(Loop);
    auto *Idx = LB.CreatePHI(I64, 2, "morok.fco.ex.hash.idx");
    auto *Acc = LB.CreatePHI(I64, 2, "morok.fco.ex.hash.acc");
    Idx->addIncoming(ConstantInt::get(I64, 0), Entry);
    Acc->addIncoming(ConstantInt::get(I64, kFnvOffset), Entry);
    Value *CharPtr = LB.CreateInBoundsGEP(I8, Name, Idx,
                                          "morok.fco.ex.hash.ptr");
    Value *Ch = LB.CreateLoad(I8, CharPtr, "morok.fco.ex.hash.byte");
    Value *IsNul =
        LB.CreateICmpEQ(Ch, ConstantInt::get(I8, 0), "morok.fco.ex.hash.nul");
    LB.CreateCondBr(IsNul, Done, Body);

    IRBuilder<> HB(Body);
    Value *Wide = HB.CreateZExt(Ch, I64, "morok.fco.ex.hash.zext");
    Value *Next = HB.CreateMul(HB.CreateXor(Acc, Wide, "morok.fco.ex.hash.xor"),
                              ConstantInt::get(I64, kFnvPrime),
                              "morok.fco.ex.hash.next");
    Value *NextIdx =
        HB.CreateAdd(Idx, ConstantInt::get(I64, 1), "morok.fco.ex.hash.idx2");
    HB.CreateBr(Loop);
    Idx->addIncoming(NextIdx, Body);
    Acc->addIncoming(Next, Body);

    B.SetInsertPoint(Done);
    return Acc;
}

Function *exceptionHandler(Module &M, ExceptionRuntime &Rt,
                           FunctionCallee Dlsym, int RtldDefaultVal) {
    if (auto *Existing =
            M.getFunction("morok.fco.ex.handler"))
        return Existing;

    LLVMContext &Ctx = M.getContext();
    auto *Void = Type::getVoidTy(Ctx);
    auto *I32 = Type::getInt32Ty(Ctx);
    auto *I64 = Type::getInt64Ty(Ctx);
    auto *Ptr = PointerType::getUnqual(Ctx);
    auto *FnTy = FunctionType::get(Void, {I32, Ptr, Ptr}, false);
    auto *Fn = Function::Create(FnTy, GlobalValue::InternalLinkage,
                                "morok.fco.ex.handler", M);
    Fn->setDSOLocal(true);
    auto *Sig = Fn->getArg(0);
    Sig->setName("sig");
    auto *UCtx = Fn->getArg(2);
    UCtx->setName("uctx");

    BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Fn);
    BasicBlock *HashCheck = BasicBlock::Create(Ctx, "hash", Fn);
    BasicBlock *Resolve = BasicBlock::Create(Ctx, "resolve", Fn);
    BasicBlock *Done = BasicBlock::Create(Ctx, "done", Fn);

    IRBuilder<> B(Entry);
    constexpr int kSigSegv = 11;
    Value *IsSegv = B.CreateICmpEQ(Sig, ConstantInt::get(I32, kSigSegv),
                                   "morok.fco.ex.sigsegv");
    Value *Name = B.CreateLoad(Ptr, Rt.name, "morok.fco.ex.name.load");
    Value *Out = B.CreateLoad(Ptr, Rt.out, "morok.fco.ex.out.load");
    Value *Cont = B.CreateLoad(Ptr, Rt.cont, "morok.fco.ex.cont.load");
    Value *Hash = B.CreateLoad(I64, Rt.hash, "morok.fco.ex.hash.load");
    Value *HasRequest = B.CreateAnd(
        B.CreateICmpNE(Name, ConstantPointerNull::get(Ptr)),
        B.CreateAnd(B.CreateICmpNE(Out, ConstantPointerNull::get(Ptr)),
                    B.CreateAnd(B.CreateICmpNE(Cont,
                                               ConstantPointerNull::get(Ptr)),
                                B.CreateICmpNE(Hash,
                                               ConstantInt::get(I64, 0)))));
    B.CreateCondBr(B.CreateAnd(IsSegv, HasRequest, "morok.fco.ex.claim"),
                   HashCheck, Done);

    IRBuilder<> HB(HashCheck);
    Value *Computed = runtimeHashName(HB, M, Fn, Name);
    HB.CreateCondBr(HB.CreateICmpEQ(Computed, Hash, "morok.fco.ex.hash.match"),
                    Resolve, Done);

    IRBuilder<> RB(Resolve);
    Value *Rtld = RB.CreateIntToPtr(ConstantInt::getSigned(I64, RtldDefaultVal),
                                    Ptr);
    Value *Resolved = RB.CreateCall(Dlsym, {Rtld, Name},
                                    "morok.fco.ex.resolved");
    RB.CreateStore(Resolved, Out);
    RB.CreateStore(ConstantPointerNull::get(Ptr), Rt.name);
    RB.CreateStore(ConstantPointerNull::get(Ptr), Rt.out);
    RB.CreateStore(ConstantPointerNull::get(Ptr), Rt.cont);
    RB.CreateStore(ConstantInt::get(I64, 0), Rt.hash);
    Value *RipSlot =
        gepI8(RB, M, UCtx, constIp(M, 168), "morok.fco.ex.rip.slot");
    RB.CreateStore(RB.CreatePtrToInt(Cont, M.getDataLayout().getIntPtrType(Ctx),
                                     "morok.fco.ex.rip"),
                   RipSlot);
    RB.CreateBr(Done);

    IRBuilder<> DB(Done);
    DB.CreateRetVoid();
    return Fn;
}

void storeSigaction(IRBuilder<> &B, Module &M, AllocaInst *Action,
                    Function *Handler) {
    auto *I32 = Type::getInt32Ty(M.getContext());
    constexpr std::uint64_t kSigactionSize = 152;
    constexpr std::uint64_t kFlagsOffset = 136;
    constexpr std::uint32_t kSaSiginfo = 4;

    zeroBytes(B, M, Action, kSigactionSize);
    B.CreateStore(Handler,
                  gepI8(B, M, Action, constIp(M, 0), "morok.fco.ex.sa.fn"));
    B.CreateStore(ConstantInt::get(I32, kSaSiginfo),
                  gepI8(B, M, Action, constIp(M, kFlagsOffset),
                        "morok.fco.ex.sa.flags"));
}

ExceptionRuntime ensureExceptionRuntime(Module &M, FunctionCallee Dlsym,
                                        int RtldDefaultVal) {
    ExceptionRuntime Rt;
    Rt.hash = i64Global(M, "morok.fco.ex.pending.hash");
    Rt.name = ptrGlobal(M, "morok.fco.ex.pending.name");
    Rt.out = ptrGlobal(M, "morok.fco.ex.pending.out");
    Rt.cont = ptrGlobal(M, "morok.fco.ex.pending.cont");

    if (M.getFunction("morok.fco.ex.install"))
        return Rt;

    LLVMContext &Ctx = M.getContext();
    auto *Void = Type::getVoidTy(Ctx);
    auto *I8 = Type::getInt8Ty(Ctx);
    auto *I32 = Type::getInt32Ty(Ctx);
    auto *Ptr = PointerType::getUnqual(Ctx);
    Function *Handler = exceptionHandler(M, Rt, Dlsym, RtldDefaultVal);
    auto *Ctor = Function::Create(FunctionType::get(Void, false),
                                  GlobalValue::InternalLinkage,
                                  "morok.fco.ex.install", M);
    Ctor->setDSOLocal(true);
    BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Ctor);
    IRBuilder<> B(Entry);
    auto *ActionTy = ArrayType::get(I8, 152);
    AllocaInst *Action =
        B.CreateAlloca(ActionTy, nullptr, "morok.fco.ex.sa");
    storeSigaction(B, M, Action, Handler);
    constexpr int kSigSegv = 11;
    B.CreateCall(sigactionDecl(M),
                 {ConstantInt::get(I32, kSigSegv), Action,
                  ConstantPointerNull::get(Ptr)});
    B.CreateRetVoid();
    appendToGlobalCtors(M, Ctor, 0);
    return Rt;
}

void emitFault(IRBuilder<> &B) {
    auto *AsmTy = FunctionType::get(Type::getVoidTy(B.getContext()), false);
    InlineAsm *IA = InlineAsm::get(
        AsmTy, "xorq %rax, %rax\n\tmovq %rax, (%rax)",
        "~{rax},~{dirflag},~{fpsr},~{flags},~{memory}",
        /*hasSideEffects=*/true);
    B.CreateCall(AsmTy, IA);
}

Value *pointerKey(IRBuilder<> &B, Module &M, ir::IRRandom &rng,
                  std::uint64_t SiteKey, unsigned Variant,
                  std::uint64_t Mul, std::uint64_t Mask) {
    auto *I64 = Type::getInt64Ty(M.getContext());
    GlobalVariable *Seed = ir::cloakSeed(M, rng);
    LoadInst *SeedLoad =
        B.CreateLoad(I64, Seed, /*isVolatile=*/true, "morok.fco.ptr.seed");
    Value *K0 = B.CreateXor(SeedLoad, ConstantInt::get(I64, SiteKey),
                            "morok.fco.ptr.k0");
    Value *K = ir::emitKeystream(B, Variant, K0, 0, Mul);
    return B.CreateXor(K, ConstantInt::get(I64, Mask), "morok.fco.ptr.key");
}

AllocaInst *entryAlloca(Function &F, Type *Ty, StringRef Name);

Value *encodeResolvedPointer(IRBuilder<> &B, Module &M, Value *Resolved,
                             ir::IRRandom &rng);

Value *emitResolvedViaException(CallInst *CI, Module &M, ExceptionRuntime &Rt,
                                Value *Name, std::uint64_t Hash,
                                ir::IRRandom &rng) {
    Function *Parent = CI->getFunction();
    BasicBlock *Pre = CI->getParent();
    BasicBlock *Cont = SplitBlock(Pre, CI);
    Cont->setName("morok.fco.ex.cont");
    Instruction *Term = Pre->getTerminator();
    IRBuilder<> B(Term);
    auto *I64 = Type::getInt64Ty(M.getContext());
    auto *Ptr = PointerType::getUnqual(M.getContext());
    AllocaInst *Slot = entryAlloca(*Parent, Ptr, "morok.fco.ex.slot");

    B.CreateStore(ConstantPointerNull::get(Ptr), Slot);
    B.CreateStore(ConstantInt::get(I64, Hash), Rt.hash);
    B.CreateStore(Name, Rt.name);
    B.CreateStore(Slot, Rt.out);
    B.CreateStore(BlockAddress::get(Parent, Cont), Rt.cont);
    emitFault(B);

    IRBuilder<> CB(CI);
    LoadInst *Resolved =
        CB.CreateLoad(Ptr, Slot, "morok.fco.ex.resolved.reload");
    Resolved->setVolatile(true);
    return encodeResolvedPointer(CB, M, Resolved, rng);
}

AllocaInst *entryAlloca(Function &F, Type *Ty, StringRef Name) {
    IRBuilder<> EntryB(&*F.getEntryBlock().getFirstInsertionPt());
    return EntryB.CreateAlloca(Ty, nullptr, Name);
}

Value *encodeResolvedPointer(IRBuilder<> &B, Module &M, Value *Resolved,
                             ir::IRRandom &rng) {
    auto *I64 = Type::getInt64Ty(M.getContext());
    const unsigned Variant = rng.range(ir::kKeystreamVariants);
    const unsigned Mode = rng.range(3);
    const std::uint64_t SiteKey = rng.next();
    const std::uint64_t Mul = rng.next() | 1ull;
    const std::uint64_t Mask = rng.next();
    const std::uint64_t PtrMul = rng.next() | 1ull;
    const std::uint64_t PtrMulInv = core::modInverse64(PtrMul);

    Value *Raw = B.CreatePtrToInt(Resolved, I64, "morok.fco.ptr.raw");
    Value *EncKey = pointerKey(B, M, rng, SiteKey, Variant, Mul, Mask);
    Value *Encoded = nullptr;
    switch (Mode) {
    case 1:
        Encoded = B.CreateXor(B.CreateAdd(Raw, EncKey, "morok.fco.ptr.add"),
                              rotl64(B, EncKey, 29), "morok.fco.ptr.enc");
        break;
    case 2:
        Encoded = B.CreateXor(
            B.CreateMul(B.CreateAdd(Raw, EncKey, "morok.fco.ptr.add"),
                        ConstantInt::get(I64, PtrMul), "morok.fco.ptr.mul"),
            EncKey, "morok.fco.ptr.enc");
        break;
    default:
        Encoded = B.CreateAdd(B.CreateXor(Raw, EncKey, "morok.fco.ptr.xor"),
                              rotl64(B, EncKey, 17), "morok.fco.ptr.enc");
        break;
    }

    AllocaInst *Slot =
        entryAlloca(*B.GetInsertBlock()->getParent(), I64, "morok.fco.ptr.slot");
    B.CreateStore(Encoded, Slot, /*isVolatile=*/true);
    LoadInst *EncodedLoad =
        B.CreateLoad(I64, Slot, /*isVolatile=*/true, "morok.fco.ptr.reload");
    Value *DecKey = pointerKey(B, M, rng, SiteKey, Variant, Mul, Mask);
    Value *DecodedInt = nullptr;
    switch (Mode) {
    case 1:
        DecodedInt = B.CreateSub(B.CreateXor(EncodedLoad, rotl64(B, DecKey, 29),
                                             "morok.fco.ptr.unxor"),
                                 DecKey, "morok.fco.ptr.dec.i");
        break;
    case 2:
        DecodedInt = B.CreateSub(
            B.CreateMul(B.CreateXor(EncodedLoad, DecKey, "morok.fco.ptr.unxor"),
                        ConstantInt::get(I64, PtrMulInv),
                        "morok.fco.ptr.unmul"),
            DecKey, "morok.fco.ptr.dec.i");
        break;
    default:
        DecodedInt = B.CreateXor(
            B.CreateSub(EncodedLoad, rotl64(B, DecKey, 17),
                        "morok.fco.ptr.unadd"),
            DecKey, "morok.fco.ptr.dec.i");
        break;
    }
    return B.CreateIntToPtr(DecodedInt, PointerType::getUnqual(M.getContext()),
                            "morok.fco.ptr.dec");
}

} // namespace

bool functionCallObfuscateModule(Module &M, const FcoParams &params,
                                 ir::IRRandom &rng) {
    if (params.probability == 0 || params.max_calls == 0)
        return false;

    const std::uint32_t Limit = std::min(params.max_calls, kMaxCallsPerModule);

    std::vector<CallBase *> targets;
    targets.reserve(Limit);
    for (Function &F : M) {
        if (targets.size() >= Limit)
            break;
        if (F.isDeclaration() || F.getName().starts_with("morok."))
            continue;
        for (Instruction &inst : instructions(F)) {
            if (targets.size() >= Limit)
                break;
            if (auto *cb = dyn_cast<CallBase>(&inst))
                if (eligible(cb))
                    if (rng.chance(params.probability))
                        targets.push_back(cb);
        }
    }
    if (targets.empty())
        return false;

    LLVMContext &ctx = M.getContext();
    auto *i64 = Type::getInt64Ty(ctx);
    auto *ptr = PointerType::getUnqual(ctx);
    const Triple tt(M.getTargetTriple());
    const int rtldDefaultVal = tt.isOSDarwin() ? -2 : 0; // RTLD_DEFAULT

    FunctionCallee dlsym = dlsymDecl(M);
    const bool exceptionCalls = useExceptionCalls(tt);
    ExceptionRuntime exceptionRt;
    if (exceptionCalls)
        exceptionRt = ensureExceptionRuntime(M, dlsym, rtldDefaultVal);

    bool changed = false;
    for (CallBase *cb : targets) {
        Function *callee = cb->getCalledFunction();

        IRBuilder<> B(cb);
        // dlsym needs the plain C symbol name.  LLVM may carry a `\01`-escaped
        // asm name (e.g. macOS libc's `\01_fwrite`); strip the escape and the
        // platform underscore, otherwise dlsym returns null and the redirected
        // call jumps to address 0.
        StringRef dlName = callee->getName();
        if (dlName.consume_front(StringRef("\x01", 1)) && tt.isOSDarwin())
            dlName.consume_front("_");
        Value *name = ir::emitCloakedSymbol(B, M, dlName, rng);
        Value *decoded = nullptr;
        if (exceptionCalls && isa<CallInst>(cb)) {
            decoded = emitResolvedViaException(cast<CallInst>(cb), M,
                                               exceptionRt, name,
                                               hashName(dlName), rng);
        } else {
            Value *rtld = B.CreateIntToPtr(
                ConstantInt::getSigned(i64, rtldDefaultVal), ptr);
            Value *resolved = B.CreateCall(dlsym, {rtld, name});
            decoded = encodeResolvedPointer(B, M, resolved, rng);
        }

        std::vector<Value *> args = argsOf(*cb);
        CallBase *indirect = nullptr;
        IRBuilder<> CallB(cb);
        if (auto *ci = dyn_cast<CallInst>(cb)) {
            auto *call =
                CallB.CreateCall(callee->getFunctionType(), decoded, args);
            call->setTailCallKind(ci->getTailCallKind());
            indirect = call;
        } else {
            auto *ii = cast<InvokeInst>(cb);
            indirect =
                CallB.CreateInvoke(callee->getFunctionType(), decoded,
                                   ii->getNormalDest(), ii->getUnwindDest(),
                                   args);
        }
        indirect->setCallingConv(cb->getCallingConv());
        indirect->setAttributes(cb->getAttributes());
        indirect->setDebugLoc(cb->getDebugLoc());
        indirect->copyMetadata(*cb);

        cb->replaceAllUsesWith(indirect);
        cb->eraseFromParent();
        changed = true;
    }
    return changed;
}

PreservedAnalyses FunctionCallObfuscatePass::run(Module &M,
                                                 ModuleAnalysisManager &) {
    ir::IRRandom rng(engine_);
    return functionCallObfuscateModule(M, params_, rng)
               ? PreservedAnalyses::none()
               : PreservedAnalyses::all();
}

} // namespace morok::passes
