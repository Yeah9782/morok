// SPDX-License-Identifier: MIT
//
// Morok — modular LLVM IR obfuscator.
//
// morok/passes/FaultPagedPayload.cpp
//
// VM bytecode delivery that keeps only one encrypted page materialized.  The VM
// helpers produced by Virtualization.cpp read morok.vm.bytecode.* through
// volatile i8 loads.  This pass replaces those loads with a per-payload accessor
// that decrypts only the touched page into a per-thread fixed-size cache,
// clears the cache on page switches, and leaves the original bytecode global
// encrypted.

#include "morok/passes/FaultPagedPayload.hpp"

#include "morok/passes/RuntimeSeal.hpp"

#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/NoFolder.h"
#include "llvm/IR/Operator.h"
#include "llvm/Support/ModRef.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

#include <algorithm>
#include <cstdint>
#include <array>
#include <string>
#include <vector>

using namespace llvm;

namespace morok::passes {

namespace {

constexpr StringLiteral kBytecodePrefix("morok.vm.bytecode.");
constexpr std::uint32_t kInvalidPage = 0xFFFFFFFFu;
constexpr std::uint32_t kMinPageSize = 16;
constexpr std::uint32_t kMaxPageSize = 4096;

using Builder = IRBuilder<NoFolder>;

struct PageSchedule {
    std::uint64_t salt = 0;
    std::uint64_t page_mul = 1;
    std::uint64_t index_mul = 1;
    std::uint64_t bias = 0;
    std::uint8_t xork = 0;
};

struct Payload {
    GlobalVariable *bytecode = nullptr;
    Function *helper = nullptr;
    std::string suffix;
    std::vector<std::uint8_t> original;
};

std::uint64_t mix64(std::uint64_t X) {
    X ^= X >> 33;
    X *= 0xff51afd7ed558ccdULL;
    X ^= X >> 29;
    X *= 0xc4ceb9fe1a85ec53ULL;
    X ^= X >> 32;
    return X;
}

PageSchedule makeSchedule(ir::IRRandom &Rng) {
    PageSchedule S;
    S.salt = Rng.next();
    S.page_mul = Rng.next() | 1ULL;
    S.index_mul = Rng.next() | 1ULL;
    S.bias = Rng.next();
    S.xork = static_cast<std::uint8_t>(Rng.next());
    return S;
}

std::uint8_t keyByte(std::uint32_t Index, std::uint32_t Page,
                     const PageSchedule &S, bool PerPageKeys) {
    const std::uint64_t PageTerm =
        PerPageKeys ? (static_cast<std::uint64_t>(Page) + 1ULL) * S.page_mul
                    : S.page_mul;
    std::uint64_t X = S.salt ^ PageTerm;
    X += (static_cast<std::uint64_t>(Index) + 0x9E3779B9ULL) * S.index_mul;
    X ^= S.bias + (static_cast<std::uint64_t>(Index & 7u) << 56);
    X = mix64(X);
    const unsigned Shift = (Index & 7u) * 8u;
    return static_cast<std::uint8_t>(X >> Shift) ^ S.xork;
}

Value *mix64(Builder &B, Value *X, const Twine &Name) {
    auto *I64 = B.getInt64Ty();
    X = B.CreateXor(X, B.CreateLShr(X, ConstantInt::get(I64, 33)),
                    Name + ".fold33");
    X = B.CreateMul(X, ConstantInt::get(I64, 0xff51afd7ed558ccdULL),
                    Name + ".mul0");
    X = B.CreateXor(X, B.CreateLShr(X, ConstantInt::get(I64, 29)),
                    Name + ".fold29");
    X = B.CreateMul(X, ConstantInt::get(I64, 0xc4ceb9fe1a85ec53ULL),
                    Name + ".mul1");
    return B.CreateXor(X, B.CreateLShr(X, ConstantInt::get(I64, 32)),
                       Name + ".fold32");
}

Value *emitKeyByte(Builder &B, Value *Index, Value *Page,
                   Value *RuntimeDelta, const PageSchedule &S,
                   bool PerPageKeys, const Twine &Name) {
    auto *I64 = B.getInt64Ty();
    auto *I8 = B.getInt8Ty();
    Value *Index64 = B.CreateZExt(Index, I64, Name + ".index");
    Value *Page64 = B.CreateZExt(Page, I64, Name + ".page");
    Value *PageTerm =
        PerPageKeys
            ? B.CreateMul(B.CreateAdd(Page64, ConstantInt::get(I64, 1)),
                          ConstantInt::get(I64, S.page_mul),
                          Name + ".page.mul")
            : ConstantInt::get(I64, S.page_mul);
    Value *X = B.CreateXor(ConstantInt::get(I64, S.salt), PageTerm,
                           Name + ".mix");
    Value *IdxTerm = B.CreateMul(
        B.CreateAdd(Index64, ConstantInt::get(I64, 0x9E3779B9ULL),
                    Name + ".index.bias"),
        ConstantInt::get(I64, S.index_mul), Name + ".index.mul");
    X = B.CreateAdd(X, IdxTerm, Name + ".mix");
    Value *ShiftBits = B.CreateShl(
        B.CreateAnd(Index64, ConstantInt::get(I64, 7), Name + ".lane"),
        ConstantInt::get(I64, 3), Name + ".shift");
    Value *LaneSalt =
        B.CreateShl(B.CreateAnd(Index64, ConstantInt::get(I64, 7)),
                    ConstantInt::get(I64, 56), Name + ".lane.salt");
    X = B.CreateXor(X,
                    B.CreateAdd(ConstantInt::get(I64, S.bias), LaneSalt,
                                Name + ".bias"),
                    Name + ".mix");
    X = B.CreateXor(X, RuntimeDelta, Name + ".seal");
    X = mix64(B, X, Name + ".kdf");
    Value *K = B.CreateTrunc(B.CreateLShr(X, ShiftBits, Name + ".select"),
                             I8, Name + ".trunc");
    return B.CreateXor(K, ConstantInt::get(I8, S.xork), Name);
}

std::vector<std::uint8_t> encrypt(ArrayRef<std::uint8_t> Plain,
                                  std::uint32_t PageSize,
                                  const PageSchedule &S, bool PerPageKeys) {
    std::vector<std::uint8_t> Cipher;
    Cipher.reserve(Plain.size());
    for (std::uint32_t I = 0; I < Plain.size(); ++I) {
        const std::uint32_t Page = I / PageSize;
        Cipher.push_back(
            static_cast<std::uint8_t>(Plain[I] ^
                                      keyByte(I, Page, S, PerPageKeys)));
    }
    return Cipher;
}

Function *helperFor(Module &M, StringRef Suffix) {
    return M.getFunction(std::string("morok.vm.") + Suffix.str() + ".exec");
}

std::vector<std::uint8_t> readBytes(GlobalVariable &GV) {
    std::vector<std::uint8_t> Bytes;
    auto *Data = dyn_cast<ConstantDataArray>(GV.getInitializer());
    if (!Data)
        return Bytes;
    Bytes.reserve(Data->getNumElements());
    for (unsigned I = 0; I < Data->getNumElements(); ++I)
        Bytes.push_back(
            static_cast<std::uint8_t>(Data->getElementAsInteger(I)));
    return Bytes;
}

std::vector<Payload> collectPayloads(Module &M,
                                     std::uint32_t MaxPayloadBytes) {
    std::vector<Payload> Payloads;
    if (MaxPayloadBytes == 0)
        return Payloads;
    for (GlobalVariable &GV : M.globals()) {
        if (!GV.getName().starts_with(kBytecodePrefix))
            continue;
        if (!GV.hasInitializer() || !GV.isConstant())
            continue;
        auto *ArrTy = dyn_cast<ArrayType>(GV.getValueType());
        if (!ArrTy || !ArrTy->getElementType()->isIntegerTy(8) ||
            ArrTy->getNumElements() == 0 ||
            ArrTy->getNumElements() > MaxPayloadBytes)
            continue;
        std::string Suffix =
            GV.getName().drop_front(kBytecodePrefix.size()).str();
        if (M.getFunction("morok.fpp.load." + Suffix))
            continue;
        Function *Helper = helperFor(M, Suffix);
        if (!Helper || Helper->isDeclaration())
            continue;
        std::vector<std::uint8_t> Bytes = readBytes(GV);
        if (Bytes.empty())
            continue;
        Payloads.push_back({&GV, Helper, std::move(Suffix), std::move(Bytes)});
    }
    return Payloads;
}

void shufflePayloads(std::vector<Payload> &Payloads, ir::IRRandom &Rng) {
    for (std::size_t I = Payloads.size(); I > 1; --I) {
        const std::size_t J = Rng.range(static_cast<std::uint32_t>(I));
        std::swap(Payloads[I - 1], Payloads[J]);
    }
}

void makeMutableCiphertext(GlobalVariable &GV, ArrayRef<std::uint8_t> Cipher) {
    auto *Init = ConstantDataArray::get(GV.getContext(), Cipher);
    GV.setInitializer(Init);
    GV.setConstant(false);
    GV.setUnnamedAddr(GlobalValue::UnnamedAddr::None);
    GV.setAlignment(Align(1));
}

GlobalVariable *createByteArray(Module &M, ArrayRef<std::uint8_t> Bytes,
                                StringRef Name, bool Constant) {
    auto *I8 = Type::getInt8Ty(M.getContext());
    auto *ArrTy = ArrayType::get(I8, Bytes.size());
    auto *Init = ConstantDataArray::get(M.getContext(), Bytes);
    auto *GV = new GlobalVariable(M, ArrTy, Constant,
                                  GlobalValue::PrivateLinkage, Init,
                                  Name.str());
    GV->setAlignment(Align(1));
    return GV;
}

GlobalVariable *createZeroArray(Module &M, std::uint32_t Count,
                                StringRef Name) {
    auto *I8 = Type::getInt8Ty(M.getContext());
    auto *ArrTy = ArrayType::get(I8, Count);
    auto *GV = new GlobalVariable(M, ArrTy, /*isConstant=*/false,
                                  GlobalValue::PrivateLinkage,
                                  ConstantAggregateZero::get(ArrTy),
                                  Name.str());
    GV->setAlignment(Align(1));
    return GV;
}

GlobalVariable *createI32State(Module &M, StringRef Name,
                               std::uint32_t Initial) {
    auto *I32 = Type::getInt32Ty(M.getContext());
    auto *GV = new GlobalVariable(M, I32, /*isConstant=*/false,
                                  GlobalValue::PrivateLinkage,
                                  ConstantInt::get(I32, Initial), Name.str());
    GV->setAlignment(Align(4));
    return GV;
}

GlobalVariable *createI64State(Module &M, StringRef Name,
                               std::uint64_t Initial) {
    auto *I64 = Type::getInt64Ty(M.getContext());
    auto *GV = new GlobalVariable(M, I64, /*isConstant=*/false,
                                  GlobalValue::PrivateLinkage,
                                  ConstantInt::get(I64, Initial), Name.str());
    GV->setAlignment(Align(8));
    return GV;
}

GlobalVariable *makeThreadLocal(GlobalVariable *GV) {
    GV->setThreadLocalMode(GlobalVariable::GeneralDynamicTLSModel);
    return GV;
}

GlobalVariable *createMeta(Module &M, StringRef Suffix, std::uint32_t Size,
                           std::uint32_t PageSize, std::uint32_t PageCount,
                           const PageSchedule &S) {
    auto *I64 = Type::getInt64Ty(M.getContext());
    const std::uint64_t Fingerprint =
        mix64(S.salt ^ S.page_mul ^ S.index_mul ^ S.bias);
    const std::uint64_t LayoutCookie =
        mix64((static_cast<std::uint64_t>(Size) << 32) ^
              (static_cast<std::uint64_t>(PageSize) << 16) ^ PageCount ^
              S.xork);
    std::array<Constant *, 5> Vals = {
        ConstantInt::get(I64, Size),
        ConstantInt::get(I64, PageSize),
        ConstantInt::get(I64, PageCount),
        ConstantInt::get(I64, Fingerprint),
        ConstantInt::get(I64, LayoutCookie),
    };
    auto *ArrTy = ArrayType::get(I64, Vals.size());
    auto *GV = new GlobalVariable(
        M, ArrTy, /*isConstant=*/true, GlobalValue::PrivateLinkage,
        ConstantArray::get(ArrTy, Vals), ("morok.fpp.meta." + Suffix).str());
    GV->setAlignment(Align(8));
    return GV;
}

GlobalVariable *createDecoys(Module &M, StringRef Suffix,
                             std::uint32_t DecoyPages,
                             std::uint32_t PageSize, ir::IRRandom &Rng) {
    if (DecoyPages == 0 || PageSize == 0)
        return nullptr;
    const std::uint64_t Bytes64 =
        static_cast<std::uint64_t>(DecoyPages) * PageSize;
    if (Bytes64 == 0 || Bytes64 > 64u * 1024u)
        return nullptr;
    std::vector<std::uint8_t> Bytes(static_cast<std::size_t>(Bytes64));
    for (std::uint8_t &B : Bytes)
        B = static_cast<std::uint8_t>(Rng.next());
    return createByteArray(M, Bytes, ("morok.fpp.decoy." + Suffix).str(),
                           true);
}

// Resolve the storage pointer for a (possibly thread-local) global.  A
// thread-local global's symbol names only its per-thread TEMPLATE; a direct
// load/store/GEP through it touches that template (shared / read-only) instead
// of the calling thread's instance — so the per-thread page cache (#99) faults
// (EXC_BAD_ACCESS writing the template) or silently shares state.
// llvm.threadlocal.address maps the global to the current thread's copy, which
// is required to make the thread-local cache actually per-thread.
Value *statePtr(Builder &B, GlobalVariable *GV) {
    if (GV->isThreadLocal())
        return B.CreateThreadLocalAddress(GV);
    return GV;
}

Value *globalBytePtr(Builder &B, GlobalVariable *GV, Value *Idx,
                     const Twine &Name) {
    auto *I32 = B.getInt32Ty();
    auto *ArrTy = cast<ArrayType>(GV->getValueType());
    return B.CreateInBoundsGEP(ArrTy, statePtr(B, GV),
                               {ConstantInt::get(I32, 0), Idx}, Name);
}

LoadInst *volatileLoadI8(Builder &B, Value *Ptr, const Twine &Name) {
    auto *Load = B.CreateLoad(B.getInt8Ty(), Ptr, Name);
    Load->setVolatile(true);
    Load->setAlignment(Align(1));
    return Load;
}

StoreInst *volatileStore(Builder &B, Value *Val, Value *Ptr) {
    auto *Store = B.CreateStore(Val, Ptr);
    Store->setVolatile(true);
    Store->setAlignment(Align(1));
    return Store;
}

Function *createAccessor(Module &M, Payload &P,
                         const FaultPagedPayloadParams &Params,
                         std::uint32_t PageSize, std::uint32_t PageCount,
                         const PageSchedule &S, GlobalVariable *Cache,
                         GlobalVariable *Loaded, GlobalVariable *Active,
                         GlobalVariable *Faults) {
    LLVMContext &Ctx = M.getContext();
    auto *I8 = Type::getInt8Ty(Ctx);
    auto *I32 = Type::getInt32Ty(Ctx);
    auto *I64 = Type::getInt64Ty(Ctx);
    auto *FnTy = FunctionType::get(I8, {I32}, false);
    auto *F = Function::Create(FnTy, GlobalValue::PrivateLinkage,
                               "morok.fpp.load." + P.suffix, M);
    F->setCallingConv(CallingConv::C);
    F->addFnAttr(Attribute::NoInline);
    F->addFnAttr(Attribute::OptimizeNone);
    F->setMemoryEffects(MemoryEffects::unknown());
    if (!Params.virtualize_helpers)
        F->addFnAttr("morok.fpp.no_vm");

    BasicBlock *Entry = BasicBlock::Create(Ctx, "morok.fpp.entry", F);
    BasicBlock *Fault = BasicBlock::Create(Ctx, "morok.fpp.fault", F);
    BasicBlock *ClearLoop =
        Params.reseal_after_use
            ? BasicBlock::Create(Ctx, "morok.fpp.clear", F)
            : nullptr;
    BasicBlock *ClearDone =
        Params.reseal_after_use
            ? BasicBlock::Create(Ctx, "morok.fpp.clear.done", F)
            : nullptr;
    BasicBlock *DecryptLoop = BasicBlock::Create(Ctx, "morok.fpp.decrypt", F);
    BasicBlock *Return = BasicBlock::Create(Ctx, "morok.fpp.return", F);

    Builder B(Entry);
    Value *Index = F->getArg(0);
    Index->setName("morok.fpp.index");
    const auto Size = static_cast<std::uint32_t>(P.original.size());
    Value *BadIndex =
        B.CreateICmpUGE(Index, ConstantInt::get(I32, Size), "morok.fpp.bad");
    Value *WrappedIndex =
        B.CreateURem(Index, ConstantInt::get(I32, Size), "morok.fpp.wrap");
    Value *SafeIndex =
        B.CreateSelect(BadIndex, WrappedIndex, Index, "morok.fpp.safe");
    Value *Page =
        B.CreateUDiv(SafeIndex, ConstantInt::get(I32, PageSize),
                     "morok.fpp.page.index");
    Value *InPage =
        B.CreateURem(SafeIndex, ConstantInt::get(I32, PageSize),
                     "morok.fpp.page.offset");
    auto *ActiveLoad =
        B.CreateLoad(I32, statePtr(B, Active), "morok.fpp.page.active.load");
    ActiveLoad->setVolatile(true);
    ActiveLoad->setAlignment(Align(4));
    Value *LoadedPtr =
        globalBytePtr(B, Loaded, Page, "morok.fpp.page.loaded.ptr");
    Value *LoadedByte = volatileLoadI8(B, LoadedPtr, "morok.fpp.page.loaded");
    Value *IsLoaded =
        B.CreateICmpNE(LoadedByte, ConstantInt::get(I8, 0),
                       "morok.fpp.page.loaded.ok");
    Value *SamePage =
        B.CreateICmpEQ(ActiveLoad, Page, "morok.fpp.page.active.same");
    Value *NeedFault =
        B.CreateNot(B.CreateAnd(IsLoaded, SamePage, "morok.fpp.page.ready"),
                    "morok.fpp.page.fault");
    B.CreateCondBr(NeedFault, Fault, Return);

    B.SetInsertPoint(Fault);
    if (Params.reseal_after_use)
        B.CreateBr(ClearLoop);
    else
        B.CreateBr(DecryptLoop);

    if (Params.reseal_after_use) {
        B.SetInsertPoint(ClearLoop);
        PHINode *ClearIdx = B.CreatePHI(I32, 2, "morok.fpp.clear.i");
        ClearIdx->addIncoming(ConstantInt::get(I32, 0), Fault);
        Value *ClearPtr =
            globalBytePtr(B, Cache, ClearIdx, "morok.fpp.cache.clear");
        volatileStore(B, ConstantInt::get(I8, 0), ClearPtr);
        Value *ClearNext = B.CreateAdd(ClearIdx, ConstantInt::get(I32, 1),
                                       "morok.fpp.clear.next");
        ClearIdx->addIncoming(ClearNext, ClearLoop);
        Value *ClearMore =
            B.CreateICmpULT(ClearNext, ConstantInt::get(I32, PageSize),
                            "morok.fpp.clear.more");
        B.CreateCondBr(ClearMore, ClearLoop, ClearDone);

        B.SetInsertPoint(ClearDone);
        Value *OldValid =
            B.CreateICmpULT(ActiveLoad, ConstantInt::get(I32, PageCount),
                            "morok.fpp.old.valid");
        Value *OldPage =
            B.CreateSelect(OldValid, ActiveLoad, ConstantInt::get(I32, 0),
                           "morok.fpp.old.page");
        Value *OldLoadedPtr =
            globalBytePtr(B, Loaded, OldPage, "morok.fpp.old.loaded.ptr");
        StoreInst *ClearLoaded =
            volatileStore(B, ConstantInt::get(I8, 0), OldLoadedPtr);
        ClearLoaded->setAlignment(Align(1));
        B.CreateBr(DecryptLoop);
    }

    B.SetInsertPoint(DecryptLoop);
    PHINode *J = B.CreatePHI(I32, 2, "morok.fpp.decrypt.i");
    J->addIncoming(ConstantInt::get(I32, 0),
                   Params.reseal_after_use ? ClearDone : Fault);
    Value *PageBase =
        B.CreateMul(Page, ConstantInt::get(I32, PageSize),
                    "morok.fpp.page.base");
    Value *GlobalIndex =
        B.CreateAdd(PageBase, J, "morok.fpp.global.index");
    Value *InRange =
        B.CreateICmpULT(GlobalIndex, ConstantInt::get(I32, Size),
                        "morok.fpp.global.range");
    Value *CipherIndex =
        B.CreateSelect(InRange, GlobalIndex, ConstantInt::get(I32, 0),
                       "morok.fpp.cipher.index");
    Value *CipherPtr =
        globalBytePtr(B, P.bytecode, CipherIndex, "morok.fpp.cipher.ptr");
    Value *Cipher = volatileLoadI8(B, CipherPtr, "morok.fpp.cipher.byte");
    Value *SealDelta =
        Params.bind_to_runtime_seal
            ? runtime_seal::emitChannelDelta(B,
                                             runtime_seal::
                                                 kFaultPagedPayloadChannel,
                                             "morok.fpp.seal")
            : ConstantInt::get(I64, 0);
    Value *Key = emitKeyByte(B, GlobalIndex, Page, SealDelta, S,
                             Params.per_page_keys, "morok.fpp.page.key");
    Value *Plain = B.CreateXor(Cipher, Key, "morok.fpp.plain.byte");
    Plain = B.CreateSelect(InRange, Plain, ConstantInt::get(I8, 0),
                           "morok.fpp.plain.masked");
    Value *CachePtr = globalBytePtr(B, Cache, J, "morok.fpp.cache.ptr");
    volatileStore(B, Plain, CachePtr);
    Value *JNext =
        B.CreateAdd(J, ConstantInt::get(I32, 1), "morok.fpp.decrypt.next");
    J->addIncoming(JNext, DecryptLoop);
    Value *More = B.CreateICmpULT(JNext, ConstantInt::get(I32, PageSize),
                                  "morok.fpp.decrypt.more");
    BasicBlock *DecryptDone =
        BasicBlock::Create(Ctx, "morok.fpp.decrypt.done", F);
    B.CreateCondBr(More, DecryptLoop, DecryptDone);

    B.SetInsertPoint(DecryptDone);
    volatileStore(B, ConstantInt::get(I8, 1), LoadedPtr);
    auto *ActiveStore = B.CreateStore(Page, statePtr(B, Active));
    ActiveStore->setVolatile(true);
    ActiveStore->setAlignment(Align(4));
    auto *FaultLoad =
        B.CreateLoad(I64, statePtr(B, Faults), "morok.fpp.fault.count.load");
    FaultLoad->setVolatile(true);
    FaultLoad->setAlignment(Align(8));
    Value *FaultNext =
        B.CreateAdd(FaultLoad, ConstantInt::get(I64, 1),
                    "morok.fpp.fault.count.next");
    auto *FaultStore = B.CreateStore(FaultNext, statePtr(B, Faults));
    FaultStore->setVolatile(true);
    FaultStore->setAlignment(Align(8));
    if (Params.bind_to_runtime_seal)
        runtime_seal::foldFlag(B, runtime_seal::kFaultPagedPayloadChannel,
                               BadIndex, S.salt ^ 0xA0761D6478BD642FULL,
                               "morok.fpp.fault.seal");
    B.CreateBr(Return);

    B.SetInsertPoint(Return);
    Value *OutPtr = globalBytePtr(B, Cache, InPage, "morok.fpp.cache.out.ptr");
    Value *Out = volatileLoadI8(B, OutPtr, "morok.fpp.byte");
    B.CreateRet(Out);
    return F;
}

Value *bytecodeIndex(Value *Ptr, GlobalVariable *Bytecode) {
    auto *GEP = dyn_cast<GEPOperator>(Ptr->stripPointerCasts());
    if (!GEP || GEP->getPointerOperand()->stripPointerCasts() != Bytecode ||
        GEP->getNumIndices() < 2)
        return nullptr;
    return GEP->getOperand(GEP->getNumOperands() - 1);
}

Value *asI32(Builder &B, Value *V) {
    auto *I32 = B.getInt32Ty();
    if (V->getType()->isIntegerTy(32))
        return V;
    if (V->getType()->isIntegerTy()) {
        auto *IT = cast<IntegerType>(V->getType());
        if (IT->getBitWidth() < 32)
            return B.CreateZExt(V, I32, "morok.fpp.idx");
        return B.CreateTrunc(V, I32, "morok.fpp.idx");
    }
    return B.CreatePtrToInt(V, I32, "morok.fpp.idx");
}

bool rewriteBytecodeLoads(Payload &P, Function *Accessor) {
    struct LoadSite {
        LoadInst *load = nullptr;
        Value *index = nullptr;
    };
    SmallVector<LoadSite, 16> Sites;
    for (Instruction &I : instructions(*P.helper)) {
        auto *LI = dyn_cast<LoadInst>(&I);
        if (!LI || !LI->getType()->isIntegerTy(8))
            continue;
        Value *Idx = bytecodeIndex(LI->getPointerOperand(), P.bytecode);
        if (!Idx)
            continue;
        Sites.push_back({LI, Idx});
    }
    for (LoadSite Site : Sites) {
        Builder B(Site.load);
        Value *Idx32 = asI32(B, Site.index);
        auto *Call = B.CreateCall(Accessor->getFunctionType(), Accessor,
                                  {Idx32}, "morok.fpp.byte");
        Call->setCallingConv(CallingConv::C);
        Site.load->replaceAllUsesWith(Call);
        Site.load->eraseFromParent();
    }
    return !Sites.empty();
}

bool hasBytecodeLoads(Payload &P) {
    for (Instruction &I : instructions(*P.helper)) {
        auto *LI = dyn_cast<LoadInst>(&I);
        if (LI && LI->getType()->isIntegerTy(8) &&
            bytecodeIndex(LI->getPointerOperand(), P.bytecode))
            return true;
    }
    return false;
}

bool protectPayload(Module &M, Payload &P,
                    const FaultPagedPayloadParams &Params,
                    std::uint32_t PageSize, ir::IRRandom &Rng) {
    if (!hasBytecodeLoads(P))
        return false;
    if (Params.bind_to_runtime_seal)
        runtime_seal::getChannel(M, runtime_seal::kFaultPagedPayloadChannel,
                                 Rng);
    const std::uint32_t Size = static_cast<std::uint32_t>(P.original.size());
    const std::uint32_t PageCount = (Size + PageSize - 1) / PageSize;
    PageSchedule S = makeSchedule(Rng);
    std::vector<std::uint8_t> Cipher =
        encrypt(P.original, PageSize, S, Params.per_page_keys);
    makeMutableCiphertext(*P.bytecode, Cipher);
    SmallVector<GlobalValue *, 4> Retained;
    Retained.push_back(createMeta(M, P.suffix, Size, PageSize, PageCount, S));
    if (GlobalVariable *Decoy =
            createDecoys(M, P.suffix, Params.decoy_pages, PageSize, Rng))
        Retained.push_back(Decoy);
    GlobalVariable *Cache = makeThreadLocal(
        createZeroArray(M, PageSize, "morok.fpp.page.cache." + P.suffix));
    GlobalVariable *Loaded = makeThreadLocal(
        createZeroArray(M, PageCount, "morok.fpp.page.loaded." + P.suffix));
    GlobalVariable *Active = makeThreadLocal(createI32State(
        M, "morok.fpp.page.active." + P.suffix, kInvalidPage));
    GlobalVariable *Faults = makeThreadLocal(
        createI64State(M, "morok.fpp.fault.count." + P.suffix, 0));
    Function *Accessor = createAccessor(M, P, Params, PageSize, PageCount, S,
                                        Cache, Loaded, Active, Faults);
    appendToUsed(M, Retained);
    appendToCompilerUsed(M, Retained);
    return rewriteBytecodeLoads(P, Accessor);
}

std::uint32_t normalizedPageSize(const FaultPagedPayloadParams &Params) {
    std::uint32_t PageSize = Params.page_size == 0 ? kMaxPageSize
                                                   : Params.page_size;
    PageSize = std::clamp(PageSize, kMinPageSize, kMaxPageSize);
    return PageSize;
}

} // namespace

bool faultPagedPayloadModule(Module &M,
                             const FaultPagedPayloadParams &Params,
                             ir::IRRandom &Rng) {
    if (!Params.enabled || Params.probability == 0 || Params.max_payloads == 0)
        return false;
    if (Params.backend != "lazy_accessor" && !Params.fallback)
        return false;

    std::vector<Payload> Payloads = collectPayloads(M, Params.max_payload_bytes);
    if (Payloads.empty())
        return false;
    shufflePayloads(Payloads, Rng);

    bool Changed = false;
    std::uint32_t Wrapped = 0;
    const std::uint32_t PageSize = normalizedPageSize(Params);
    for (Payload &P : Payloads) {
        if (Wrapped >= Params.max_payloads)
            break;
        if (!Rng.chance(Params.probability))
            continue;
        if (protectPayload(M, P, Params, PageSize, Rng)) {
            Changed = true;
            ++Wrapped;
        }
    }
    return Changed;
}

PreservedAnalyses FaultPagedPayloadPass::run(Module &M,
                                             ModuleAnalysisManager &) {
    ir::IRRandom Rng(engine_);
    if (!faultPagedPayloadModule(M, params_, Rng))
        return PreservedAnalyses::all();
    return PreservedAnalyses::none();
}

} // namespace morok::passes
