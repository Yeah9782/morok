// SPDX-License-Identifier: MIT
//
// Morok — modular LLVM IR obfuscator.
//
// morok/passes/InterproceduralFsm.cpp
//
// Interprocedural FSM splitting.  This pass assumes a function has already been
// flattened by one of Morok's flattening-family passes.  It finds stores to the
// dispatcher state alloca (`fla.state`) and replaces the stored value with a
// call to one of two shared helper functions.  The helpers are mutually
// recursive for one bounded step, thread the current state through arguments and
// a volatile global slot, and return the proposed next state unchanged.

#include "morok/passes/InterproceduralFsm.hpp"

#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/NoFolder.h"

#include <algorithm>
#include <cstdint>
#include <vector>

using namespace llvm;

namespace morok::passes {

namespace {

struct Runtime {
    Function *stepA = nullptr;
    Function *stepB = nullptr;
    GlobalVariable *thread = nullptr;
};

struct StateStore {
    StoreInst *store = nullptr;
    AllocaInst *state = nullptr;
};

std::uint32_t freshOdd(ir::IRRandom &rng) {
    return static_cast<std::uint32_t>(rng.next()) | 1u;
}

void addNoInlineAttrs(Function *F) {
    F->addFnAttr(Attribute::NoInline);
    F->addFnAttr(Attribute::OptimizeNone);
}

void buildHelperBody(Function *Self, Function *Other,
                     std::uint32_t outgoingStateMask,
                     std::uint32_t outgoingTokenMask,
                     std::uint32_t finishStateMask,
                     std::uint32_t finishTokenMask) {
    if (!Self->empty())
        return;

    LLVMContext &Ctx = Self->getContext();
    auto *I32 = Type::getInt32Ty(Ctx);

    auto AI = Self->arg_begin();
    Value *Current = &*AI++;
    Current->setName("current");
    Value *Proposed = &*AI++;
    Proposed->setName("proposed");
    Value *Token = &*AI++;
    Token->setName("token");
    Value *Thread = &*AI++;
    Thread->setName("thread");
    Value *Phase = &*AI++;
    Phase->setName("phase");

    BasicBlock *Entry = BasicBlock::Create(Ctx, "entry", Self);
    BasicBlock *Recurse = BasicBlock::Create(Ctx, "recurse", Self);
    BasicBlock *Finish = BasicBlock::Create(Ctx, "finish", Self);

    IRBuilder<NoFolder> B(Entry);
    auto *Store = B.CreateStore(Current, Thread);
    Store->setVolatile(true);
    Store->setAlignment(Align(4));
    Value *IsOuter =
        B.CreateICmpEQ(Phase, ConstantInt::get(I32, 0), "morok.ifsm.outer");
    B.CreateCondBr(IsOuter, Recurse, Finish);

    B.SetInsertPoint(Recurse);
    Value *NextPhase =
        B.CreateAdd(Phase, ConstantInt::get(I32, 1), "morok.ifsm.phase");
    Value *MaskedCurrent =
        B.CreateXor(Current, ConstantInt::get(I32, outgoingStateMask),
                    "morok.ifsm.current.mask");
    Value *MaskedState =
        B.CreateXor(Proposed, ConstantInt::get(I32, outgoingStateMask),
                    "morok.ifsm.state.mask");
    Value *MaskedToken =
        B.CreateXor(Token, ConstantInt::get(I32, outgoingTokenMask),
                    "morok.ifsm.token.mask");
    CallInst *Call =
        B.CreateCall(Other->getFunctionType(), Other,
                     {MaskedCurrent, MaskedState, MaskedToken, Thread,
                      NextPhase},
                     "morok.ifsm.recur");
    Call->setTailCallKind(CallInst::TCK_NoTail);
    B.CreateRet(Call);

    B.SetInsertPoint(Finish);
    auto *Loaded =
        B.CreateLoad(I32, Thread, "morok.ifsm.thread.load");
    Loaded->setVolatile(true);
    Loaded->setAlignment(Align(4));
    Value *RealState =
        B.CreateXor(Proposed, ConstantInt::get(I32, finishStateMask),
                    "morok.ifsm.state.unmask");
    Value *RealToken =
        B.CreateXor(Token, ConstantInt::get(I32, finishTokenMask),
                    "morok.ifsm.token.unmask");
    Value *ThreadZero =
        B.CreateXor(Loaded, Loaded, "morok.ifsm.thread.zero");
    Value *TokenZero = B.CreateXor(RealToken, RealToken,
                                   "morok.ifsm.token.zero");
    Value *Out =
        B.CreateXor(RealState, ThreadZero, "morok.ifsm.state.threaded");
    Out = B.CreateXor(Out, TokenZero, "morok.ifsm.state.tokened");
    B.CreateRet(Out);
}

Runtime createRuntime(Module &M, ir::IRRandom &rng) {
    Runtime R;
    LLVMContext &Ctx = M.getContext();
    auto *I32 = Type::getInt32Ty(Ctx);
    auto *PtrTy = PointerType::getUnqual(Ctx);

    if (auto *GV = M.getGlobalVariable("morok.ifsm.thread", true)) {
        R.thread = GV;
    } else {
        R.thread = new GlobalVariable(
            M, I32, /*isConstant=*/false, GlobalValue::PrivateLinkage,
            ConstantInt::get(I32, 0), "morok.ifsm.thread");
        R.thread->setAlignment(Align(4));
    }

    FunctionType *FT =
        FunctionType::get(I32, {I32, I32, I32, PtrTy, I32}, false);
    R.stepA = M.getFunction("morok.ifsm.step.a");
    if (!R.stepA)
        R.stepA = Function::Create(FT, GlobalValue::InternalLinkage,
                                   "morok.ifsm.step.a", &M);
    R.stepB = M.getFunction("morok.ifsm.step.b");
    if (!R.stepB)
        R.stepB = Function::Create(FT, GlobalValue::InternalLinkage,
                                   "morok.ifsm.step.b", &M);

    addNoInlineAttrs(R.stepA);
    addNoInlineAttrs(R.stepB);

    const std::uint32_t ABState = freshOdd(rng);
    const std::uint32_t ABToken = freshOdd(rng);
    const std::uint32_t BAState = freshOdd(rng);
    const std::uint32_t BAToken = freshOdd(rng);
    buildHelperBody(R.stepA, R.stepB, ABState, ABToken, BAState, BAToken);
    buildHelperBody(R.stepB, R.stepA, BAState, BAToken, ABState, ABToken);
    return R;
}

bool isGeneratedFunction(const Function &F) {
    return F.getName().starts_with("morok.");
}

AllocaInst *flattenStateAlloca(StoreInst &SI) {
    if (!SI.getValueOperand()->getType()->isIntegerTy(32))
        return nullptr;
    auto *AI =
        dyn_cast<AllocaInst>(SI.getPointerOperand()->stripPointerCasts());
    if (!AI || !AI->getName().starts_with("fla.state"))
        return nullptr;
    return AI;
}

bool alreadyWrapped(StoreInst &SI) {
    auto *CI = dyn_cast<CallInst>(SI.getValueOperand());
    if (!CI)
        return false;
    Function *Callee = CI->getCalledFunction();
    return Callee && Callee->getName().starts_with("morok.ifsm.");
}

std::vector<StateStore> collectCandidates(Function &F) {
    std::vector<StateStore> Sites;
    if (F.isDeclaration() || isGeneratedFunction(F))
        return Sites;
    for (Instruction &I : instructions(F)) {
        auto *SI = dyn_cast<StoreInst>(&I);
        if (!SI || SI->getParent() == &F.getEntryBlock() ||
            alreadyWrapped(*SI))
            continue;
        if (AllocaInst *State = flattenStateAlloca(*SI))
            Sites.push_back({SI, State});
    }
    return Sites;
}

std::vector<StateStore> collectCandidates(Module &M) {
    std::vector<StateStore> Sites;
    for (Function &F : M) {
        std::vector<StateStore> FunctionSites = collectCandidates(F);
        Sites.insert(Sites.end(), FunctionSites.begin(), FunctionSites.end());
    }
    return Sites;
}

void shuffleSites(std::vector<StateStore> &Sites, ir::IRRandom &rng) {
    for (std::size_t I = Sites.size(); I > 1; --I) {
        const std::size_t J = rng.range(static_cast<std::uint32_t>(I));
        std::swap(Sites[I - 1], Sites[J]);
    }
}

Value *asI32(IRBuilder<NoFolder> &B, Value *V) {
    auto *I32 = B.getInt32Ty();
    if (V->getType() == I32)
        return V;
    if (auto *IT = dyn_cast<IntegerType>(V->getType())) {
        const unsigned Bits = IT->getBitWidth();
        if (Bits < 32)
            return B.CreateZExt(V, I32, "morok.ifsm.term.zext");
        if (Bits > 32)
            return B.CreateTrunc(V, I32, "morok.ifsm.term.trunc");
    }
    if (V->getType()->isHalfTy() || V->getType()->isBFloatTy() ||
        V->getType()->isFloatTy() || V->getType()->isDoubleTy()) {
        IntegerType *CarrierTy = nullptr;
        if (V->getType()->isHalfTy() || V->getType()->isBFloatTy())
            CarrierTy = IntegerType::get(V->getContext(), 16);
        else if (V->getType()->isFloatTy())
            CarrierTy = IntegerType::get(V->getContext(), 32);
        else
            CarrierTy = IntegerType::get(V->getContext(), 64);
        Value *Bits = B.CreateBitCast(V, CarrierTy, "morok.ifsm.term.fp");
        if (CarrierTy->getBitWidth() < 32)
            return B.CreateZExt(Bits, I32, "morok.ifsm.term.zext");
        if (CarrierTy->getBitWidth() > 32)
            return B.CreateTrunc(Bits, I32, "morok.ifsm.term.trunc");
        return Bits;
    }
    return nullptr;
}

void addTerm(Value *V, SmallPtrSetImpl<Value *> &Seen,
             std::vector<Value *> &Terms) {
    if (!V)
        return;
    Type *Ty = V->getType();
    if (!Ty->isIntegerTy() && !Ty->isHalfTy() && !Ty->isBFloatTy() &&
        !Ty->isFloatTy() && !Ty->isDoubleTy())
        return;
    if (Seen.insert(V).second)
        Terms.push_back(V);
}

std::vector<Value *> collectTerms(StoreInst &SI) {
    std::vector<Value *> Terms;
    SmallPtrSet<Value *, 32> Seen;
    addTerm(SI.getValueOperand(), Seen, Terms);
    for (Instruction &I : *SI.getParent()) {
        if (&I == &SI)
            break;
        if (isa<AllocaInst>(&I))
            continue;
        addTerm(&I, Seen, Terms);
    }
    return Terms;
}

void shuffleTerms(std::vector<Value *> &Terms, ir::IRRandom &rng) {
    for (std::size_t I = Terms.size(); I > 1; --I) {
        const std::size_t J = rng.range(static_cast<std::uint32_t>(I));
        std::swap(Terms[I - 1], Terms[J]);
    }
}

Value *mixedToken(IRBuilder<NoFolder> &B, StoreInst &SI, AllocaInst *State,
                  Value *Current, const InterproceduralFsmParams &Params,
                  ir::IRRandom &rng) {
    auto *I32 = B.getInt32Ty();
    Value *Token = B.CreateXor(Current, SI.getValueOperand(),
                               "morok.ifsm.token.seed");

    std::vector<Value *> Terms = collectTerms(SI);
    shuffleTerms(Terms, rng);
    const std::uint32_t Limit = std::min<std::uint32_t>(
        Params.max_terms, static_cast<std::uint32_t>(Terms.size()));
    for (std::uint32_t I = 0; I < Limit; ++I) {
        Value *Term = asI32(B, Terms[I]);
        if (!Term || Term == SI.getValueOperand() || Term == State)
            continue;
        Value *Salt =
            ConstantInt::get(I32, static_cast<std::uint32_t>(rng.next()));
        Value *Odd =
            ConstantInt::get(I32, static_cast<std::uint32_t>(rng.next()) | 1u);
        Token = B.CreateMul(
            B.CreateXor(Token, B.CreateXor(Term, Salt),
                        "morok.ifsm.token.fold"),
            Odd, "morok.ifsm.token.mix");
    }
    return Token;
}

void wrapStore(const StateStore &Site, const Runtime &R,
               const InterproceduralFsmParams &Params, ir::IRRandom &rng,
               std::uint32_t Ordinal) {
    StoreInst *SI = Site.store;
    IRBuilder<NoFolder> B(SI);
    Value *Current =
        B.CreateLoad(B.getInt32Ty(), Site.state, "morok.ifsm.current");
    Value *Token = mixedToken(B, *SI, Site.state, Current, Params, rng);
    Function *Callee = (Ordinal % 2u) == 0u ? R.stepA : R.stepB;
    CallInst *Next = B.CreateCall(
        Callee->getFunctionType(), Callee,
        {Current, SI->getValueOperand(), Token, R.thread,
         ConstantInt::get(B.getInt32Ty(), 0)},
        "morok.ifsm.next");
    Next->setTailCallKind(CallInst::TCK_NoTail);
    SI->setOperand(0, Next);
}

} // namespace

bool interproceduralFsmSplitFunction(Function &F,
                                     const InterproceduralFsmParams &params,
                                     ir::IRRandom &rng) {
    if (params.probability == 0 || params.max_sites == 0 || !F.getParent())
        return false;

    std::vector<StateStore> Candidates = collectCandidates(F);
    shuffleSites(Candidates, rng);

    std::vector<StateStore> Selected;
    Selected.reserve(
        std::min<std::size_t>(Candidates.size(), params.max_sites));
    for (const StateStore &Site : Candidates) {
        if (Selected.size() >= params.max_sites)
            break;
        if (rng.chance(params.probability))
            Selected.push_back(Site);
    }
    if (Selected.empty())
        return false;

    Runtime R = createRuntime(*F.getParent(), rng);
    for (std::uint32_t I = 0; I < Selected.size(); ++I)
        wrapStore(Selected[I], R, params, rng, I);
    return true;
}

bool interproceduralFsmSplitModule(Module &M,
                                   const InterproceduralFsmParams &params,
                                   ir::IRRandom &rng) {
    if (params.probability == 0 || params.max_sites == 0)
        return false;

    std::vector<StateStore> Candidates = collectCandidates(M);
    shuffleSites(Candidates, rng);

    std::vector<StateStore> Selected;
    Selected.reserve(
        std::min<std::size_t>(Candidates.size(), params.max_sites));
    for (const StateStore &Site : Candidates) {
        if (Selected.size() >= params.max_sites)
            break;
        if (rng.chance(params.probability))
            Selected.push_back(Site);
    }
    if (Selected.empty())
        return false;

    Runtime R = createRuntime(M, rng);
    for (std::uint32_t I = 0; I < Selected.size(); ++I)
        wrapStore(Selected[I], R, params, rng, I);
    return true;
}

PreservedAnalyses InterproceduralFsmPass::run(Module &M,
                                              ModuleAnalysisManager &) {
    ir::IRRandom rng(engine_);
    return interproceduralFsmSplitModule(M, params_, rng)
               ? PreservedAnalyses::none()
               : PreservedAnalyses::all();
}

} // namespace morok::passes
