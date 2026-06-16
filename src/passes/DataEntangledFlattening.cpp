// SPDX-License-Identifier: MIT
//
// Morok — modular LLVM IR obfuscator.
//
// morok/passes/DataEntangledFlattening.cpp
//
// Data-entangled control-flow flattening.  The dispatcher still receives the
// true successor id, but each state update is computed as:
//   selected_successor ^ token ^ token
// where token is mixed from the previous dispatcher state and live scalar
// integer/floating-point program values.  The duplicate token is routed through
// volatile shadow memory
// so the expression is value-neutral at run time without becoming a trivially
// foldable SSA identity.

#include "morok/passes/DataEntangledFlattening.hpp"

#include "morok/ir/ControlFlowFlattener.hpp"

#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"

#include <algorithm>
#include <cstdint>
#include <vector>

using namespace llvm;

namespace morok::passes {

namespace {

AllocaInst *findShadow(Function &F) {
    for (Instruction &I : F.getEntryBlock())
        if (auto *AI = dyn_cast<AllocaInst>(&I))
            if (AI->getName().starts_with("entfla.shadow"))
                return AI;
    return nullptr;
}

AllocaInst *ensureShadow(Function &F) {
    if (AllocaInst *Existing = findShadow(F))
        return Existing;

    LLVMContext &Ctx = F.getContext();
    IRBuilder<> B(&*F.getEntryBlock().getFirstInsertionPt());
    auto *I32 = Type::getInt32Ty(Ctx);
    auto *ShadowTy = ArrayType::get(I32, 2);
    auto *Shadow = B.CreateAlloca(ShadowTy, nullptr, "entfla.shadow");
    Shadow->setAlignment(Align(4));
    return Shadow;
}

Value *shadowSlot(IRBuilder<> &B, AllocaInst *Shadow, unsigned Index,
                  const Twine &Name) {
    auto *I32 = B.getInt32Ty();
    Value *Zero = ConstantInt::get(I32, 0);
    Value *Slot = ConstantInt::get(I32, Index);
    return B.CreateInBoundsGEP(Shadow->getAllocatedType(), Shadow, {Zero, Slot},
                               Name);
}

bool supportedFloatType(Type *Ty) {
    return Ty->isHalfTy() || Ty->isBFloatTy() || Ty->isFloatTy() ||
           Ty->isDoubleTy();
}

IntegerType *integerCarrierFor(Type *Ty) {
    if (Ty->isHalfTy() || Ty->isBFloatTy())
        return IntegerType::get(Ty->getContext(), 16);
    if (Ty->isFloatTy())
        return IntegerType::get(Ty->getContext(), 32);
    if (Ty->isDoubleTy())
        return IntegerType::get(Ty->getContext(), 64);
    return nullptr;
}

Value *asI32(IRBuilder<> &B, Value *V) {
    auto *I32 = B.getInt32Ty();
    if (V->getType() == I32)
        return V;
    if (auto *IT = dyn_cast<IntegerType>(V->getType())) {
        const unsigned Bits = IT->getBitWidth();
        if (Bits < 32)
            return B.CreateZExt(V, I32, "entfla.term.zext");
        if (Bits > 32)
            return B.CreateTrunc(V, I32, "entfla.term.trunc");
    }
    if (supportedFloatType(V->getType())) {
        Value *Bits = B.CreateBitCast(V, integerCarrierFor(V->getType()),
                                      "entfla.term.fp");
        auto *CarrierTy = cast<IntegerType>(Bits->getType());
        if (CarrierTy->getBitWidth() < 32)
            return B.CreateZExt(Bits, I32, "entfla.term.zext");
        if (CarrierTy->getBitWidth() > 32)
            return B.CreateTrunc(Bits, I32, "entfla.term.trunc");
        return Bits;
    }
    return nullptr;
}

void addTerm(Value *V, SmallPtrSetImpl<Value *> &Seen,
             std::vector<Value *> &Terms) {
    if (!V ||
        (!V->getType()->isIntegerTy() && !supportedFloatType(V->getType())))
        return;
    if (Seen.insert(V).second)
        Terms.push_back(V);
}

std::vector<Value *> collectLiveTerms(IRBuilder<> &B,
                                      const ir::SuccessorIds &Succ) {
    std::vector<Value *> Terms;
    SmallPtrSet<Value *, 32> Seen;

    for (const ir::SuccessorArm &Arm : Succ.arms)
        addTerm(Arm.condition, Seen, Terms);

    BasicBlock *BB = B.GetInsertBlock();
    const Instruction *InsertPt = &*B.GetInsertPoint();
    for (Instruction &I : *BB) {
        if (&I == InsertPt)
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

Value *selectedTarget(IRBuilder<> &B, const ir::SuccessorIds &Succ) {
    auto *I32 = B.getInt32Ty();
    Value *Target = ConstantInt::get(I32, Succ.defaultId);
    for (auto It = Succ.arms.rbegin(); It != Succ.arms.rend(); ++It) {
        Target =
            B.CreateSelect(It->condition, ConstantInt::get(I32, It->targetId),
                           Target, "entfla.target");
    }
    return Target;
}

Value *mixedToken(IRBuilder<> &B, AllocaInst *StateVar, std::uint32_t CurrentId,
                  const ir::SuccessorIds &Succ,
                  const DataEntangledFlattenParams &Params, ir::IRRandom &rng) {
    auto *I32 = B.getInt32Ty();
    Value *Cur = B.CreateLoad(I32, StateVar, "entfla.cur");
    Value *Token =
        B.CreateXor(Cur, ConstantInt::get(I32, CurrentId), "entfla.token.seed");

    std::vector<Value *> Terms = collectLiveTerms(B, Succ);
    shuffleTerms(Terms, rng);

    const std::uint32_t Limit =
        Params.max_terms == 0
            ? 0
            : std::min<std::uint32_t>(Params.max_terms,
                                      static_cast<std::uint32_t>(Terms.size()));
    for (std::uint32_t I = 0; I < Limit; ++I) {
        Value *Term = asI32(B, Terms[I]);
        if (!Term)
            continue;
        Value *Salt =
            ConstantInt::get(I32, static_cast<std::uint32_t>(rng.next()));
        Value *Odd =
            ConstantInt::get(I32, static_cast<std::uint32_t>(rng.next()) | 1u);
        Value *Mixed = B.CreateXor(Term, Salt, "entfla.token.term");
        Value *Fold = B.CreateXor(Token, Mixed, "entfla.token.fold");
        Token = B.CreateMul(Fold, Odd, "entfla.token.mix");
    }

    return Token;
}

Value *shadowedCancel(IRBuilder<> &B, AllocaInst *Shadow, Value *Token) {
    auto *I32 = B.getInt32Ty();
    Value *Slot0 = shadowSlot(B, Shadow, 0, "entfla.shadow.slot0");
    Value *Slot1 = shadowSlot(B, Shadow, 1, "entfla.shadow.slot1");

    auto *Store0 = B.CreateStore(Token, Slot0);
    Store0->setVolatile(true);
    Store0->setAlignment(Align(4));
    auto *Store1 = B.CreateStore(Token, Slot1);
    Store1->setVolatile(true);
    Store1->setAlignment(Align(4));

    auto *A = B.CreateLoad(I32, Slot0, "entfla.shadow.a");
    A->setVolatile(true);
    A->setAlignment(Align(4));
    auto *Bv = B.CreateLoad(I32, Slot1, "entfla.shadow.b");
    Bv->setVolatile(true);
    Bv->setAlignment(Align(4));
    return B.CreateXor(A, Bv, "entfla.cancel");
}

} // namespace

bool dataEntangledFlattenFunction(Function &F,
                                  const DataEntangledFlattenParams &params,
                                  ir::IRRandom &rng) {
    AllocaInst *Shadow = nullptr;
    return ir::flattenControlFlow(
        F, rng,
        [&](IRBuilder<> &B, AllocaInst *StateVar, std::uint32_t CurrentId,
            const ir::SuccessorIds &Succ) -> Value * {
            if (!Shadow)
                Shadow = ensureShadow(F);
            Value *Target = selectedTarget(B, Succ);
            Value *Token =
                mixedToken(B, StateVar, CurrentId, Succ, params, rng);
            Value *Cancel = shadowedCancel(B, Shadow, Token);
            return B.CreateXor(Target, Cancel, "entfla.next");
        });
}

PreservedAnalyses DataEntangledFlatteningPass::run(Function &F,
                                                   FunctionAnalysisManager &) {
    if (F.isDeclaration())
        return PreservedAnalyses::all();
    ir::IRRandom rng(engine_);
    return dataEntangledFlattenFunction(F, params_, rng)
               ? PreservedAnalyses::none()
               : PreservedAnalyses::all();
}

} // namespace morok::passes
