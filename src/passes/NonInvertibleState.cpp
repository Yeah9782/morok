// SPDX-License-Identifier: MIT
//
// Morok — modular LLVM IR obfuscator.
//
// morok/passes/NonInvertibleState.cpp
//
// Non-invertible next-state flattening.  The dispatcher switch is keyed by a
// lossy per-build state encoding.  Each block selects a logical successor id,
// mixes the previous encoded state and live scalar integer/floating-point
// values into a token, routes the token through volatile shadow slots so the
// runtime value cancels, then hashes the resulting logical target into the
// encoded state domain.

#include "morok/passes/NonInvertibleState.hpp"

#include "morok/ir/ControlFlowFlattener.hpp"

#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/NoFolder.h"

#include <algorithm>
#include <cstdint>
#include <vector>

using namespace llvm;

namespace morok::passes {

namespace {

constexpr std::uint32_t kLossMask = 0x7fffffffu;

std::uint32_t rotl32(std::uint32_t X, unsigned R) {
    R &= 31u;
    return R == 0 ? X : static_cast<std::uint32_t>((X << R) | (X >> (32 - R)));
}

std::uint32_t roundSalt(std::uint32_t Key, std::uint32_t Round) {
    return Key + 0x9e3779b9u * (Round + 1u) + 0x7f4a7c15u;
}

std::uint64_t roundMul(std::uint32_t Key, std::uint32_t Round) {
    const std::uint32_t Hi =
        rotl32(Key ^ 0x85ebca6bu, 3u + (Round * 7u)) | 1u;
    const std::uint32_t Lo =
        (0xc2b2ae35u + 0x27d4eb2fu * (Round + 1u)) | 1u;
    return (static_cast<std::uint64_t>(Hi) << 32u) |
           static_cast<std::uint64_t>(Lo);
}

std::uint32_t encodeStateId(std::uint32_t Raw, std::uint32_t Key,
                            std::uint32_t Rounds) {
    std::uint32_t X = Raw ^ Key;
    const std::uint32_t Count = std::max<std::uint32_t>(Rounds, 1u);
    for (std::uint32_t R = 0; R < Count; ++R) {
        X ^= roundSalt(Key, R);
        const std::uint64_t Wide =
            static_cast<std::uint64_t>(X) * roundMul(Key, R);
        X = static_cast<std::uint32_t>(Wide) ^
            static_cast<std::uint32_t>(Wide >> 32u);
        X ^= X >> (5u + (R % 11u));
        X += roundSalt(Key ^ 0xa5a5a5a5u, R);
        X &= kLossMask;
    }
    X ^= Key & kLossMask;
    X &= kLossMask;
    if (X == Raw)
        X = (X ^ 0x5bd1e995u) & kLossMask;
    return X;
}

AllocaInst *findShadow(Function &F) {
    for (Instruction &I : F.getEntryBlock())
        if (auto *AI = dyn_cast<AllocaInst>(&I))
            if (AI->getName().starts_with("nistate.shadow"))
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
    auto *Shadow = B.CreateAlloca(ShadowTy, nullptr, "nistate.shadow");
    Shadow->setAlignment(Align(4));
    return Shadow;
}

Value *shadowSlot(IRBuilder<NoFolder> &B, AllocaInst *Shadow, unsigned Index,
                  const Twine &Name) {
    auto *I32 = B.getInt32Ty();
    return B.CreateInBoundsGEP(
        Shadow->getAllocatedType(), Shadow,
        {ConstantInt::get(I32, 0), ConstantInt::get(I32, Index)}, Name);
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

Value *asI32(IRBuilder<NoFolder> &B, Value *V) {
    auto *I32 = B.getInt32Ty();
    if (V->getType() == I32)
        return V;
    if (auto *IT = dyn_cast<IntegerType>(V->getType())) {
        const unsigned Bits = IT->getBitWidth();
        if (Bits < 32)
            return B.CreateZExt(V, I32, "nistate.term.zext");
        if (Bits > 32)
            return B.CreateTrunc(V, I32, "nistate.term.trunc");
    }
    if (supportedFloatType(V->getType())) {
        Value *Bits = B.CreateBitCast(V, integerCarrierFor(V->getType()),
                                      "nistate.term.fp");
        auto *CarrierTy = cast<IntegerType>(Bits->getType());
        if (CarrierTy->getBitWidth() < 32)
            return B.CreateZExt(Bits, I32, "nistate.term.zext");
        if (CarrierTy->getBitWidth() > 32)
            return B.CreateTrunc(Bits, I32, "nistate.term.trunc");
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

std::vector<Value *> collectLiveTerms(IRBuilder<NoFolder> &B,
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

Value *selectedTarget(IRBuilder<NoFolder> &B, const ir::SuccessorIds &Succ) {
    auto *I32 = B.getInt32Ty();
    Value *Target = ConstantInt::get(I32, Succ.defaultId);
    for (auto It = Succ.arms.rbegin(); It != Succ.arms.rend(); ++It) {
        Target = B.CreateSelect(It->condition,
                                ConstantInt::get(I32, It->targetId), Target,
                                "nistate.target.raw");
    }
    return Target;
}

Value *mixedToken(IRBuilder<NoFolder> &B, AllocaInst *StateVar,
                  std::uint32_t CurrentId, const ir::SuccessorIds &Succ,
                  const NonInvertibleStateParams &Params, ir::IRRandom &rng,
                  std::uint32_t Key) {
    auto *I32 = B.getInt32Ty();
    Value *Cur = B.CreateLoad(I32, StateVar, "nistate.cur");
    Value *Token = B.CreateXor(
        Cur, ConstantInt::get(I32, CurrentId ^ Key), "nistate.token.seed");

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
        Value *Fold =
            B.CreateXor(Token, B.CreateXor(Term, Salt), "nistate.token.fold");
        Token = B.CreateMul(Fold, Odd, "nistate.token.mix");
    }

    return Token;
}

Value *shadowedCancel(IRBuilder<NoFolder> &B, AllocaInst *Shadow,
                      Value *Token) {
    auto *I32 = B.getInt32Ty();
    Value *Slot0 = shadowSlot(B, Shadow, 0, "nistate.shadow.slot0");
    Value *Slot1 = shadowSlot(B, Shadow, 1, "nistate.shadow.slot1");

    auto *Store0 = B.CreateStore(Token, Slot0);
    Store0->setVolatile(true);
    Store0->setAlignment(Align(4));
    auto *Store1 = B.CreateStore(Token, Slot1);
    Store1->setVolatile(true);
    Store1->setAlignment(Align(4));

    auto *A = B.CreateLoad(I32, Slot0, "nistate.shadow.a");
    A->setVolatile(true);
    A->setAlignment(Align(4));
    auto *Bv = B.CreateLoad(I32, Slot1, "nistate.shadow.b");
    Bv->setVolatile(true);
    Bv->setAlignment(Align(4));
    return B.CreateXor(A, Bv, "nistate.cancel");
}

Value *hashValue(IRBuilder<NoFolder> &B, Value *Input, std::uint32_t Key,
                 std::uint32_t Rounds) {
    auto *I32 = B.getInt32Ty();
    auto *I64 = B.getInt64Ty();
    Value *X = B.CreateXor(Input, ConstantInt::get(I32, Key),
                           "nistate.hash.seed");
    const std::uint32_t Count = std::max<std::uint32_t>(Rounds, 1u);

    for (std::uint32_t R = 0; R < Count; ++R) {
        X = B.CreateXor(X, ConstantInt::get(I32, roundSalt(Key, R)),
                        "nistate.hash.salt");
        Value *Wide = B.CreateMul(
            B.CreateZExt(X, I64, "nistate.hash.ext"),
            ConstantInt::get(I64, roundMul(Key, R)), "nistate.hash.wide");
        Value *Lo = B.CreateTrunc(Wide, I32, "nistate.hash.lo");
        Value *Hi = B.CreateTrunc(
            B.CreateLShr(Wide, ConstantInt::get(I64, 32),
                         "nistate.hash.high.shift"),
            I32, "nistate.hash.hi");
        X = B.CreateXor(Lo, Hi, "nistate.hash.fold");
        X = B.CreateXor(
            X, B.CreateLShr(X, ConstantInt::get(I32, 5u + (R % 11u)),
                            "nistate.hash.diffuse.shift"),
            "nistate.hash.diffuse");
        X = B.CreateAdd(
            X, ConstantInt::get(I32, roundSalt(Key ^ 0xa5a5a5a5u, R)),
            "nistate.hash.add");
        X = B.CreateAnd(X, ConstantInt::get(I32, kLossMask),
                        "nistate.hash.loss");
    }

    X = B.CreateXor(X, ConstantInt::get(I32, Key & kLossMask),
                    "nistate.hash.final");
    X = B.CreateAnd(X, ConstantInt::get(I32, kLossMask),
                    "nistate.hash.final.loss");
    Value *Fixed = B.CreateAnd(
        B.CreateXor(X, ConstantInt::get(I32, 0x5bd1e995u),
                    "nistate.hash.eq.fix"),
        ConstantInt::get(I32, kLossMask), "nistate.hash.eq.loss");
    X = B.CreateSelect(B.CreateICmpEQ(X, Input, "nistate.hash.eq"), Fixed, X,
                       "nistate.hash.disjoint");
    return B.CreateAdd(X, ConstantInt::get(I32, 0), "nistate.next");
}

} // namespace

bool nonInvertibleStateFunction(Function &F,
                                const NonInvertibleStateParams &params,
                                ir::IRRandom &rng) {
    std::uint32_t Key = 0;
    do {
        Key = static_cast<std::uint32_t>(rng.next()) | 1u;
    } while (Key == 0);
    const std::uint32_t Rounds = std::max<std::uint32_t>(params.rounds, 1u);

    AllocaInst *Shadow = nullptr;
    return ir::flattenControlFlow(
        F, rng,
        [&](IRBuilder<> &PlainB, AllocaInst *StateVar, std::uint32_t CurrentId,
            const ir::SuccessorIds &Succ) -> Value * {
            if (!Shadow)
                Shadow = ensureShadow(F);

            IRBuilder<NoFolder> B(PlainB.GetInsertBlock(),
                                  PlainB.GetInsertPoint());
            Value *RawTarget = selectedTarget(B, Succ);
            Value *Token =
                mixedToken(B, StateVar, CurrentId, Succ, params, rng, Key);
            Value *Input = B.CreateXor(RawTarget, shadowedCancel(B, Shadow, Token),
                                       "nistate.hash.input");
            return hashValue(B, Input, Key, Rounds);
        },
        [Key, Rounds](std::uint32_t LogicalId) -> std::uint32_t {
            return encodeStateId(LogicalId, Key, Rounds);
        });
}

PreservedAnalyses NonInvertibleStatePass::run(Function &F,
                                              FunctionAnalysisManager &) {
    if (F.isDeclaration())
        return PreservedAnalyses::all();
    ir::IRRandom rng(engine_);
    return nonInvertibleStateFunction(F, params_, rng)
               ? PreservedAnalyses::none()
               : PreservedAnalyses::all();
}

} // namespace morok::passes
