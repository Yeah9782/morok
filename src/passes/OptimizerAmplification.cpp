// SPDX-License-Identifier: MIT
//
// Morok — modular LLVM IR obfuscator.
//
// morok/passes/OptimizerAmplification.cpp
//
// This pass deliberately avoids volatile state and helper calls.  It emits
// ordinary branchless arithmetic/comparisons: several equivalent forms of the
// same operation are selected by input-derived guards.  Placing the pass before
// the vectorizers gives LLVM a larger arithmetic graph to reassociate and lower
// into normal optimized code without carrying a distinctive runtime
// obfuscation scaffold.

#include "morok/passes/OptimizerAmplification.hpp"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/NoFolder.h"

#include <algorithm>
#include <vector>

using namespace llvm;

namespace morok::passes {

namespace {

using Builder = IRBuilder<NoFolder>;

struct Target {
    Instruction *inst = nullptr;
};

bool eligible(BinaryOperator *BO) {
    auto *Ty = dyn_cast<IntegerType>(BO->getType());
    if (!Ty || Ty->getBitWidth() == 0)
        return false;
    if (BO->getName().starts_with("morok.optamp"))
        return false;
    // Poison-generating flags (nsw/nuw, `or disjoint`, …) are accepted: amplify
    // replaces the op with a select over a flag-free base and flag-free
    // equivalent forms (see amplify()), a sound refinement of the flagged op —
    // identical for every input the flag promised about.

    switch (BO->getOpcode()) {
    case Instruction::Add:
    case Instruction::Sub:
    case Instruction::Mul:
    case Instruction::And:
    case Instruction::Or:
    case Instruction::Xor:
        return true;
    default:
        return false;
    }
}

bool eligible(ICmpInst *CI) {
    auto *Ty = dyn_cast<IntegerType>(CI->getOperand(0)->getType());
    if (!Ty || Ty->getBitWidth() == 0)
        return false;
    if (CI->getOperand(1)->getType() != Ty)
        return false;
    if (CI->getName().starts_with("morok.optamp"))
        return false;
    switch (CI->getPredicate()) {
    case CmpInst::ICMP_EQ:
    case CmpInst::ICMP_NE:
    case CmpInst::ICMP_UGT:
    case CmpInst::ICMP_UGE:
    case CmpInst::ICMP_ULT:
    case CmpInst::ICMP_ULE:
    case CmpInst::ICMP_SGT:
    case CmpInst::ICMP_SGE:
    case CmpInst::ICMP_SLT:
    case CmpInst::ICMP_SLE:
        return true;
    default:
        return false;
    }
}

bool supportedFloatType(Type *Ty) {
    return Ty->isHalfTy() || Ty->isBFloatTy() || Ty->isFloatTy() ||
           Ty->isDoubleTy();
}

bool eligible(FCmpInst *FI) {
    Type *Ty = FI->getOperand(0)->getType();
    if (!supportedFloatType(Ty) || FI->getOperand(1)->getType() != Ty)
        return false;
    if (FI->getName().starts_with("morok.optamp"))
        return false;
    if (FI->getFastMathFlags().any())
        return false;
    switch (FI->getPredicate()) {
    case CmpInst::FCMP_OEQ:
    case CmpInst::FCMP_OGT:
    case CmpInst::FCMP_OGE:
    case CmpInst::FCMP_OLT:
    case CmpInst::FCMP_OLE:
    case CmpInst::FCMP_ONE:
    case CmpInst::FCMP_ORD:
    case CmpInst::FCMP_UNO:
    case CmpInst::FCMP_UEQ:
    case CmpInst::FCMP_UGT:
    case CmpInst::FCMP_UGE:
    case CmpInst::FCMP_ULT:
    case CmpInst::FCMP_ULE:
    case CmpInst::FCMP_UNE:
        return true;
    default:
        return false;
    }
}

IntegerType *integerCarrierFor(Type *Ty) {
    const unsigned Bits = static_cast<unsigned>(Ty->getPrimitiveSizeInBits());
    return IntegerType::get(Ty->getContext(), Bits);
}

Value *one(IntegerType *Ty) { return ConstantInt::get(Ty, 1); }

Value *two(Builder &B, Value *V, IntegerType *Ty) {
    return B.CreateShl(V, one(Ty), "morok.optamp.twice");
}

Value *equivalentForm(Builder &B, BinaryOperator *BO, std::uint32_t Variant) {
    Value *A = BO->getOperand(0);
    Value *C = BO->getOperand(1);
    auto *Ty = cast<IntegerType>(BO->getType());

    switch (BO->getOpcode()) {
    case Instruction::Add:
        if ((Variant & 1u) == 0 && Ty->getBitWidth() > 1)
            return B.CreateAdd(B.CreateXor(A, C, "morok.optamp.add.xor"),
                               two(B, B.CreateAnd(A, C,
                                                  "morok.optamp.add.carry"),
                                   Ty),
                               "morok.optamp.form");
        return B.CreateAdd(B.CreateOr(A, C, "morok.optamp.add.or"),
                           B.CreateAnd(A, C, "morok.optamp.add.and"),
                           "morok.optamp.form");
    case Instruction::Sub:
        if ((Variant & 1u) == 0 && Ty->getBitWidth() > 1)
            return B.CreateSub(
                B.CreateXor(A, C, "morok.optamp.sub.xor"),
                two(B, B.CreateAnd(B.CreateNot(A, "morok.optamp.sub.nota"), C,
                                   "morok.optamp.sub.borrow"),
                    Ty),
                "morok.optamp.form");
        return B.CreateAdd(
            B.CreateAdd(A, B.CreateNot(C, "morok.optamp.sub.notb"),
                        "morok.optamp.sub.ones"),
            one(Ty), "morok.optamp.form");
    case Instruction::Mul:
        if ((Variant & 1u) == 0)
            return B.CreateSub(
                B.CreateMul(A, B.CreateAdd(C, one(Ty),
                                           "morok.optamp.mul.inc"),
                            "morok.optamp.mul.wide"),
                A, "morok.optamp.form");
        return B.CreateNeg(
            B.CreateMul(A, B.CreateNeg(C, "morok.optamp.mul.negb"),
                        "morok.optamp.mul.negprod"),
            "morok.optamp.form");
    case Instruction::And:
        if ((Variant & 1u) == 0)
            return B.CreateNot(
                B.CreateOr(B.CreateNot(A, "morok.optamp.and.nota"),
                           B.CreateNot(C, "morok.optamp.and.notb"),
                           "morok.optamp.and.demorgan"),
                "morok.optamp.form");
        return B.CreateAnd(B.CreateXor(A, B.CreateNot(C,
                                                      "morok.optamp.and.notb"),
                                       "morok.optamp.and.mask"),
                           A, "morok.optamp.form");
    case Instruction::Or:
        if ((Variant & 1u) == 0)
            return B.CreateNot(
                B.CreateAnd(B.CreateNot(A, "morok.optamp.or.nota"),
                            B.CreateNot(C, "morok.optamp.or.notb"),
                            "morok.optamp.or.demorgan"),
                "morok.optamp.form");
        return B.CreateOr(B.CreateAnd(A, C, "morok.optamp.or.and"),
                          B.CreateXor(A, C, "morok.optamp.or.xor"),
                          "morok.optamp.form");
    case Instruction::Xor:
        if ((Variant & 1u) == 0)
            return B.CreateSub(B.CreateOr(A, C, "morok.optamp.xor.or"),
                               B.CreateAnd(A, C, "morok.optamp.xor.and"),
                               "morok.optamp.form");
        return B.CreateOr(
            B.CreateAnd(B.CreateNot(A, "morok.optamp.xor.nota"), C,
                        "morok.optamp.xor.rhs"),
            B.CreateAnd(A, B.CreateNot(C, "morok.optamp.xor.notb"),
                        "morok.optamp.xor.lhs"),
            "morok.optamp.form");
    default:
        return nullptr;
    }
}

Value *equivalentCompareForm(Builder &B, ICmpInst *CI,
                             std::uint32_t Variant) {
    Value *A = CI->getOperand(0);
    Value *C = CI->getOperand(1);
    auto *Ty = cast<IntegerType>(A->getType());
    CmpInst::Predicate Pred = CI->getPredicate();

    switch (Variant & 3u) {
    case 0:
        return B.CreateICmp(Pred, A, C, "morok.optamp.cmp.form");
    case 1:
        return B.CreateICmp(CmpInst::getSwappedPredicate(Pred), C, A,
                            "morok.optamp.cmp.form");
    case 2:
        return B.CreateNot(
            B.CreateICmp(CmpInst::getInversePredicate(Pred), A, C,
                         "morok.optamp.cmp.inverse"),
            "morok.optamp.cmp.form");
    default:
        if (Pred == CmpInst::ICMP_EQ || Pred == CmpInst::ICMP_NE) {
            Value *Diff = B.CreateXor(A, C, "morok.optamp.cmp.xor");
            CmpInst::Predicate ZeroPred =
                Pred == CmpInst::ICMP_EQ ? CmpInst::ICMP_EQ
                                         : CmpInst::ICMP_NE;
            return B.CreateICmp(ZeroPred, Diff, ConstantInt::get(Ty, 0),
                                "morok.optamp.cmp.form");
        }
        CmpInst::Predicate Swapped = CmpInst::getSwappedPredicate(Pred);
        return B.CreateNot(
            B.CreateICmp(CmpInst::getInversePredicate(Swapped), C, A,
                         "morok.optamp.cmp.inverse"),
            "morok.optamp.cmp.form");
    }
}

Value *equivalentCompareForm(Builder &B, FCmpInst *FI,
                             std::uint32_t Variant) {
    Value *A = FI->getOperand(0);
    Value *C = FI->getOperand(1);
    CmpInst::Predicate Pred = FI->getPredicate();

    switch (Variant & 3u) {
    case 0:
        return B.CreateFCmp(Pred, A, C, "morok.optamp.fcmp.form");
    case 1:
        return B.CreateFCmp(CmpInst::getSwappedPredicate(Pred), C, A,
                            "morok.optamp.fcmp.form");
    case 2:
        return B.CreateNot(
            B.CreateFCmp(CmpInst::getInversePredicate(Pred), A, C,
                         "morok.optamp.fcmp.inverse"),
            "morok.optamp.fcmp.form");
    default:
        CmpInst::Predicate Swapped = CmpInst::getSwappedPredicate(Pred);
        return B.CreateNot(
            B.CreateFCmp(CmpInst::getInversePredicate(Swapped), C, A,
                         "morok.optamp.fcmp.inverse"),
            "morok.optamp.fcmp.form");
    }
}

Value *inputGuard(Builder &B, Value *A, Value *C, IntegerType *Ty,
                  std::uint32_t Index, ir::IRRandom &rng) {
    const unsigned Width = Ty->getBitWidth();
    const unsigned ShiftA = static_cast<unsigned>((Index * 5u) % Width);
    const unsigned ShiftB = static_cast<unsigned>((Index * 7u + 3u) % Width);

    Value *SA = ShiftA == 0 ? A : B.CreateLShr(A, ConstantInt::get(Ty, ShiftA),
                                               "morok.optamp.guard.sa");
    Value *SB = ShiftB == 0 ? C : B.CreateLShr(C, ConstantInt::get(Ty, ShiftB),
                                               "morok.optamp.guard.sb");
    Value *Salt = ConstantInt::get(Ty, rng.next());
    Value *Mix = B.CreateXor(B.CreateXor(SA, SB, "morok.optamp.guard.mix"),
                             Salt, "morok.optamp.guard.salt");
    Value *Bit = B.CreateAnd(Mix, one(Ty), "morok.optamp.guard.bit");
    return B.CreateICmpNE(Bit, ConstantInt::get(Ty, 0), "morok.optamp.guard");
}

Value *inputGuard(Builder &B, BinaryOperator *BO, std::uint32_t Index,
                  ir::IRRandom &rng) {
    auto *Ty = cast<IntegerType>(BO->getType());
    return inputGuard(B, BO->getOperand(0), BO->getOperand(1), Ty, Index, rng);
}

Value *inputGuard(Builder &B, ICmpInst *CI, std::uint32_t Index,
                  ir::IRRandom &rng) {
    auto *Ty = cast<IntegerType>(CI->getOperand(0)->getType());
    return inputGuard(B, CI->getOperand(0), CI->getOperand(1), Ty, Index, rng);
}

Value *inputGuard(Builder &B, FCmpInst *FI, std::uint32_t Index,
                  ir::IRRandom &rng) {
    Type *FloatTy = FI->getOperand(0)->getType();
    IntegerType *CarrierTy = integerCarrierFor(FloatTy);
    Value *A = B.CreateBitCast(FI->getOperand(0), CarrierTy,
                               "morok.optamp.guard.bits");
    Value *C = B.CreateBitCast(FI->getOperand(1), CarrierTy,
                               "morok.optamp.guard.bits");
    return inputGuard(B, A, C, CarrierTy, Index, rng);
}

Value *amplify(BinaryOperator *BO, const OptAmpParams &Params,
               ir::IRRandom &rng) {
    Builder B(BO);
    Value *Result = B.CreateBinOp(BO->getOpcode(), BO->getOperand(0),
                                  BO->getOperand(1), "morok.optamp.base");
    const std::uint32_t Forms =
        std::clamp<std::uint32_t>(Params.max_forms, 1, 4);
    const std::uint32_t FirstVariant = rng.range(2);

    for (std::uint32_t I = 0; I < Forms; ++I) {
        Value *Alt = equivalentForm(B, BO, FirstVariant + I);
        if (!Alt)
            return nullptr;
        Value *Guard = inputGuard(B, BO, I + 1, rng);
        Result = B.CreateSelect(Guard, Alt, Result, "morok.optamp.select");
    }
    return Result;
}

Value *amplify(ICmpInst *CI, const OptAmpParams &Params, ir::IRRandom &rng) {
    Builder B(CI);
    Value *Result = B.CreateICmp(CI->getPredicate(), CI->getOperand(0),
                                 CI->getOperand(1), "morok.optamp.base");
    const std::uint32_t Forms =
        std::clamp<std::uint32_t>(Params.max_forms, 1, 4);
    const std::uint32_t FirstVariant = rng.range(4);

    for (std::uint32_t I = 0; I < Forms; ++I) {
        Value *Alt = equivalentCompareForm(B, CI, FirstVariant + I);
        if (!Alt)
            return nullptr;
        Value *Guard = inputGuard(B, CI, I + 1, rng);
        Result = B.CreateSelect(Guard, Alt, Result, "morok.optamp.select");
    }
    return Result;
}

Value *amplify(FCmpInst *FI, const OptAmpParams &Params, ir::IRRandom &rng) {
    Builder B(FI);
    Value *Result = B.CreateFCmp(FI->getPredicate(), FI->getOperand(0),
                                 FI->getOperand(1), "morok.optamp.base");
    const std::uint32_t Forms =
        std::clamp<std::uint32_t>(Params.max_forms, 1, 4);
    const std::uint32_t FirstVariant = rng.range(4);

    for (std::uint32_t I = 0; I < Forms; ++I) {
        Value *Alt = equivalentCompareForm(B, FI, FirstVariant + I);
        if (!Alt)
            return nullptr;
        Value *Guard = inputGuard(B, FI, I + 1, rng);
        Result = B.CreateSelect(Guard, Alt, Result, "morok.optamp.select");
    }
    return Result;
}

} // namespace

bool optimizerAmplifyFunction(Function &F, const OptAmpParams &Params,
                              ir::IRRandom &rng) {
    if (F.isDeclaration() || Params.probability == 0 || Params.max_forms == 0)
        return false;

    std::vector<Target> Targets;
    for (BasicBlock &BB : F) {
        for (Instruction &I : BB) {
            if (auto *BO = dyn_cast<BinaryOperator>(&I)) {
                if (eligible(BO))
                    Targets.push_back({BO});
                continue;
            }
            if (auto *CI = dyn_cast<ICmpInst>(&I))
                if (eligible(CI))
                    Targets.push_back({CI});
            if (auto *FI = dyn_cast<FCmpInst>(&I))
                if (eligible(FI))
                    Targets.push_back({FI});
        }
    }

    bool Changed = false;
    for (const Target &T : Targets) {
        if (!rng.chance(Params.probability))
            continue;
        Value *Replacement = nullptr;
        if (auto *BO = dyn_cast<BinaryOperator>(T.inst))
            Replacement = amplify(BO, Params, rng);
        else if (auto *CI = dyn_cast<ICmpInst>(T.inst))
            Replacement = amplify(CI, Params, rng);
        else if (auto *FI = dyn_cast<FCmpInst>(T.inst))
            Replacement = amplify(FI, Params, rng);
        if (Replacement) {
            T.inst->replaceAllUsesWith(Replacement);
            T.inst->eraseFromParent();
            Changed = true;
        }
    }
    return Changed;
}

PreservedAnalyses
OptimizerAmplificationPass::run(Function &F, FunctionAnalysisManager &) {
    if (F.isDeclaration())
        return PreservedAnalyses::all();
    ir::IRRandom rng(engine_);
    return optimizerAmplifyFunction(F, params_, rng) ? PreservedAnalyses::none()
                                                     : PreservedAnalyses::all();
}

} // namespace morok::passes
