// SPDX-License-Identifier: MIT
//
// Morok — modular LLVM IR obfuscator.
//
// morok/passes/PhiTangling.cpp
//
// SSA/PHI tangling: surround an existing integer PHI with redundant edge copies
// and PHIs that all carry the same value.  Cross-PHI XORs produce zero and are
// folded into downstream uses, preserving semantics while making expression
// propagation walk a denser cross-block web.

#include "morok/passes/PhiTangling.hpp"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/NoFolder.h"

#include <algorithm>
#include <cstdint>
#include <utility>
#include <vector>

using namespace llvm;

namespace morok::passes {

namespace {

bool isPassGenerated(const Value *V) {
    if (const auto *I = dyn_cast<Instruction>(V))
        return I->getName().starts_with("morok.phi");
    return false;
}

bool eligiblePhi(const PHINode &PN) {
    auto *Ty = dyn_cast<IntegerType>(PN.getType());
    if (!Ty)
        return false;
    if (Ty->getBitWidth() < 8 || isPassGenerated(&PN))
        return false;
    if (PN.getNumIncomingValues() < 2)
        return false;

    for (unsigned i = 0; i < PN.getNumIncomingValues(); ++i) {
        BasicBlock *Pred = PN.getIncomingBlock(i);
        if (!Pred || Pred->isEHPad() || Pred->isLandingPad() ||
            isa<InvokeInst>(Pred->getTerminator()))
            return false;
    }
    return true;
}

void shufflePhis(std::vector<PHINode *> &phis, ir::IRRandom &rng) {
    for (std::size_t i = phis.size(); i > 1; --i) {
        const std::size_t j = rng.range(static_cast<std::uint32_t>(i));
        std::swap(phis[i - 1], phis[j]);
    }
}

Value *edgeCopy(PHINode &PN, unsigned incoming, IntegerType *Ty,
                ir::IRRandom &rng) {
    BasicBlock *Pred = PN.getIncomingBlock(incoming);
    Instruction *Term = Pred->getTerminator();
    IRBuilder<NoFolder> B(Term);
    Value *V = PN.getIncomingValue(incoming);
    Value *K = rng.constInt(Ty);
    Value *mixed = B.CreateXor(V, K, "morok.phi.edge.mix");
    return B.CreateXor(mixed, K, "morok.phi.edge.copy");
}

PHINode *cloneDirectPhi(PHINode &PN, IntegerType *Ty) {
    auto *Copy =
        PHINode::Create(Ty, PN.getNumIncomingValues(), "morok.phi.direct", &PN);
    for (unsigned i = 0; i < PN.getNumIncomingValues(); ++i)
        Copy->addIncoming(PN.getIncomingValue(i), PN.getIncomingBlock(i));
    return Copy;
}

PHINode *cloneEdgePhi(PHINode &PN, IntegerType *Ty, ir::IRRandom &rng) {
    auto *Copy =
        PHINode::Create(Ty, PN.getNumIncomingValues(), "morok.phi.edge", &PN);
    // A predecessor can appear at more than one incoming index (callbr/asm-goto
    // with duplicate targets, or `br` with both arms to one block).  Every
    // entry for the same block must carry an identical value, so compute the
    // edge copy once per distinct predecessor and reuse it.
    DenseMap<BasicBlock *, Value *> PerBlock;
    for (unsigned i = 0; i < PN.getNumIncomingValues(); ++i) {
        BasicBlock *Pred = PN.getIncomingBlock(i);
        auto It = PerBlock.find(Pred);
        if (It == PerBlock.end())
            It = PerBlock.try_emplace(Pred, edgeCopy(PN, i, Ty, rng)).first;
        Copy->addIncoming(It->second, Pred);
    }
    return Copy;
}

Instruction *firstInsertionAfterPhis(BasicBlock &BB) {
    for (Instruction &I : BB)
        if (!isa<PHINode>(&I))
            return &I;
    return BB.getTerminator();
}

Value *buildTangledValue(PHINode &PN, const PhiTangleParams &params,
                         ir::IRRandom &rng,
                         std::vector<Instruction *> &generated) {
    auto *Ty = cast<IntegerType>(PN.getType());
    BasicBlock &BB = *PN.getParent();
    Instruction *InsertPt = firstInsertionAfterPhis(BB);
    IRBuilder<NoFolder> B(InsertPt);

    Value *Acc = &PN;
    const std::uint32_t layers = std::max<std::uint32_t>(params.layers, 1);
    for (std::uint32_t i = 0; i < layers; ++i) {
        PHINode *Edge = cloneEdgePhi(PN, Ty, rng);
        PHINode *Direct = cloneDirectPhi(PN, Ty);
        generated.push_back(Edge);
        generated.push_back(Direct);

        Value *Zero = B.CreateXor(Edge, Direct, "morok.phi.zero");
        Value *Next = B.CreateXor(Acc, Zero, "morok.phi.value");
        generated.push_back(cast<Instruction>(Zero));
        generated.push_back(cast<Instruction>(Next));
        Acc = Next;
    }
    return Acc;
}

void replaceUses(PHINode &PN, Value *Replacement,
                 const std::vector<Instruction *> &generated) {
    SmallPtrSet<const User *, 16> generatedUsers;
    for (Instruction *I : generated)
        generatedUsers.insert(I);

    PN.replaceUsesWithIf(Replacement, [&](Use &U) {
        if (generatedUsers.contains(U.getUser()))
            return false;
        if (auto *UserI = dyn_cast<Instruction>(U.getUser()))
            if (isa<PHINode>(UserI) && UserI->getParent() == PN.getParent())
                return false;
        return true;
    });
}

} // namespace

bool phiTangleFunction(Function &F, const PhiTangleParams &params,
                       ir::IRRandom &rng) {
    if (F.isDeclaration() || params.probability == 0 || params.max_phis == 0)
        return false;

    std::vector<PHINode *> candidates;
    for (BasicBlock &BB : F)
        for (Instruction &I : BB) {
            auto *PN = dyn_cast<PHINode>(&I);
            if (!PN)
                break;
            if (eligiblePhi(*PN))
                candidates.push_back(PN);
        }

    shufflePhis(candidates, rng);

    bool changed = false;
    std::uint32_t selected = 0;
    for (PHINode *PN : candidates) {
        if (selected >= params.max_phis)
            break;
        if (!rng.chance(params.probability))
            continue;

        std::vector<Instruction *> generated;
        Value *Replacement = buildTangledValue(*PN, params, rng, generated);
        replaceUses(*PN, Replacement, generated);
        changed = true;
        ++selected;
    }

    return changed;
}

PreservedAnalyses PhiTanglingPass::run(Function &F, FunctionAnalysisManager &) {
    if (F.isDeclaration())
        return PreservedAnalyses::all();
    ir::IRRandom rng(engine_);
    return phiTangleFunction(F, params_, rng) ? PreservedAnalyses::none()
                                              : PreservedAnalyses::all();
}

} // namespace morok::passes
