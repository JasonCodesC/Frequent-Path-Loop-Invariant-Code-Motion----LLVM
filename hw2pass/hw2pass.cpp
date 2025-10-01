
//===-- Frequent Path Loop Invariant Code Motion Pass --------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===---------------------------------------------------------------------===//
//
// CSE583 F25 - This pass can be used as a template for your FPLICM homework
//               assignment.
//               The passes get registered as "fplicm-correctness" and
//               "fplicm-performance".
//
//
////===-------------------------------------------------------------------===//
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/IR/IRBuilder.h"
#include <vector>
#include <iterator>
#include <algorithm>
#include <unordered_set>
#include <unordered_map>


/* *******Implementation Starts Here******* */
// You can include more Header files here
/* *******Implementation Ends Here******* */

using namespace llvm;
using namespace std;

namespace {

  std::vector<BasicBlock*> compute_frequent_path(Loop *L, BranchProbabilityInfo &bpi) {
    std::vector<BasicBlock*> path;
    BasicBlock *Header = L->getHeader();
    if (!Header) {
      return path;
    }
    BasicBlock *Curr = Header;
    path.push_back(Curr);

    for (int i = 0; i < 1000; ++i) {
      auto begin = succ_begin(Curr);
      auto end = succ_end(Curr);
      size_t num_succ = std::distance(begin, end);
      bool back_to_header = (Curr != Header) && std::any_of(begin, end, [&](BasicBlock *S){ return S == Header; });
      if (back_to_header) {
        break;
      }
      BasicBlock *Next = nullptr;
      if (num_succ == 1) {
        BasicBlock *S = *begin;
        if (!L->contains(S)) {
          break;
        }
        Next = S;
      } 
      else if (num_succ == 2) {
        BasicBlock *S0 = *begin;
        BasicBlock *S1 = *std::next(begin);
        auto prob = [&](BasicBlock *S) -> double {
          BranchProbability P = bpi.getEdgeProbability(Curr, S);
          return double(P.getNumerator()) / double(P.getDenominator());
        };
        bool in0 = L->contains(S0);
        bool in1 = L->contains(S1);
        double p0 = prob(S0); 
        double p1 = prob(S1);
        if (in0 && p0 >= 0.8) {
          Next = S0;
        } 
        else if (in1 && p1 >= 0.8) {
          Next = S1;
        }
        else {
          if (in0 && !in1) {
            Next = S0;
          }
          else if (!in0 && in1) {
            Next = S1;
          }
          else if (in0 && in1)  {
            Next = (p0 >= p1) ? S0 : S1;
          }
          else {
            break; 
          }
        }
      } 
      else {
        break;
      }
      if (!Next) {
        break;
      }
      path.push_back(Next);
      Curr = Next;
    }
    return path;
  }

  bool backedge_to_header(Loop *L, const vector<BasicBlock*> &Path) {
    if (Path.size() < 2) {
      return false;
    }
    BasicBlock *Header = L->getHeader();
    BasicBlock *Tail   = Path.back();
    for (BasicBlock *Succ : successors(Tail)) {
      if (Succ == Header) return true;
    }
    return false;
  }

  bool store_in_blocks(const vector<BasicBlock*> &BBs, Value *Ptr) {
    for (BasicBlock *B : BBs) {
      for (Instruction &I : *B) {
        if (auto *SI = dyn_cast<StoreInst>(&I)) {
          if (SI->getPointerOperand() == Ptr) {
            return true;
          }
        }
      }
    }
    return false;
  }

  bool has_loop_use(Loop *L, Instruction *Def) {
    for (User *U : Def->users()) {
      if (auto *I = dyn_cast<Instruction>(U)) {
        if (L->contains(I->getParent())) {
          return true;
        }
      }
    }
    return false;
  }

  void loop_uses(Loop *L, Value *From, Value *With, Instruction *SkipUser) {
    std::vector<Use*> Uses;
    for (auto &U : From->uses()) {
      Uses.push_back(&U);
    }
    for (Use *U : Uses) {
      if (auto *I = dyn_cast<Instruction>(U->getUser())) {
        if (SkipUser && I == SkipUser) {
          continue;
        }
        if (isa<PHINode>(I)) {
          continue;
        }
        if (L->contains(I->getParent())) {   
          U->set(With);
        }
      }
    }
  }


  struct HW2CorrectnessPass : public PassInfoMixin<HW2CorrectnessPass> {

    PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM) {
      llvm::BlockFrequencyAnalysis::Result &bfi = FAM.getResult<BlockFrequencyAnalysis>(F);
      llvm::BranchProbabilityAnalysis::Result &bpi = FAM.getResult<BranchProbabilityAnalysis>(F);
      llvm::LoopAnalysis::Result &li = FAM.getResult<LoopAnalysis>(F);
      /* *******Implementation Starts Here******* */
    bool changed = false;

    for (Loop *L : li) {
      BasicBlock *Header = L->getHeader();
      BasicBlock *Preheader = L->getLoopPreheader();
      if (!Header || !Preheader) {
        continue;
      }
      vector<BasicBlock*> Freq = compute_frequent_path(L, bpi);
      if (Freq.size() <= 1) {
        continue;
      }
      if (!backedge_to_header(L, Freq)) {
        continue;
      }
      unordered_set<BasicBlock*> FreqSet(Freq.begin(), Freq.end());
      vector<BasicBlock*> Infrequent;
      for (BasicBlock *BB : L->blocks()) {
        if (!FreqSet.count(BB)) {
          Infrequent.push_back(BB);
        }
      }
      if (Infrequent.empty()) {
        continue;
      }
      vector<LoadInst*> Cands;
      for (BasicBlock *BB : Freq) {
        for (Instruction &I : *BB) {
          auto *LD = dyn_cast<LoadInst>(&I);
          if (!LD) {
            continue;
          }
          Value *Ptr = LD->getPointerOperand();
          if (auto *PI = dyn_cast<Instruction>(Ptr)) {
            if (L->contains(PI->getParent())) {
              continue;
            }
          }
          if (!has_loop_use(L, LD)) {
            continue;
          }
          if (!store_in_blocks(Infrequent, Ptr)) {
            continue;
          }
          if (store_in_blocks(Freq, Ptr)) {
            continue;
          }
          Cands.push_back(LD);
        }
      }
      if (Cands.empty()) {
        continue;
      }
      unordered_map<Value*, LoadInst*> FirstLoadForPtr;
      for (LoadInst *LD : Cands) {
        Value *P = LD->getPointerOperand();
        if (!FirstLoadForPtr.count(P)) {
          FirstLoadForPtr[P] = LD;
        }
      }
      vector<BasicBlock*> HeaderPreds;
      for (BasicBlock *Pred : predecessors(Header)) {
        HeaderPreds.push_back(Pred);
      }

      for (auto &KV : FirstLoadForPtr) {
        Value *Ptr = KV.first;
        LoadInst *RepLD = KV.second;
        if (auto *PI = dyn_cast<Instruction>(Ptr)) {
          if (L->contains(PI->getParent())) {
            continue;
          }
        }
        if (!has_loop_use(L, RepLD) || !store_in_blocks(Infrequent, Ptr) || store_in_blocks(Freq, Ptr)) {
          continue;
        }
        vector<LoadInst*> ToReplace;
        for (BasicBlock *BB : L->blocks()) {
          for (Instruction &I : *BB) {
            if (auto *LD2 = dyn_cast<LoadInst>(&I)) {
              if (LD2 != RepLD && LD2->getPointerOperand() == Ptr) {
                ToReplace.push_back(LD2);
              }
            }
          }
        }

        Instruction *PreT = Preheader->getTerminator();
        RepLD->moveBefore(PreT);
        auto IP = Header->getFirstInsertionPt();
        IRBuilder<> HB(&*IP);
        PHINode *Phi = HB.CreatePHI(RepLD->getType(), (unsigned)HeaderPreds.size());
        Phi->addIncoming(RepLD, Preheader);
        for (BasicBlock *Pred : HeaderPreds) {
          if (Pred == Preheader) {
            continue;
          }
          IRBuilder<> PB(Pred->getTerminator());
          auto *Fix = PB.CreateLoad(RepLD->getType(), Ptr);
          Phi->addIncoming(Fix, Pred);
        }
        loop_uses(L, RepLD, Phi, Phi);
        for (LoadInst *LD2 : ToReplace) {
          loop_uses(L, LD2, Phi, nullptr);
          LD2->eraseFromParent();
        }
        changed = true;
      }
    }
      /* *******Implementation Ends Here******* */
      // Your pass is modifying the source code. Figure out which analyses
      // are preserved and only return those, not all.
      if (!changed) {
        return PreservedAnalyses::all();
      }
      else {
        return PreservedAnalyses::none();
      }
    }
  };

  struct HW2PerformancePass : public PassInfoMixin<HW2PerformancePass> {
    PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM) {
      llvm::BlockFrequencyAnalysis::Result &bfi = FAM.getResult<BlockFrequencyAnalysis>(F);
      llvm::BranchProbabilityAnalysis::Result &bpi = FAM.getResult<BranchProbabilityAnalysis>(F);
      llvm::LoopAnalysis::Result &li = FAM.getResult<LoopAnalysis>(F);
      /* *******Implementation Starts Here******* */
      // This is a bonus. You do not need to attempt this to receive full credit.
      /* *******Implementation Ends Here******* */

      // Your pass is modifying the source code. Figure out which analyses
      // are preserved and only return those, not all.
      return PreservedAnalyses::all();
    }
  };
}

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK llvmGetPassPluginInfo() {
  return {
    LLVM_PLUGIN_API_VERSION, "HW2Pass", "v0.1",
    [](PassBuilder &PB) {
      PB.registerPipelineParsingCallback(
        [](StringRef Name, FunctionPassManager &FPM,
        ArrayRef<PassBuilder::PipelineElement>) {
          if(Name == "fplicm-correctness"){
            FPM.addPass(HW2CorrectnessPass());
            return true;
          }
          if(Name == "fplicm-performance"){
            FPM.addPass(HW2PerformancePass());
            return true;
          }
          return false;
        }
      );
    }
  };
} 