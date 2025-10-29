
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

  struct freq_path {
    vector<BasicBlock*> blocks;
    unordered_set<BasicBlock*> set;
  };

  struct slot_info {
    AllocaInst *slot = nullptr;
    bool new_created = false;
  };

  Value *strip_ptr(Value *v) {
    return v ? v->stripPointerCasts() : v;
  }

  bool backedge_to_header(BasicBlock *bb, BasicBlock *header) {
    for (BasicBlock *succ : successors(bb)) {
      if (succ == header) {
        return true;
      }
    }
    return false;
  }

  freq_path compute_frequent_path(Loop *l, BranchProbabilityInfo &bpi) {
    freq_path fp;
    BasicBlock *header = l->getHeader();
    if (!header) {
      return fp;
    }

    BasicBlock *curr = header;
    const BranchProbability thresh(4, 5);
    int max_hops = max(8, 4 * static_cast<int>(l->getNumBlocks()));

    for (int i = 0; i < max_hops; ++i) {
      fp.blocks.push_back(curr);
      fp.set.insert(curr);
      if (backedge_to_header(curr, header)) {
        break;
      }

      Instruction *ti = curr->getTerminator();
      BasicBlock *next_bb = nullptr;
      if (auto *bi = dyn_cast<BranchInst>(ti)) {
        if (bi->isUnconditional()) {
          BasicBlock *s = bi->getSuccessor(0);
          if (l->contains(s)) {
            next_bb = s;
          }
        } 
        else if (bi->isConditional()) {
          BasicBlock *s0 = bi->getSuccessor(0);
          BasicBlock *s1 = bi->getSuccessor(1);
          if (l->contains(s0) && bpi.getEdgeProbability(curr, s0) >= thresh) {
            next_bb = s0;
          } 
          else if (l->contains(s1) && bpi.getEdgeProbability(curr, s1) >= thresh) {
            next_bb = s1;
          }
        }
      } 
      else if (auto *si = dyn_cast<SwitchInst>(ti)) {
        for (unsigned s = 0, e = si->getNumSuccessors(); s != e; ++s) {
          BasicBlock *sb = si->getSuccessor(s);
          if (!l->contains(sb)) {
            continue;
          }
          if (bpi.getEdgeProbability(curr, sb) >= thresh) {
            next_bb = sb;
            break;
          }
        }
      }
      if (!next_bb || !l->contains(next_bb)) {
        break;
      }
      curr = next_bb;
    }
    return fp;
  }

  vector<BasicBlock*> collect_infrequent_blocks(Loop *l, const unordered_set<BasicBlock*> &freq) {
    vector<BasicBlock*> res;
    for (BasicBlock *bb : l->blocks()) {
      if (!freq.count(bb)) {
        res.push_back(bb);
      }
    }
    return res;
  }


  void collect_stores_by_ptr(const vector<BasicBlock*> &blocks, 
       unordered_map<Value*, vector<StoreInst*>> &out, unordered_set<Value*> &ptrs_with_stores) {
    for (BasicBlock *bb : blocks) {
      for (Instruction &inst : *bb) {
        if (auto *si = dyn_cast<StoreInst>(&inst)) {
          Value *p = strip_ptr(si->getPointerOperand());
          out[p].push_back(si);
          ptrs_with_stores.insert(p);
        }
      }
    }
  }

  void replace_load_with_slot(LoadInst *li, AllocaInst *slot) {
    IRBuilder<> b(li);
    LoadInst *from_slot = b.CreateLoad(li->getType(), slot, "fplicm.use");
    from_slot->setAlignment(li->getAlign());
    from_slot->setVolatile(li->isVolatile());
    li->replaceAllUsesWith(from_slot);
    li->eraseFromParent();
  }

  void insert_repair_after_store(StoreInst *s, Value *orig_ptr, Type *load_ty, Align load_align, bool is_volatile, AllocaInst *slot) {
    Instruction *insert_pt = s->getNextNode();
    if (!insert_pt) {
      return;
    }
    IRBuilder<> b(insert_pt);
    LoadInst *recompute = b.CreateLoad(load_ty, orig_ptr, "fplicm.recompute");
    recompute->setAlignment(load_align);
    recompute->setVolatile(is_volatile);
    b.CreateStore(recompute, slot);
  }

  slot_info ensure_slot_and_repairs(Loop *l, BasicBlock *preheader, Value *orig_ptr_raw, Type *ty, Align a,
            bool is_volatile, const unordered_map<Value*, vector<StoreInst*>> &infrequent_stores,
            unordered_map<Value*, AllocaInst*> &slots, unordered_set<StoreInst*> &repair_dedup) {

    Value *key = strip_ptr(orig_ptr_raw);
    auto it = slots.find(key);
    if (it != slots.end()) {
      return {it->second, false};
    }

    Instruction *insert_before = preheader->getTerminator();
    auto *slot = new AllocaInst(ty, 0, nullptr, a, "fplicm.slot", insert_before);
    IRBuilder<> b(insert_before);
    LoadInst *init = b.CreateLoad(ty, orig_ptr_raw, "fplicm.ldslot");
    init->setAlignment(a);
    init->setVolatile(is_volatile);
    b.CreateStore(init, slot);

    if (auto its = infrequent_stores.find(key); its != infrequent_stores.end()) {
      for (StoreInst *st : its->second) {
        if (repair_dedup.insert(st).second) {
          insert_repair_after_store(st, orig_ptr_raw, ty, a, is_volatile, slot);
        }
      }
    }
    slots.emplace(key, slot);
    return {slot, true};
  }


  struct HW2CorrectnessPass : public PassInfoMixin<HW2CorrectnessPass> {

    PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM) {
      llvm::BlockFrequencyAnalysis::Result &bfi = FAM.getResult<BlockFrequencyAnalysis>(F);
      llvm::BranchProbabilityAnalysis::Result &bpi = FAM.getResult<BranchProbabilityAnalysis>(F);
      llvm::LoopAnalysis::Result &li = FAM.getResult<LoopAnalysis>(F);
      /* *******Implementation Starts Here******* */
      bool changed = false;
      for (Loop *l : li) {
        if (!l) {
          continue;
        }
        BasicBlock *preheader = l->getLoopPreheader();
        if (!preheader) {
          continue;
        }
        freq_path fp = compute_frequent_path(l, bpi);
        if (fp.blocks.empty()) {
          continue;
        }
        if (!backedge_to_header(fp.blocks.back(), l->getHeader())) {
          continue;
        }
        vector<BasicBlock*> infrequent = collect_infrequent_blocks(l, fp.set);
        if (infrequent.empty()) {
          continue;
        }

        unordered_map<Value*, vector<StoreInst*>> stores_freq, stores_infreq;
        unordered_set<Value*> ptrs_with_freq_stores, ptrs_with_infreq_stores;
        collect_stores_by_ptr(fp.blocks, stores_freq, ptrs_with_freq_stores);
        collect_stores_by_ptr(infrequent, stores_infreq, ptrs_with_infreq_stores);

        unordered_map<Value*, AllocaInst*> slot_for_ptr;
        unordered_set<StoreInst*> repair_already_inserted;
        for (BasicBlock *bb : fp.blocks) {
          for (auto it = bb->begin(); it != bb->end(); ) {
            Instruction *inst = &(*it);
            it++;
            auto *ld = dyn_cast<LoadInst>(inst);
            if (!ld) {
              continue;
            }
            Value *orig_ptr_raw = ld->getPointerOperand();
            Value *key = strip_ptr(orig_ptr_raw);
            if (!ptrs_with_infreq_stores.count(key)) {
              continue;
            }
            if (ptrs_with_freq_stores.count(key)) {
              continue;
            }
            slot_info si = ensure_slot_and_repairs(l, preheader, orig_ptr_raw, ld->getType(), ld->getAlign(),
                          ld->isVolatile(), stores_infreq, slot_for_ptr, repair_already_inserted);
            replace_load_with_slot(ld, si.slot);
            changed = true;
          }
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


