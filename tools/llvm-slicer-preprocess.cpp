#include <llvm/Config/llvm-config.h>

#if (LLVM_VERSION_MAJOR < 3)
#error "Unsupported version of LLVM"
#endif

// ignore unused parameters in LLVM libraries
#if (__clang__)
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
#else
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#endif

#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/CFG.h>
#include <llvm/Support/raw_os_ostream.h>

#if (__clang__)
#pragma clang diagnostic pop // ignore -Wunused-parameter
#else
#pragma GCC diagnostic pop
#endif

#include <set>
#include <vector>
#include <stack>

#include "dg/llvm/CallGraph/CallGraph.h"
#include "llvm-slicer-preprocess.h"

using namespace llvm;

namespace dg {
namespace llvmdg {

// FIXME: refactor
// FIXME: configurable entry
bool cutoffDivergingBranches(Module& M, const std::string& entry,
                             const std::vector<const llvm::Value *>& criteria) {

    if (criteria.empty()) {
        assert(false && "Have no slicing criteria instructions");
        return false;
    }

    llvmdg::LazyLLVMCallGraph CG(&M);
    std::set<BasicBlock*> relevant;
    std::set<BasicBlock*> visited;
    std::stack<BasicBlock*> queue; // not efficient...
    auto& Ctx = M.getContext();
    auto *entryFun = M.getFunction(entry);

    if (!entryFun) {
        llvm::errs() << "Did not find the entry function\n";
        return false;
    }

    // initialize the queue with blocks of slicing criteria
    for (auto *c : criteria) {
        auto *I = llvm::dyn_cast<Instruction>(const_cast<llvm::Value*>(c));
        if (!I) {
            continue;
        }
        if (visited.insert(I->getParent()).second) {
            queue.push(I->getParent());
        }
    }

    // get all backward reachable blocks in the ICFG, only those blocks
    // can be relevant in the slice
    while (!queue.empty()) {
        auto *cur = queue.top();
        queue.pop();

        // paths from this block go to the slicing criteria
        relevant.insert(cur);

        if ((pred_begin(cur) == pred_end(cur))) {
            // pop-up from call
            for (auto *C : CG.getCallsOf(cast<Function>(cur->getParent()))) {
              if (visited.insert(const_cast<llvm::BasicBlock*>(C->getParent())).second)
                queue.push(const_cast<llvm::BasicBlock*>(C->getParent()));
            }
        } else {
          for (auto *pred : predecessors(cur)) {
            if (visited.insert(pred).second)
              queue.push(pred);
          }
        }
    }

    // Now kill the irrelevant blocks (those from which the execution will
    // never reach the slicing criterion

    // FIXME Do also a pass from entry to remove dead code
    // FIXME: make configurable... and insert __dg_abort()
    // which will be internally implemented as abort() or exit().
    Type *argTy = Type::getInt32Ty(Ctx);
    auto exitC = M.getOrInsertFunction("exit",
                                       Type::getVoidTy(Ctx), argTy
#if LLVM_VERSION_MAJOR < 5
                                   , nullptr
#endif
                                   );
#if LLVM_VERSION_MAJOR >= 9
    auto exitF = cast<Function>(exitC.getCallee());
#else
    auto exitF = cast<Function>(exitC);
#endif
    exitF->addFnAttr(Attribute::NoReturn);

    for (auto& F : M) {
      for (auto& B : F) {
        if (relevant.count(&B) == 0) {
          auto new_CI = CallInst::Create(exitF, {ConstantInt::get(argTy, 0)});
          auto *point = B.getFirstNonPHI();
          //CloneMetadata(point, new_CI);
          new_CI->insertBefore(point);
        }
      }
    }

  return true;
}

} // namespace llvmdg
} // namespace dg
