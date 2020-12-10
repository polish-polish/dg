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

#include "llvm-slicer-preprocess.h"

using namespace llvm;

namespace dg {
namespace llvmdg {

static std::vector<llvm::Instruction *> getCallers(const Function *fun) {
    std::vector<llvm::Instruction *> retval;

    bool has_address_taken = false;
    for (auto use_it = fun->use_begin(), use_end = fun->use_end();
         use_it != use_end; ++use_it) {
#if ((LLVM_VERSION_MAJOR == 3) && (LLVM_VERSION_MINOR < 5))
        Value *user = *use_it;
#else
        Value *user = use_it->getUser();
#endif
        if (auto *C = dyn_cast<CallInst>(user)) {
            if (fun == C->getCalledFunction()) {
                retval.push_back(C);
            } else {
                llvm::errs() << "User: " << *user << "\n";
                has_address_taken = true;
            }
        } else if (auto *S = dyn_cast<StoreInst>(user)) {
            if (S->getValueOperand()->stripPointerCasts() == fun) {
                llvm::errs() << "User: " << *user << "\n";
                has_address_taken = true;
            } else {
                llvm::errs() << "Unhandled function use: " << *user  << "\n";
                assert(false && "Unhandled function use");
                has_address_taken = true; // to be safe
            }
        } else {
            llvm::errs() << "Unhandled function use: " << *user  << "\n";
            assert(false && "Unhandled function use");
            has_address_taken = true; // to be safe
        }
    }

    if (has_address_taken) {
        llvm::errs() << "ERROR: hasAddrTaken(" << fun->getName() << ")?\n";
        // add calls of function pointers that may call this function
        assert(false && "Not implemented yet");
        abort();
    }

    return retval;
}


// FIXME: refactor
// FIXME: configurable entry
bool cutoffDivergingBranches(Module& M, const std::string& entry,
                             const std::vector<const llvm::Value *>& criteria) {

    if (criteria.empty()) {
        assert(false && "Have no slicing criteria instructions");
        return false;
    }

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

    while (!queue.empty()) {
        auto *cur = queue.top();
        queue.pop();

        // paths from this block go to the slicing criteria
        relevant.insert(cur);

        if ((pred_begin(cur) == pred_end(cur))) {
            // pop-up from call
            for (auto *C : getCallers(cast<Function>(cur->getParent()))) {
              if (visited.insert(C->getParent()).second)
                queue.push(C->getParent());
            }
        } else {
          for (auto *pred : predecessors(cur)) {
            if (visited.insert(pred).second)
              queue.push(pred);
          }
        }
    }

    // FIXME
    // Now do the same from entry and kill the blocks that are not relevant
    // (a slicing criterion cannot be reached from them)

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
