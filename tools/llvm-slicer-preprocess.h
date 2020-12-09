#ifndef LLVM_SLICER_PREPROCESS_H_
#define LLVM_SLICER_PREPROCESS_H_

#include <vector>

namespace llvm {
    class Module;
    class Instruction;
}

namespace dg {
namespace llvmdg {


bool cutoffDiveringBranches(llvm::Module& M,
                           const std::vector<llvm::Instruction *>& criteria);

} // namespace llvmdg
} // namespace dg

#endif
