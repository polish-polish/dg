#ifndef _LLVM_DG_RD_H_
#define _LLVM_DG_RD_H_

#include <unordered_map>
#include <memory>
#include <type_traits>

// ignore unused parameters in LLVM libraries
#if (__clang__)
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
#else
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
#endif

#include <llvm/Support/raw_os_ostream.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Constants.h>

#if (__clang__)
#pragma clang diagnostic pop // ignore -Wunused-parameter
#else
#pragma GCC diagnostic pop
#endif

#include "dg/analysis/DataDependence/DataDependence.h"

#include "dg/llvm/analysis/PointsTo/PointerAnalysis.h"
#include "dg/llvm/analysis/DataDependence/LLVMDataDependenceAnalysisOptions.h"

namespace dg {
namespace analysis {

class LLVMReadWriteGraphBuilder;

class LLVMDataDependenceAnalysis
{
    const llvm::Module *m;
    dg::LLVMPointerAnalysis *pta;
    const LLVMDataDependenceAnalysisOptions _options;
    LLVMReadWriteGraphBuilder *builder{nullptr};
    std::unique_ptr<DataDependenceAnalysis> DDA;

    LLVMReadWriteGraphBuilder *createBuilder();
    DataDependenceAnalysis *createDDA();

public:

    LLVMDataDependenceAnalysis(const llvm::Module *m,
                            dg::LLVMPointerAnalysis *pta,
                            const LLVMDataDependenceAnalysisOptions& opts)
    : m(m), pta(pta), _options(opts), builder(createBuilder()), DDA(createDDA()) {}

    ~LLVMDataDependenceAnalysis();

    void run() {
        assert(builder);
        assert(DDA);
        assert(getRoot());

        DDA->run();
    }

    RWNode *getRoot() { return DDA->getRoot(); }
    ReadWriteGraph *getGraph() { return DDA->getGraph(); }
    RWNode *getNode(const llvm::Value *val);
    const RWNode *getNode(const llvm::Value *val) const;

    // let the user get the nodes map, so that we can
    // map the points-to informatio back to LLVM nodes
    const std::unordered_map<const llvm::Value *, RWNode *>& getNodesMap() const;
    const std::unordered_map<const llvm::Value *, RWNode *>& getMapping() const;

    RWNode *getMapping(const llvm::Value *val);
    const RWNode *getMapping(const llvm::Value *val) const;

    bool isUse(const llvm::Value *val) const {
        auto nd = getNode(val);
        return nd && !nd->getUses().empty();
    }

    bool isDef(const llvm::Value *val) const {
        auto nd = getNode(val);
        return nd && (!nd->getDefines().empty() || !nd->getOverwrites().empty());
    }

    std::vector<RWNode *> getNodes() {
        assert(DDA);
        // FIXME: this is insane, we should have this method defined here
        // not in DDA
        return getGraph()->getNodes(getRoot());
    }

    std::vector<RWNode *> getDefinitions(RWNode *where, RWNode *mem,
                                                 const Offset& off, const Offset& len) {
        return DDA->getDefinitions(where, mem, off, len);
    }

    std::vector<RWNode *> getDefinitions(RWNode *use) {
        return DDA->getDefinitions(use);
    }

    std::vector<RWNode *> getDefinitions(llvm::Value *use) {
        auto node = getNode(use);
        assert(node);
        return getDefinitions(node);
    }

    // return instructions that define the given value
    // (the value must read from memory, e.g. LoadInst)
    std::vector<llvm::Value *> getLLVMDefinitions(llvm::Value *use);
};


} // namespace analysis
} // namespace dg

#endif