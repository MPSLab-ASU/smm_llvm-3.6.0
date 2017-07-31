#include "llvm/Pass.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

#include <iostream>
#include <fstream>
#include <unordered_map>
#include <unordered_set>


#include "../SMMCommon/Helper.h"

using namespace llvm;

namespace {


    struct LibraryFunctionName : public ModulePass {
	static char ID; // Pass identification, replacement for typeid

	LibraryFunctionName() : ModulePass(ID) {
	}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	}

	virtual bool runOnModule(Module &mod) {
	    // Call graph
	    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph();

	    // Print out the names of library functionsa
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second);
		Function *fi = cgn->getFunction();
		// Skip external nodes
		if (!fi)
		    continue;
		// Print names of library functions
		if (isLibraryFunction(fi))
		    errs() << fi->getName().str() << "\n";
	    }

	    return true;
	}
    };
}

char LibraryFunctionName::ID = 0; //Id the pass.
static RegisterPass<LibraryFunctionName> A("libfunc", "Library functions pass"); //Register the pass.
//char WeightedCallGraphPass::ID = 1; //Id the pass.
//static RegisterPass<WeightedCallGraphPass> B("smmsm-wcg", "Weighted call graph pass"); //Register the pass.
