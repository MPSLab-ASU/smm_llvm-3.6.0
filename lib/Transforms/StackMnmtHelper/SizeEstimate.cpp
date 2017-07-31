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

cl::opt<std::string> stack_frame_size("stack-frame-size", cl::desc("Specify the file that stores the sizes of stack frames"), cl::value_desc("a string"));

namespace {
    struct SizeEstimate : public ModulePass {
	static char ID; // Pass identification, replacement for typeid

	SizeEstimate() : ModulePass(ID) {
	}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	}
	virtual bool runOnModule(Module &mod) {
	    unsigned long frameSize;
	    //unsigned path_id;
	    std::string func_name;
	    //std::ostream &ofs = std::cerr;
	    std::ifstream ifs;
	    std::unordered_map <std::string, unsigned long> stackFrameSize;
	    std::vector<std::vector<CallGraphNode::CallRecord *> > paths;
	    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph(); // call graph
	    CallGraphNode *cgn_main = cg[mod.getFunction("main")]; 
	    CallGraphNode::CallRecord *root;

	    unsigned long minStackSize = 0, maxStackSize = 0;

	    // Initialize root node by main function
	    for (CallGraphNode::iterator cgni = cg.begin()->second->begin(), cgne = cg.begin()->second->end(); cgni != cgne; cgni++) {
		if (cgni->second == cgn_main) {
		    root = &*cgni;
		    break;
		}
	    }
	    assert(CallGraphNode::iterator(root) != cg.begin()->second->end());

	    // Get all the paths from the call graph rooted at main
	    auto res = getPaths(root); 
	    paths = res.first;

	    ifs.open(stack_frame_size, std::fstream::in);
	    // Read function stack sizes
	    while (ifs.good()) {
		ifs >> func_name >> frameSize;
		stackFrameSize[func_name]  = frameSize;
	    }

	    for (size_t i = 0; i < paths.size(); i++) {
		unsigned long frameSize = 0;
		//dbgs() << "path " << i << " : ";
		for (size_t j = 0; j < paths[i].size(); j++) {
		    if (paths[i][j]->second->getFunction()) {
			std::string func_name = paths[i][j]->second->getFunction()->getName().str();
			if (stackFrameSize.find(func_name) != stackFrameSize.end()) {
			    frameSize += stackFrameSize[func_name];
			    if (stackFrameSize[func_name] > minStackSize)
				minStackSize = stackFrameSize[func_name];
			} else {
			    // TODO Get library function stack sizes
			    //errs() << func_name << "\n";
			    //ofs << std::numeric_limits<int>::max();
			}
			//dbgs() << " " << func_name << " (" << frameSize << ")";
		    } 
		}
		if (frameSize > maxStackSize) {
		    maxStackSize = frameSize;
		    //path_id = i;
		}
		//dbgs() << "\n";
	    }

	    std::cerr << "minimum " << minStackSize << "\n";
	    std::cerr << "maximum " << maxStackSize << "\n";

	    ifs.close();

	    return false;
	}

    };


}

char SizeEstimate::ID = 2; //Id the pass.
static RegisterPass<SizeEstimate> C("estimate-size", "Estimate the range of stack size"); //Register the pass.
