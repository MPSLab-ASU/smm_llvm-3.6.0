#include "llvm/Pass.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/Debug.h"

#include "Helper.h"

#define DEBUG_TYPE "smmim"

using namespace llvm;

//cl::opt<std::string> overlaying("overlaying", cl::desc("Specify the file that stores the mapping from functions to regions"), cl::value_desc("a string"));

namespace {
    struct UserHeap : public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	UserHeap() : ModulePass(ID) {}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	}

	virtual bool runOnModule (Module &mod) {
	    LLVMContext &context = mod.getContext();
	    IRBuilder<> builder(context);
	    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph();
	    Function *func_main = mod.getFunction("main");
	    Function *func_smm_main = mod.getFunction("smm_main");
	    Function *func_heap_allocator = mod.getFunction("_allocate");
	    assert(func_heap_allocator);
	    DEBUG(dbgs() << "\nHeap:\n");
	    // Substitute calls to malloc with calls to allocate
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		if(CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second)) {
		    Function *caller = cgn->getFunction();
		    // Skip external nodes
		    if(!caller)
			continue;
		    // Skip library functions
		    if (isLibraryFunction(caller))
			continue;
		    // Skip management functions
		    if (isManagementFunction(caller))
			continue;
		    // Skip the wrapper of the main function
		    if (func_smm_main && caller == func_main)
			continue;

		    //DEBUG(errs() << caller->getName() << "\n");
		    errs() << caller->getName() << "\n";
		    for (CallGraphNode::iterator cgni = cgn->begin(), cgne = cgn->end(); cgni != cgne; ++cgni) {
			if (!cgni->first) 
			    continue;
			CallInst *call_inst = dyn_cast <CallInst> (cgni->first);
			if (call_inst->isInlineAsm())
			    continue;
			CallGraphNode *callee_cgn = cgni->second;
			Function *callee = callee_cgn->getFunction();
			if (!callee) {
			    callee = dyn_cast <Function> (call_inst->getCalledValue()->stripPointerCasts());
			    assert(callee);
			}
			if (callee->getName() == "malloc") {
			    DEBUG(dbgs() << "\t" << *call_inst << "\n");

			    assert(call_inst->getNumArgOperands() == 1);
			    builder.SetInsertPoint(call_inst);
			    CallInst *new_malloc =  builder.CreateCall(func_heap_allocator, call_inst->getArgOperand(0));
			    //DEBUG(dbgs() << "\t\t" << *new_malloc <<"\n");

			    DEBUG(dbgs() << "\t\tOld uses:\n");
			    for (Value::use_iterator ui = call_inst->use_begin(), ue = call_inst->use_end(); ui != ue; ++ui) {
				DEBUG(dbgs() << "\t\t\t" << *ui->getUser() << "\n");
			    }


			    call_inst->replaceAllUsesWith (new_malloc);
			    call_inst->eraseFromParent();
			}
		    }
		}
	    }
	    // Erase all the free
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		if(CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second)) {
		    Function *caller = cgn->getFunction();
		    // Skip external nodes
		    if(!caller)
			continue;
		    // Skip library functions
		    if (isLibraryFunction(caller))
			continue;
		    // Skip management functions
		    if (isManagementFunction(caller))
			continue;
		    // Skip the wrapper of the main function
		    if (func_smm_main && caller == func_main)
			continue;
		    //DEBUG(errs() << caller->getName() << "\n");
		    errs() << caller->getName() << "\n";
		    for (CallGraphNode::iterator cgni = cgn->begin(), cgne = cgn->end(); cgni != cgne; ++cgni) {
			if (!cgni->first) 
			    continue;
			CallInst *call_inst = dyn_cast <CallInst> (cgni->first);
			if (call_inst->isInlineAsm())
			    continue;
			CallGraphNode *callee_cgn = cgni->second;
			Function *callee = callee_cgn->getFunction();
			if (!callee) {
			    callee = dyn_cast <Function> (call_inst->getCalledValue()->stripPointerCasts());
			    assert(callee);
			}
			if (callee->getName() == "free") {
			    DEBUG(dbgs() << "\t" << *call_inst << "\n");
			    call_inst->eraseFromParent();

			}
		    }
		}
	    }
	    return true;
	}

    };
}

char UserHeap::ID = 3;
static RegisterPass<UserHeap> D("user-heap", "Place heap data from user code into a reserved address range)");
