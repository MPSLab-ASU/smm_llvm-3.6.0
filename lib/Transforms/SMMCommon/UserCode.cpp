#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/YAMLTraits.h"

#include "Helper.h"

#define DEBUG_TYPE "smmim"

using namespace llvm;

namespace {
    struct UserCode : public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	UserCode() : ModulePass(ID) {}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	}

	virtual bool runOnModule (Module &mod) {
	    Function *func_main = mod.getFunction("main");
	    Function *func_smm_main = mod.getFunction("smm_main");
	    DEBUG(dbgs() << "\nCode:\n");
	    for (Module::iterator fi = mod.begin(), fe = mod.end(); fi != fe; ++fi) {
		Function *func = &*fi;
		// Skip library functions
		if (isLibraryFunction(func))
		    continue;
		// Skip management functions
		// Skip the wrapper of the main function
		if (func_smm_main && func == func_main) 
		    continue;
		if (isManagementFunction(func)) {
		    if (std::string(func->getSection()) == "") {
			func->setSection(".management_text");
		    }
		}
		// Place all the user functions to a custom region
		else if (std::string(func->getSection()) == "") {
		    func->setSection(".user_text");
		}
		//
		DEBUG(dbgs() << func->getName() << "\t" << func->getSection() << "\n");
	    }
	    return true;
	}

    };
}

char UserCode::ID = 0;
static RegisterPass<UserCode> X("user-code", "Place code from user code into a reserved address range)");
