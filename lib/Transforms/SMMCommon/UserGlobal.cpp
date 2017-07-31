#include "llvm/Pass.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/Debug.h"

#include "Helper.h"

#define DEBUG_TYPE "smmim"

using namespace llvm;

namespace {
    struct UserGlobal : public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	UserGlobal() : ModulePass(ID) {}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	}

	virtual bool runOnModule (Module &mod) {
	    LLVMContext &context = mod.getContext();
	    IRBuilder<> builder(context);
	    // Global
	    DEBUG(dbgs() << "\nGlobal:\n");
	    for (Module::global_iterator gi = mod.global_begin(), ge = mod.global_end(); gi != ge; ++gi) {
		if(GlobalVariable *gvar = &*gi) {
		    if (!isManagementVariable(gvar)) {
			StringRef gvar_name = gvar->getName();
			if (gvar_name.startswith(".str"))
			    continue;
			if (gvar_name.startswith("str"))
			    continue;
			if (gvar_name == "stdin")
			    continue;
			if (gvar_name == "stdout")
			    continue;
			if (gvar_name == "stderr")
			    continue;

			GlobalValue::LinkageTypes gvar_linkage = gvar->getLinkage();
			if (gvar_linkage != GlobalValue::LinkageTypes::ExternalLinkage) {
			    gvar->setLinkage(GlobalValue::LinkageTypes::ExternalLinkage);
			}
			if (std::string(gvar->getSection()) == "")
			    gvar->setSection(".user_data");


		    } 
		    DEBUG(dbgs() << gvar->getName() << "\t" << *gvar->getType()  << "\t" << gvar->getSection() << "\t" << gvar->getLinkage() << "\n");
		}
	    }
	    return true;
	}

    };
}

char UserGlobal::ID = 2;
static RegisterPass<UserGlobal> C("user-global", "Place global data from user code into a reserved address range)");
