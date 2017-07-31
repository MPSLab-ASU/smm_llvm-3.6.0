//===- --------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements several methods that are used to extract functions,
// loops, or portions of a module from the rest of the module.
//
//===----------------------------------------------------------------------===//


#include "llvm/Pass.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

#include "../SMMCommon/Helper.h"

using namespace llvm;

namespace {
    struct SizeEstimate: public ModulePass {
	static char ID; // Pass identification, replacement for typeid

	SizeEstimate() : ModulePass(ID) {
	}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	}

	virtual bool runOnModule(Module &mod) {
	    const DataLayout *dl = mod.getDataLayout();
	    for (Module::global_iterator gi = mod.global_begin(), ge = mod.global_end(); gi != ge; ++gi) {
		GlobalVariable *gvar = &*gi;
		StringRef gvar_name = gvar->getName();
		PointerType *gvar_type = gvar->getType();
		assert(gvar_type);
		if (isManagementVariable(gvar))
		    continue;
		if (gvar_name.startswith(".str"))
		    continue;
		if (gvar_name.startswith("str"))
		    continue;
		if (gvar_name.startswith("_spm"))
		    continue;
		if (gvar_name == "stdin")
		    continue;
		if (gvar_name == "stdout")
		    continue;
		if (gvar_name == "stderr")
		    continue;
		size_t gvar_size = getTypeSize(dl, gvar_type->getElementType());
		dbgs() << gvar_name << " " << gvar_size << "\n";
	    }
	    return true;
	}
    };

}

char SizeEstimate::ID = 0; //Id the pass.
static RegisterPass<SizeEstimate> X("estimate-size", "Dump the size of global variables"); //Register the pass.

