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
#include "llvm/PassManager.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

#include <fstream>
#include <queue>
#include <tuple>
#include <stack>
#include <utility>
#include <unordered_map>
#include <unordered_set>

#include "Helper.h"
#include "MemoryAllocator.h"

#define DEBUG_TYPE "smm"

using namespace llvm;

cl::opt<std::string> relocateCode("code", cl::desc("Specify whther to relocate code"), cl::value_desc("a string"));
cl::opt<std::string> relocateGlobal("global", cl::desc("Specify whether to relocate global variables"), cl::value_desc("a string"));


namespace {

    struct SMMPrologPass : public ModulePass {
	static char ID; // Pass identification, replacement for typeid

	SMMPrologPass() : ModulePass(ID) {
	}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	}

	virtual bool runOnModule(Module &mod) { // Transform the main function to an user-defined function (this step will destroy call graph)
	    LLVMContext &context = mod.getContext();
	     IRBuilder<> builder(context);
	    	    
	    // Functions
	    Function *func_main = mod.getFunction("main");

	    // Create an external function called smm_main
	    Function *func_smm_main = mod.getFunction("smm_main");

	    if (!func_smm_main) {
		func_smm_main = Function::Create(cast<FunctionType>(func_main->getType()->getElementType()), func_main->getLinkage(), "smm_main", &mod);
		ValueToValueMapTy VMap;
		std::vector<Value*> args;

		// Set up the mapping between arguments of main to those of smm_main
		Function::arg_iterator ai_new = func_smm_main->arg_begin();
		for (Function::arg_iterator ai = func_main->arg_begin(), ae = func_main->arg_end(); ai != ae; ++ai) { 
		    ai_new->setName(ai->getName());
		    VMap[ai] = ai_new;
		    args.push_back(ai);
		    ai_new++;
		}
		// Copy the function body from main to smm_main
		SmallVector<ReturnInst*, 8> Returns;
		CloneFunctionInto(func_smm_main, func_main, VMap, true, Returns);

		// Delete all the basic blocks in main function
		std::vector<BasicBlock*> bb_list;
		for (Function::iterator bi = func_main->begin(), be = func_main->end();  bi!= be; ++bi) { 
		    for (BasicBlock::iterator ii = bi->begin(), ie = bi->end(); ii != ie; ++ii) {
			ii->dropAllReferences(); //Make sure there are no uses of any instruction
		    } 
		    bb_list.push_back(bi);
		}
		for (unsigned int i = 0; i < bb_list.size(); ++i) {
		    bb_list[i]->eraseFromParent();
		}

		// Create the new body of main function which calls smm_main and return 0
		BasicBlock* entry_block = BasicBlock::Create(getGlobalContext(), "EntryBlock", func_main);
		builder.SetInsertPoint(entry_block);
		builder.CreateCall(func_smm_main, args);
		Value *zero = builder.getInt32(0);
		builder.CreateRet(zero);
	    }

	    return true;
	}
    };
}

char SMMPrologPass::ID = 0; //Id the pass.
static RegisterPass<SMMPrologPass> X("smm-prolog", "SMM Prolog Pass"); //Register the pass.
