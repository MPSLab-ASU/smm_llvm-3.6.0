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
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"

#include "Mnmt.h"
#include "../SMMCommon/Helper.h"


#define DEBUG_TYPE "smmsm"

using namespace llvm;

namespace {

    struct StackManagementPass : public ModulePass {
	static char ID; // Pass identification, replacement for typeid

	StackManagementPass() : ModulePass(ID) {
	}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	}

	virtual bool runOnModule(Module &mod) {
	    LLVMContext &context = mod.getContext();

	    // Pointer Types
	    PointerType* ptrty_int8 = PointerType::get(IntegerType::get(context, 8), 0);
	    PointerType* ptrty_ptrint8 = PointerType::get(ptrty_int8, 0);

	    std::vector<Type*> call_args;
	    call_args.push_back(ptrty_ptrint8);
	    FunctionType* functy_inline_asm = FunctionType::get(
		    Type::getVoidTy(context), // Results
		    call_args, // Params
		    false); //isVarArg

	    // External Variables
	    GlobalVariable* spm_stack_end = new GlobalVariable(mod, // Module
		    IntegerType::get(context, 8), //Type
		    false, //isConstant
		    GlobalValue::ExternalLinkage, // Linkage
		    0, // Initializer
		    "_spm_stack_end");

	    // Global Variables
	    GlobalVariable* mem_stack_base = mod.getGlobalVariable("_mem_stack_base");
	    GlobalVariable* spm_stack_base = mod.getGlobalVariable("_spm_stack_base");

	    // Functions
	    Function *func_main = mod.getFunction("main");
	    Function *func_smm_main = mod.getFunction("smm_main");
	    assert(func_smm_main);

	    // Inline Assembly
	    InlineAsm *func_putSP = InlineAsm::get(functy_inline_asm, "mov $0, %rsp;", "*m,~{rsp},~{dirflag},~{fpsr},~{flags}",true);
	    InlineAsm *func_getSP = InlineAsm::get(functy_inline_asm, "mov %rsp, $0;", "=*m,~{dirflag},~{fpsr},~{flags}",true);

	    // Call graph
	    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph();


	    // Step 1: Insert pointer management functions
	    DEBUG(errs() << "Pointer management {\n");

	    DEBUG(errs() << "insert g2l functions {\n");
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		CallGraphNode *cgn = cgi->second;
		Function *fi = cgn->getFunction();
		// Skip external nodes
		if (!fi)
		    continue;
		DEBUG(errs() << "\t" << fi->getName() << "\n");
		// Skip library functions
		if (isLibraryFunction(fi))
		    continue;
		// Skip stack management functions
		if (isManagementFunction(fi))
		    continue;
		// Skip main function
		if (fi == func_main)
		    continue;
		// Insert g2l functions
		g2l_pointer_management_instrumentation(mod, cgn);
	    }

	    DEBUG(errs() << "Insert l2g functions {\n");

	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		if(CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second)) {
		    Function *fi = cgn->getFunction();
		    // Skip external nodes
		    if(!fi)
			continue;
		    // Skip library functions
		    if (isLibraryFunction(fi))
			continue;
		    // Skip management functions
		    if (isManagementFunction(fi))
			continue;
		    // Skip main function
		    if (fi == func_main)
			continue;

		    // insert l2g functions
		    l2g_pointer_management_instrumentation(mod, cgn);
		}
	    }

	    DEBUG(errs() << "}\n\n\n");

	    // Step 2: Insert stack frame management functions
	    DEBUG(errs() << "Stack frame management {\n");

	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second); 
		Function *fi = cgn->getFunction();
		// Skip external nodes
		if (!fi)
		    continue;
		//Skip library functions
		if (isLibraryFunction(fi))
		    continue;
		// Skip stack management functions
		if (isManagementFunction(fi))
		    continue;
		// Skip main function
		if (fi == func_main)
		    continue;

		DEBUG(errs() << fi->getName() << "\n");

		// Process user-defined functions
		for (CallGraphNode::iterator cgni = cgn->begin(), cgne = cgn->end(); cgni != cgne; cgni++) {
		    // Insert management functions around function calls
		    if (CallInst *call_inst = dyn_cast<CallInst>(cgni->first)) {
			Instruction *inst = dyn_cast<Instruction>(cgni->first);
			BasicBlock::iterator ii(inst);
			Instruction *next_inst = &*(++ii);
			BasicBlock::iterator in(next_inst);
			assert(in != call_inst->getParent()->end());

			// Skip inline assebmly
			if (call_inst->isInlineAsm())
			    continue;
			Function *callee = call_inst->getCalledFunction();
			// If the callee is a function pointer or not a management function and an instrinsic function, go ahead and process
			if(callee) { 
			    if (isManagementFunction(callee))
				continue;
			    if (callee->isIntrinsic())
				continue;
			} 

			stack_frame_management_instrumentation (mod, call_inst);
		    }
		}
	    }
	     

	    DEBUG(errs() << "}\n\n");

	    // Step 3: Insert starting and ending code in main function, which is now a wrapper function of the real main function (smm_main)
	    BasicBlock *entry_block = &func_main->getEntryBlock();
	    IRBuilder<> builder(entry_block);

	    for (BasicBlock::iterator ii = entry_block->begin(), ie = entry_block->end(); ii != ie; ii++) {
		Instruction *inst  = &*ii;
		if (CallInst *call_inst = dyn_cast<CallInst>(inst)) {
		    Function *callee = call_inst->getCalledFunction();
		    // Find the call to smm_main
		    if (callee == func_smm_main) {
			// Before the call
			builder.SetInsertPoint(&*ii);
			builder.CreateCall(func_getSP, mem_stack_base);
			builder.CreateStore(spm_stack_end, spm_stack_base);
			builder.CreateCall(func_putSP, spm_stack_base);
			// After the call
			++ii;
			builder.SetInsertPoint(&*ii);
			builder.CreateCall(func_putSP, mem_stack_base); 
			// Exit the loop
			break;
		    }

		}
	    }


	    return true;
	}
    };
}

char StackManagementPass::ID = 0; //Id the pass.
static RegisterPass<StackManagementPass> X("smmsm", "Stack Management Pass"); //Register the pass.

