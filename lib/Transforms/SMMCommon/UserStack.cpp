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

namespace {
    struct UserStack : public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	UserStack() : ModulePass(ID) {}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	}

	virtual bool runOnModule (Module &mod) {
	    LLVMContext &context = mod.getContext();
	    IRBuilder<> builder(context);
	    // Types
	    Type *ty_int8 = IntegerType::get(context, 8);
	    PointerType* ptrty_int8 = PointerType::get(ty_int8, 0);
	    PointerType* ptrty_ptrint8 = PointerType::get(ptrty_int8, 0);

	    std::vector<Type*> call_args;
	    call_args.push_back(ptrty_ptrint8);
	    FunctionType* functy_inline_asm = FunctionType::get(
		    Type::getVoidTy(context), // Results
		    call_args, // Params
		    false); //isVarArg

	    // Functions
	    Function *func_main = mod.getFunction("main");
	    Function *func_smm_main = mod.getFunction("smm_main");

	    // Call graph
	    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph();

	    // Global Variables
	    GlobalVariable* cacheable_sp = new GlobalVariable(mod, // Module
		    ptrty_int8, //Type
		    false, //isConstant
		    GlobalValue::CommonLinkage, // Linkage
		    0, // Initializer
		    "_cacheable_sp");
	    cacheable_sp->setAlignment(8);
	    cacheable_sp->setInitializer(ConstantPointerNull::get(ptrty_int8));

	    GlobalVariable* cacheable_stack_base = new GlobalVariable(mod, // Module
		    ptrty_int8, //Type
		    false, //isConstant
		    GlobalValue::CommonLinkage, // Linkage
		    0, // Initializer
		    "_cacheable_stack_base");
	    cacheable_stack_base->setAlignment(8);
	    cacheable_stack_base->setInitializer(ConstantPointerNull::get(ptrty_int8));

	    GlobalVariable* cacheable_stack_end = new GlobalVariable(mod, // Module
		    ty_int8, //Type
		    false, //isConstant
		    GlobalValue::ExternalLinkage, // Linkage
		    0, // Initializer
		    "_cacheable_stack_end");

	    GlobalVariable* noncacheable_sp = new GlobalVariable(mod, // Module
		    ptrty_int8, //Type
		    false, //isConstant
		    GlobalValue::CommonLinkage, // Linkage
		    0, // Initializer
		    "_noncacheable_sp");
	    noncacheable_sp->setAlignment(8);
	    noncacheable_sp->setInitializer(ConstantPointerNull::get(ptrty_int8));


	    GlobalVariable* noncacheable_stack_base = new GlobalVariable(mod, // Module
		    ptrty_int8, //Type
		    false, //isConstant
		    GlobalValue::CommonLinkage, // Linkage
		    0, // Initializer
		    "_noncacheable_stack_base");
	    noncacheable_stack_base->setAlignment(8);
	    noncacheable_stack_base->setInitializer(ConstantPointerNull::get(ptrty_int8));

	    // Inline Assembly
	    InlineAsm *func_putSP = InlineAsm::get(functy_inline_asm, "mov $0, %rsp;", "*m,~{rsp},~{dirflag},~{fpsr},~{flags}",true);
	    InlineAsm *func_getSP = InlineAsm::get(functy_inline_asm, "mov %rsp, $0;", "=*m,~{dirflag},~{fpsr},~{flags}",true);

	    DEBUG(dbgs() << "\nStack:\n");
	    // Use noncacheable memory space for library function calls
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second); 
		Function *caller = cgn->getFunction();
		// Skip external nodes
		if (!caller)
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
		DEBUG(dbgs() << caller->getName() << "\n");

		std::unordered_set <CallInst *> funcCalls;

		// Process user-defined functions
		for (CallGraphNode::iterator cgni = cgn->begin(), cgne = cgn->end(); cgni != cgne; cgni++) {
		    // Insert management functions around function calls
		    if (CallInst *call_inst = dyn_cast<CallInst>(cgni->first)) {
			// Skip inline assebmly
			if (call_inst->isInlineAsm())
			    continue;
			Function *callee = call_inst->getCalledFunction();
			if (!callee) {
			    callee = dyn_cast <Function> (call_inst->getCalledValue()->stripPointerCasts());
			    assert(callee);
			}
			dbgs() << *call_inst << "\n";
			if(isLibraryFunction(callee) || callee->getName().count("c_call") == 1) {
			    funcCalls.insert(call_inst);
			} 
		    }
		}

		// If the caller calls any library function or a c_call function (if any), relocate stack pointer to a non-cacheable address before the call
		if (funcCalls.size() > 0) {
		    builder.SetInsertPoint(caller->getEntryBlock().getFirstNonPHI());
		    AllocaInst * oldSP = builder.CreateAlloca(ptrty_int8, nullptr, "old_sp");
		    for (auto ci = funcCalls.begin(), ce = funcCalls.end(); ci != ce; ++ci) {
			CallInst *call_inst = *ci;
			Function *callee = call_inst->getCalledFunction();
			if (!callee) {
			    callee = dyn_cast <Function> (call_inst->getCalledValue()->stripPointerCasts());
			    assert(callee);
			}
			DEBUG(dbgs() << "\t" << *call_inst << "\n");
			//Instruction *inst = dyn_cast<Instruction>(cgni->first);
			BasicBlock::iterator ii(call_inst);
			Instruction *next_inst = &*(ii);
			BasicBlock::iterator in(next_inst);
			++in;
			assert(in != call_inst->getParent()->end());
			// Before the function call
			builder.SetInsertPoint(ii);

			// Store the current value of SP to cacheable SP, since the call must happen in a user-defined function call
			if (callee->getName().count("c_call") == 1)
			    builder.CreateCall(func_getSP, cacheable_sp);

			// Store the current value of SP in stack
			builder.CreateCall(func_getSP, oldSP);
			// Set SP to noncacheable memory region
			//builder.CreateCall(func_putSP, noncacheable_stack_base);
			builder.CreateCall(func_putSP, noncacheable_sp);
			// After the function call
			builder.SetInsertPoint(in);
			// Recover the current value of SP
			builder.CreateCall(func_putSP, oldSP);
		    }
		}

	    }

	    // Relocate the SP to a cacheable address in c_call (if any)
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second); 
		Function *caller = cgn->getFunction();
		// Skip external nodes
		if (!caller)
		    continue;
		if (caller->getName().count("c_call") != 1) 
		    continue;
		DEBUG(dbgs() << caller->getName() << "\n");
		// Process user-defined functions
		builder.SetInsertPoint(caller->getEntryBlock().getFirstNonPHI());
		AllocaInst * oldSP = builder.CreateAlloca(ptrty_int8, nullptr, "old_sp");
		CallInst * call_inst;
		for (Function::iterator bi = caller->begin(), be = caller->end(); bi != be; ++bi) {
		    for (BasicBlock::iterator ii = bi->begin(), ie = bi->end(); ii != ie; ++ii) {
			call_inst = dyn_cast<CallInst>(&*ii);
			if (call_inst) {
			    Function *callee = call_inst->getCalledFunction();
			    // locate the call to user-defined functions in c_call functions
			    if(!callee) {
				DEBUG(dbgs() << "\t" << *call_inst << "\n"); 
				BasicBlock::iterator ii(call_inst);
				Instruction *next_inst = &*(ii);
				BasicBlock::iterator in(next_inst);
				++in;
				assert(in != call_inst->getParent()->end());
				// Before the function call
				builder.SetInsertPoint(ii);

				// Store the current value of SP to noncacheable SP, since the call must happen in a management function
				builder.CreateCall(func_getSP, noncacheable_sp);

				// Store the current value of SP in stack
				builder.CreateCall(func_getSP, oldSP);
				// Set SP to cacheable memory region
				builder.CreateCall(func_putSP, cacheable_sp);
				// After the function call
				builder.SetInsertPoint(in);
				// Recover the current value of SP
				builder.CreateCall(func_putSP, oldSP);
				break;
			    }
			}
		    }
		}
	    }


	    //Insert starting and ending code in main function, which is now a wrapper function of the real main function (smm_main)
	    BasicBlock *entry_block = &func_main->getEntryBlock();
	    for (BasicBlock::iterator ii = entry_block->begin(), ie = entry_block->end(); ii != ie; ii++) {
		Instruction *inst  = &*ii;
		if (CallInst *call_inst = dyn_cast<CallInst>(inst)) {
		    Function *callee = call_inst->getCalledFunction();
		    // Find the call to smm_main
		    if (callee == func_smm_main) {
			// Before the call
			builder.SetInsertPoint(&*ii);
			// Store the current value of SP
			builder.CreateCall(func_getSP, noncacheable_stack_base);
			// Initialize the noncacheable SP
			builder.CreateCall(func_getSP, noncacheable_sp);
			// Set the SP to the end of cacheable memory region 
			builder.CreateStore(cacheable_stack_end, cacheable_stack_base);
			builder.CreateCall(func_putSP, cacheable_stack_base);
			// After the call
			++ii;
			builder.SetInsertPoint(&*ii);
			// Restore the current value of SP
			builder.CreateCall(func_putSP, noncacheable_stack_base); 
			// Exit the loop
			break;
		    }

		}
	    }
	    return true;
	}

    };
}

char UserStack::ID = 1;
static RegisterPass<UserStack> Y("user-stack", "Place stack data from user code into a reserved address range)");
