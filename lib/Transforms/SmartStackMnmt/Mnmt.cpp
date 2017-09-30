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


#include "../SMMCommon/Helper.h"

#define DEBUG_TYPE "smmssm"

using namespace llvm;

// Transform

void g2l_pointer_management_instrumentation(Module &mod, CallGraphNode *cgn) {
    LLVMContext &context = mod.getContext();
    const DataLayout *dl = mod.getDataLayout();

    // Pointer Types
    PointerType* ptrty_int8 = PointerType::get(IntegerType::get(context, 8), 0);
    PointerType* ptrty_ptrint8 = PointerType::get(ptrty_int8, 0);
    // Function Types
    std::vector<Type*> arg_types;
    arg_types.push_back(ptrty_ptrint8);
    FunctionType* functy_inline_asm = FunctionType::get(
	    Type::getVoidTy(context), // Results
	    arg_types, // Params
	    false); //isVarArg
    InlineAsm *func_getSP = InlineAsm::get(functy_inline_asm, "mov %rsp, $0;", "=*m,~{dirflag},~{fpsr},~{flags}",true);

    GlobalVariable* stack_pointer = mod.getGlobalVariable("_stack_pointer");

    Function *func_g2l = mod.getFunction("_g2l");
    Function *func_ptr_wr = mod.getFunction("_ptr_wr");
    assert(func_ptr_wr);

    Function *func = cgn->getFunction();

    DEBUG(errs() << "\t" << func->getName() << "\n");


    for (Function::arg_iterator ai = func->arg_begin(), ae = func->arg_end(); ai != ae; ai++) {
	// Find user instructions of pointer-type arguments and replace the uses with the result of calling g2l on the arguments
	if (ai->getType()->isPointerTy()) { 
	    Value *val = &*ai;

	    DEBUG(errs() << "\t\t" << *val << " " << val->getNumUses() << " " << *val->getType()->getPointerElementType() << " " << getTypeSize(dl, val->getType()->getPointerElementType()) <<  "\n");

	    // Find the uses of the arguments of interest and call g2l on them
	    for (Value::use_iterator ui = val->use_begin(), ue = val->use_end(); ui != ue; ) {
		// Move iterator to next use before the current use is destroyed
		Use *u = &*ui++;
		unsigned operand_num = u->getOperandNo();
		Instruction *user_inst = dyn_cast<Instruction>(u->getUser());
		assert(user_inst);

		DEBUG(errs() << "\t\t\t" << *user_inst << "\n");

		Instruction *insert_point = user_inst;
		// If the use is in a phi instruction, insert g2l function before the terminator of the incoming basic block
		if (PHINode *target = dyn_cast<PHINode>(user_inst))
		    insert_point = target->getIncomingBlock(operand_num)->getTerminator();
		IRBuilder<> builder(insert_point); // Instruction will be inserted before this instruction
		// Cast the value (in this case, a memory address) to be of char pointer type required by g2l function
		Value *g2l_arg = builder.CreatePointerCast(val, Type::getInt8PtrTy(context), "g2l_arg");
		std::vector<Value *>g2l_args;
		g2l_args.push_back(g2l_arg);
		g2l_args.push_back(builder.getInt64(getTypeSize(dl, val->getType()->getPointerElementType())));
		// Call the function g2l with the value with cast type
		//   Insert getSP(_stack_pointer)
		builder.CreateCall(func_getSP, stack_pointer);
		Value *g2l_ret = builder.CreateCall(func_g2l, g2l_args, "g2l_ret");

		// Cast the result back to be of the original type
		Value *g2l_result = builder.CreatePointerCast(g2l_ret, val->getType(), "g2l_result");
		// Replace the uses of the pointer argument
		u->set(g2l_result);

		// Insert a call to ptr_wr function after every store to the arguments or their GEP expressions.
		if (StoreInst *st_inst = dyn_cast <StoreInst>(user_inst)) {
		    if (st_inst->getPointerOperand() ==  val) {
			BasicBlock::iterator ii(insert_point);
			BasicBlock::iterator in = ii;
			in++;
			IRBuilder<>builder(&*in);
			Value* arg1 = builder.CreatePointerCast(val, Type::getInt8PtrTy(context), "ptr_wr_arg");
			Value* arg2 = builder.getInt64(getTypeSize(dl, val->getType()->getPointerElementType()));
			std::vector<Value *> wr_args;
			wr_args.push_back(arg1);
			wr_args.push_back(arg2);
			//   Insert getSP(_stack_pointer)
			builder.CreateCall(func_getSP, stack_pointer);
			builder.CreateCall(func_ptr_wr, wr_args);
		    }
		} else if (user_inst->getOpcode() == Instruction::GetElementPtr) { 
		    for (Value::use_iterator uui = user_inst->use_begin(), uue = user_inst->use_end(); uui != uue; uui++) {

			DEBUG(errs() << "\t\t\t\t" << *uui->getUser() << "\n");

			if (StoreInst *st_inst = dyn_cast<StoreInst>(uui->getUser())) {
			    if (st_inst->getPointerOperand() == user_inst) {
				BasicBlock::iterator ii(st_inst);
				BasicBlock::iterator in = ii;
				in++;
				IRBuilder<>builder(&*in);
				Value* arg1 = builder.CreatePointerCast(val, Type::getInt8PtrTy(context), "ptr_wr_arg");
				Value* arg2 = builder.getInt64(getTypeSize(dl, val->getType()->getPointerElementType()));
				std::vector<Value *> wr_args;
				wr_args.push_back(arg1);
				wr_args.push_back(arg2);
				//   Insert getSP(_stack_pointer)
				builder.CreateCall(func_getSP, stack_pointer);
				builder.CreateCall(func_ptr_wr, wr_args);
			    }
			}
		    }
		}
	    }
	}


    }
}


void l2g_pointer_management_instrumentation(Module &mod, CallGraphNode *cgn) {
    LLVMContext &context = mod.getContext();
    // Pointer Types
    PointerType* ptrty_int8 = PointerType::get(IntegerType::get(context, 8), 0);
    PointerType* ptrty_ptrint8 = PointerType::get(ptrty_int8, 0);
    // Function Types
    std::vector<Type*> arg_types;
    arg_types.push_back(ptrty_ptrint8);
    FunctionType* functy_inline_asm = FunctionType::get(
	    Type::getVoidTy(context), // Results
	    arg_types, // Params
	    false); //isVarArg
    InlineAsm *func_getSP = InlineAsm::get(functy_inline_asm, "mov %rsp, $0;", "=*m,~{dirflag},~{fpsr},~{flags}",true);

    GlobalVariable* stack_pointer = mod.getGlobalVariable("_stack_pointer");

    Function *func_l2g = mod.getFunction("_l2g");

    DEBUG(errs() << "\t" << cgn->getFunction()->getName() << "\n");


    for (CallGraphNode::iterator cgni = cgn->begin(), cgne = cgn->end(); cgni != cgne; cgni++) {
	if (CallInst *call_inst = dyn_cast<CallInst>(cgni->first)) {
	    // Skip inline assembly
	    if (call_inst->isInlineAsm())
		continue;
	    Function *callee = call_inst->getCalledFunction();

	    // If the called function is a function pointer or if it is not a stack management or an intrinsic function, go ahead and process
	    if (callee) { 
		if (isManagementFunction(callee))
		    continue;
		if (isLibraryFunction(callee))
		    continue;
		assert(!callee->isIntrinsic());
		if (callee->isIntrinsic())
		    continue;
	    } 


	    DEBUG(errs() << "\t\t" << *call_inst << "\n");

	    //  Insert l2g function before function calls wth pointer-type arguments
	    for (unsigned int i = 0, n = call_inst->getNumArgOperands(); i < n; i++) { 
		Value *operand = call_inst->getArgOperand(i);
		if (operand->getType()->isPointerTy() ) {

		    DEBUG(errs() << "\t\t\t" << *operand << "\n");

		    IRBuilder<> builder(call_inst); // Instruction will be inserted before ii
		    // Cast the value (in this case, a memory address) to be of char pointer type required by l2g function
		    Value *l2g_arg = builder.CreatePointerCast(operand, Type::getInt8PtrTy(context), "l2g_arg"); 
		    // Call the function l2g with the value with cast type
		    //   Insert getSP(_stack_pointer)
		    CallInst::Create(func_getSP, stack_pointer, "", call_inst);
		    Value *l2g_ret = builder.CreateCall(func_l2g, l2g_arg, "l2g_ret"); 
		    // Cast the result back to be of the original type
		    Value *l2g_result = builder.CreatePointerCast(l2g_ret, operand->getType(), "l2g_result"); 
		    // Replace the use of the original memory address with the translated address
		    call_inst->setOperand(i, l2g_result); 
		}
	    }
	}
    }

}

void stack_frame_management_instrumentation (Module &mod, CallInst *call_inst) {
    LLVMContext &context = mod.getContext();
    IRBuilder<> builder(context);

    // Pointer Types
    PointerType* ptrty_int8 = PointerType::get(IntegerType::get(context, 8), 0);
    PointerType* ptrty_ptrint8 = PointerType::get(ptrty_int8, 0);
    // Function Types
    std::vector<Type*> arg_types;
    arg_types.push_back(ptrty_ptrint8);
    FunctionType* functy_inline_asm = FunctionType::get(
	    Type::getVoidTy(context), // Results
	    arg_types, // Params
	    false); //isVarArg

    // Global Variables
    GlobalVariable* spm_stack_base = mod.getGlobalVariable("_spm_stack_base");
    GlobalVariable* mem_stack_depth = mod.getGlobalVariable("_mem_stack_depth");
    GlobalVariable* mem_stack = mod.getGlobalVariable("_mem_stack");
    GlobalVariable* stack_pointer = mod.getGlobalVariable("_stack_pointer");


    // Inline Assembly
    InlineAsm *func_putSP = InlineAsm::get(functy_inline_asm, "mov $0, %rsp;", "*m,~{rsp},~{dirflag},~{fpsr},~{flags}",true);
    InlineAsm *func_getSP = InlineAsm::get(functy_inline_asm, "mov %rsp, $0;", "=*m,~{dirflag},~{fpsr},~{flags}",true);

    // Functions
    Function *func_sstore = mod.getFunction("_sstore");
    Function *func_sload = mod.getFunction("_sload");

    BasicBlock::iterator ii(call_inst);
    Instruction *next_inst = &*(++ii);

    DEBUG(errs() << "\t" << *call_inst <<  " " << call_inst->getNumUses() << "\n");

    // Before the function call
    builder.SetInsertPoint(call_inst);
    // Insert a sstore function
    //   Insert getSP(_stack_pointer)
    builder.CreateCall(func_getSP, stack_pointer);
    builder.CreateCall(func_sstore);
    // Insert putSP(_spm_stack_base)
    builder.CreateCall(func_putSP, spm_stack_base);
    // After the function call
    builder.SetInsertPoint(next_inst);
    ConstantInt* int32_0 = builder.getInt32(0);
    ConstantInt* int64_1 = builder.getInt64(1);
    // Read value of _mem_stack_depth
    LoadInst * mem_stack_depth_val = builder.CreateLoad(mem_stack_depth);
    // Calculate _mem_stack_depth - 1
    Value* mem_stack_depth_val1 = builder.CreateSub(mem_stack_depth_val, int64_1, "sub");
    // Get the address of _mem_stack[_mem_stack_depth-1]
    std::vector<Value*> arrayidx;
    arrayidx.push_back(int32_0);
    arrayidx.push_back(mem_stack_depth_val1);
    Value* arrayelem = builder.CreateGEP(mem_stack, arrayidx, "arrayelem");
    // Get &_mem_stack[_mem_stack_depth-1].spm_address
    std::vector<Value*> fieldidx;
    fieldidx.push_back(int32_0);
    fieldidx.push_back(int32_0);
    Value* then_stack_pointer = builder.CreateGEP(arrayelem, fieldidx, "then_stack_pointer");
    // Insert putSP(_mem_stack[_mem_stack_depth-1].spm_addr)
    builder.CreateCall(func_putSP, then_stack_pointer);
    // Insert a corresponding sload function
    builder.CreateCall(func_sload);

    // Skip if the function does not have return value
    Type * retty = call_inst->getType();
    if (retty->isVoidTy())
	return;
    // Skip if the return value is never used
    if (call_inst->getNumUses() == 0) 
	return;
    // Save return value in a global variable temporarily until sload is executed if it is used
    // Always create a new global variable in case of recursive functions
    GlobalVariable *gvar_ret = new GlobalVariable(mod, //Module
	    retty, //Type
	    false, //isConstant
	    GlobalValue::ExternalLinkage, //linkage
	    0, // Initializer
	    "_gvar_ret"); //Name
    // Initialize the temporary global variable
    gvar_ret->setInitializer(Constant::getNullValue(retty));
    // Save return value to the global variable before sload is called
    StoreInst *st_ret = new StoreInst(call_inst, gvar_ret);
    st_ret->insertAfter(call_inst);

    for (Value::use_iterator ui_ret = call_inst->use_begin(), ue_ret = call_inst->use_end(); ui_ret != ue_ret;) {
	// Move iterator to next use before the current use is destroyed
	Use *u = &*ui_ret++;
	Instruction *user_inst = dyn_cast<Instruction>(u->getUser()); 
	assert(user_inst);

	DEBUG(errs() <<  "\t\t" << *user_inst << "\n");

	if (StoreInst *st_inst = dyn_cast <StoreInst> (user_inst)) {
	    if (st_inst->getPointerOperand()->getName().count("_gvar_ret") == 1) {
		DEBUG(errs() << "\t\t\t" << st_inst->getPointerOperand()->getName() << "\n");
		continue;
	    }
	}

	Instruction *insert_point = user_inst;

	if (PHINode *phi_inst = dyn_cast<PHINode>(user_inst))
	    insert_point = phi_inst->getIncomingBlock(u->getOperandNo())->getTerminator();

	// Read the global variable
	LoadInst *ret_val = new LoadInst(gvar_ret, "", insert_point);
	// Find the uses of return value and replace them
	u->set(ret_val);
    }
}
