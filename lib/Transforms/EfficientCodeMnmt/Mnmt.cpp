#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"

#include <unordered_set>

#include "../CodeMnmtHelper/GCCFG.h"
#include "../SMMCommon/Helper.h"


#define DEBUG_TYPE "smmcm"

using namespace llvm;

// Build the wrapper function: retTy c_call_complete(char *caller_lma, char *callee_lma, calleeTy callee_vma, ...)
Function *getOrInsertCCall(CallInst *call_inst) {
    // Get the caller
    Function* caller = call_inst->getParent()->getParent();
    // Get the called function
    Function* callee = call_inst->getCalledFunction();
    Module *mod = caller->getParent();
    LLVMContext &context = mod->getContext();
    IRBuilder <> builder(context);

    FunctionType* calleeTy = NULL;
    Type *retTy = NULL;
    std::vector<Type*> calleeArgTy;
    // Get the type of the called function
    calleeTy = callee->getFunctionType();
    // Get arguments types of the called function (if there are any)
    for (unsigned int i = 0, num = call_inst->getNumArgOperands(); i < num; i++) {
	calleeArgTy.push_back(call_inst->getArgOperand(i)->getType());
    }
    // Get the return type of the called function
    retTy = callee->getReturnType();

    // Create a pointer type to char
    PointerType *ptrTy_int8 = PointerType::get(IntegerType::get(context, 8), 0);
    // Create a pointer type to callee type
    PointerType *calleeTyPtr = PointerType::get(calleeTy, 0);
    // Get the pointer to c_get function
    Function* func_c_get = mod->getFunction("c_get");
    assert(func_c_get);

    Function* func_c_call =  nullptr;

    // Go through all the exsiting wrapper functions and check if there is any one can be used directly
    for (Module::iterator fi = mod->begin(), fe = mod->end(); fi != fe; ++fi) {
	if (fi->getName().count("c_call_complete") == 1) {
	    int num_args_before = 3;
	    FunctionType *fiTy = fi->getFunctionType();
	    // Compare the return types
	    FunctionType *fiCalleeTy = (FunctionType *)(((PointerType *)fiTy->getParamType(num_args_before-1))->getElementType());
	    //DEBUG(dbgs() << *fiCalleeTy->getReturnType() <<"\n");
	    Type *fiCalleeRetTy = fiCalleeTy->getReturnType();
	    if (retTy != fiCalleeRetTy ) {
		continue;
	    }

	    // Compare number of arguments
	    unsigned int fiNumCalleeParams = fiTy->getNumParams() - num_args_before;
	    if(calleeArgTy.size() != fiNumCalleeParams)
		continue;
	    // Compare argument types 
	    unsigned int i = num_args_before;
	    std::vector<Type*>::iterator ai = calleeArgTy.begin(), ae = calleeArgTy.end();
	    while( ai!=ae) {
		if(*ai != fiTy->getParamType(i)) 
		    break;
		ai++;
		i++;
	    }
	    if (ai!=ae)
		continue;
	    // If all the above tests pass, then return the wrapper function
	    func_c_call = fi;
	    return func_c_call;
	}
    }

    // Create a function type for c_call it has not been created for corresponding function type
    if (!func_c_call) {
	std::vector<Type*> callArgs;
	// The first parameter should be a char pointer to caller name
	callArgs.push_back(ptrTy_int8);
	// The second parameter should be a char pointer to callee name
	callArgs.push_back(ptrTy_int8);
	// The third parameter should be a callee function type pointer to callee address
	callArgs.push_back(calleeTyPtr);
	// The following parameters should be the callee arguments if passed in
	for (std::vector<Type*>::iterator ai = calleeArgTy.begin(), ae = calleeArgTy.end(); ai!=ae; ++ai)
	    callArgs.push_back(*ai);
	FunctionType* funcTy = FunctionType::get(
		retTy,
		callArgs,
		false);

	func_c_call = Function::Create(
		funcTy,
		GlobalValue::LinkOnceODRLinkage ,
		"c_call_complete", mod);
    }

    assert(func_c_call);

    // Get arguments for c_call
    Function::arg_iterator ai = func_c_call->arg_begin();
    // Get caller LMA from first argument
    Value* callerLMA = ai++;
    callerLMA->setName("caller_lma");
    // Get callee LMA from second argument
    Value* calleeLMA = ai++;
    calleeLMA->setName("callee_lma");
    // Skip callee type from the third argument (used to tell whether a c_call function can be reused)
    ai++;
    // Get addresses of callee arguments from following arguments if passed in
    std::vector<Value*> calleeArg;
    for (Function::arg_iterator ae = func_c_call->arg_end(); ai!=ae; ai++) {
	static int i = 0;
	Value* arg = ai;
	arg->setName("arg" + std::to_string(i++));
	calleeArg.push_back(arg);
    }

    // Create the entry basic block 
    BasicBlock* c_call_entry = BasicBlock::Create(context, "entry", func_c_call, 0);
    // Set insert point as the end of entry block
    builder.SetInsertPoint(c_call_entry);

    // Create local variables for callee arugments if passed in
    std::vector<AllocaInst*> calleeArgAddr;
    for (std::vector<Type*>::size_type i = 0; i < calleeArgTy.size(); i++) {	
	AllocaInst* arg_addr = builder.CreateAlloca(calleeArgTy[i], nullptr, "callee_arg" + std::to_string(i));
	calleeArgAddr.push_back(arg_addr);
    }

    // Allocate space for return value if its type is not void
    AllocaInst* ret_val;
    if (!retTy->isVoidTy()) {
	ret_val = builder.CreateAlloca(retTy, nullptr, "ret_val");
    }

    // Copy the callee arguments to the local variables if passed in
    for (std::vector<Value*>::size_type i = 0; i < calleeArg.size(); i++) {
	builder.CreateStore(calleeArg[i], calleeArgAddr[i], false);
    }

    // Find out the SPM address for callee
    CallInst* callee_vma_int8 = CallInst::Create(func_c_get, calleeLMA, "callee_vma_int8", c_call_entry);
    // Cast the type of the SPM address to the function type of the callee
    CastInst* callee_vma = cast <CastInst> (builder.CreateBitCast(callee_vma_int8, calleeTyPtr, "callee_vma")); 

    // Read callee arguments and get their values if passed in
    std::vector<Value*> calleeArgVals;
    for (std::vector<AllocaInst*>::iterator ai = calleeArgAddr.begin(), ae = calleeArgAddr.end(); ai != ae; ai++) {
	LoadInst* arg_val = builder.CreateLoad(*ai);
	calleeArgVals.push_back(arg_val);
    }

    // Call the callee
    CallInst* calleeRet;

    // Get return value if its type is not void
    if (!retTy->isVoidTy()) {
	calleeRet = builder.CreateCall(callee_vma, calleeArgVals, "callee_ret_val");
	builder.CreateStore(calleeRet, ret_val, false);
    } else
	calleeRet = builder.CreateCall(callee_vma, calleeArgVals);

    // Ensure the caller is present after the callee returns
    CallInst::Create(func_c_get, callerLMA, "caller_vma", c_call_entry);

    // Read return value and return it if its type is not void
    if (!retTy->isVoidTy()) {
	LoadInst *ld_ret_val = builder.CreateLoad(ret_val);
	ReturnInst::Create(context, ld_ret_val, c_call_entry);
	//builder.CreateRet(ld_ret_val);
    } else {
	ReturnInst::Create(context, c_call_entry);
	//builder.CreateRetVoid();
    }
    return func_c_call;
}

// Build the wrapper function: retTy c_call_callee_only(char *callee_lma, calleeTy callee_vma, ...)
Function *getOrInsertCCall2(CallInst *call_inst) {
    // Get the called function
    Function* callee = call_inst->getCalledFunction();
    Module *mod = call_inst->getParent()->getParent()->getParent();
    LLVMContext &context = mod->getContext();
    IRBuilder <> builder(context);

    FunctionType* calleeTy = NULL;
    Type *retTy = NULL;
    std::vector<Type*>calleeArgTy;
    // Get the type of the called function
    calleeTy = callee->getFunctionType();
    // Get arguments types of the called function (if there are any)
    for (unsigned int i = 0, num = call_inst->getNumArgOperands(); i < num; i++) {
	calleeArgTy.push_back(call_inst->getArgOperand(i)->getType());
    }
    // Get the return type of e_call function
    retTy = callee->getReturnType();

    // Create a pointer type to char
    PointerType *ptrTy_int8 = PointerType::get(IntegerType::get(context, 8), 0);
    // Create a pointer type to callee type
    PointerType *calleeTyPtr = PointerType::get(calleeTy, 0);
    // Get the pointer to c_get function
    Function* func_c_get = mod->getFunction("c_get");
    assert(func_c_get);

    Function* func_c_call =  nullptr;

    // Go through all the exsiting wrapper functions and check if there is any one can be used directly
    for (Module::iterator fi = mod->begin(), fe = mod->end(); fi != fe; ++fi) {
	if (fi->getName().count("c_call_callee_only") == 1) {
	    int num_args_before = 2;
	    FunctionType *fiTy = fi->getFunctionType();
	    // Compare the return types
	    FunctionType *fiCalleeTy = (FunctionType *)(((PointerType *)fiTy->getParamType(num_args_before-1))->getElementType());
	    //DEBUG(dbgs() << *fiCalleeTy->getReturnType() <<"\n");
	    Type *fiCalleeRetTy = fiCalleeTy->getReturnType();
	    if (retTy != fiCalleeRetTy ) {
		continue;
	    }

	    // Compare number of arguments
	    unsigned int fiNumCalleeParams = fiTy->getNumParams() - num_args_before;
	    if(calleeArgTy.size() != fiNumCalleeParams)
		continue;
	    // Compare argument types 
	    unsigned int i = num_args_before;
	    std::vector<Type*>::iterator ai = calleeArgTy.begin(), ae = calleeArgTy.end();
	    while( ai!=ae) {
		if(*ai != fiTy->getParamType(i)) 
		    break;
		ai++;
		i++;
	    }
	    if (ai!=ae)
		continue;
	    // If all the above tests pass, then return the wrapper function
	    func_c_call = fi;
	    return func_c_call;
	}
    } 

    // Create a function type for c_call it has not been created for corresponding function type
    if (!func_c_call) {
	std::vector<Type*> callArgs;
	// The first parameter should be a char pointer to callee name
	callArgs.push_back(ptrTy_int8);
	// The second parameter should be a callee function type pointer to callee address
	callArgs.push_back(calleeTyPtr);
	// The following parameters should be the callee arguments if passed in
	for (std::vector<Type*>::iterator ai = calleeArgTy.begin(), ae = calleeArgTy.end(); ai!=ae; ++ai)
	    callArgs.push_back(*ai);
	FunctionType* funcTy = FunctionType::get(
		retTy,
		callArgs,
		false);

	func_c_call = Function::Create(
		funcTy,
		GlobalValue::LinkOnceODRLinkage ,
		"c_call_callee_only", mod);
    }

    assert(func_c_call);

    // Get arguments for c_call
    Function::arg_iterator ai = func_c_call->arg_begin();
    // Get callee name from first argument
    Value* calleeLMA = ai++;
    calleeLMA->setName("callee_lma");
    // Skip callee type from the third argument (used to tell whether a c_call function can be reused)
    ai++;
    // Get addresses of callee arguments from following arguments if passed in
    std::vector<Value*> calleeArg;
    for (Function::arg_iterator ae = func_c_call->arg_end(); ai!=ae; ai++) {
	static int i = 0;
	Value* arg = ai;
	arg->setName("arg" + std::to_string(i++));
	calleeArg.push_back(arg);
    }

    // Block entry (c_call_entry)
    BasicBlock* c_call_entry = BasicBlock::Create(context, "entry",func_c_call, 0);
    builder.SetInsertPoint(c_call_entry);

    // Allocate space for return value if its type is not void
    AllocaInst* ret_val;
    if (!retTy->isVoidTy()) {
	ret_val = builder.CreateAlloca(retTy, nullptr, "ret_val");
    }

    CallInst* calleeRet;
    // Create local variables for callee arugments if passed in
    std::vector<AllocaInst*> calleeArgAddr;
    for (std::vector<Type*>::size_type i = 0; i < calleeArgTy.size(); i++) {	
	AllocaInst* arg_addr = builder.CreateAlloca(calleeArgTy[i], nullptr, "callee_arg" + std::to_string(i));
	calleeArgAddr.push_back(arg_addr);
    }

    // Copy the callee arguments to the local variables if passed in
    for (std::vector<Value*>::size_type i = 0; i < calleeArg.size(); i++) {
	builder.CreateStore(calleeArg[i], calleeArgAddr[i], false);
    }

    // Find out the SPM address for callee
    CallInst* callee_vma_int8 = builder.CreateCall(func_c_get, calleeLMA, "callee_vma_int8");
    // Cast the type of the SPM address to the function type of the callee
    CastInst* callee_vma = cast <CastInst> (builder.CreateBitCast(callee_vma_int8, calleeTyPtr, "callee_vma")); 

    // Read callee arguments and get their values if passed in
    std::vector<Value*> calleeArgVals;
    for (std::vector<AllocaInst*>::iterator ai = calleeArgAddr.begin(), ae = calleeArgAddr.end(); ai != ae; ai++) {
	LoadInst* arg_val = builder.CreateLoad(*ai);
	calleeArgVals.push_back(arg_val);
    }

    // Get return value if its type is not void
    if (!retTy->isVoidTy()) {
	// Call the callee
	calleeRet = builder.CreateCall(callee_vma, calleeArgVals, "callee_ret_val");
	builder.CreateStore(calleeRet, ret_val, false);
    } else
	calleeRet = builder.CreateCall(callee_vma, calleeArgVals);

    // Read return value and return it if its type is not void
    if (!retTy->isVoidTy()) {
	LoadInst *ld_ret_val = builder.CreateLoad(ret_val);
	builder.CreateRet(ld_ret_val);
    } else {
	builder.CreateRetVoid();
    }
    return func_c_call;
}


// Build the wrapper function: retTy c_call_caller_only(char *caller_lma, calleeTy callee_vma, ...)
Function *getOrInsertCCall3(CallInst *call_inst) {
    // Get the caller
    Function* caller = call_inst->getParent()->getParent();
    // Get the called function
    Function* callee = call_inst->getCalledFunction();
    Module *mod = caller->getParent();
    LLVMContext &context = mod->getContext();
    IRBuilder <> builder(context);

    FunctionType* calleeTy = NULL;
    Type *retTy = NULL;
    std::vector<Type*>calleeArgTy;
    // Get the type of the called function
    calleeTy = callee->getFunctionType();
    // Get arguments types of the called function (if there are any)
    for (unsigned int i = 0, num = call_inst->getNumArgOperands(); i < num; i++) {
	calleeArgTy.push_back(call_inst->getArgOperand(i)->getType());
    }
    // Get the return type of the called function
    retTy = callee->getReturnType();

    // Create a pointer type to char
    PointerType *ptrTy_int8 = PointerType::get(IntegerType::get(context, 8), 0);
    // Create a pointer type to callee type
    PointerType *calleeTyPtr = PointerType::get(calleeTy, 0);
    // Get the pointer to c_get function
    Function* func_c_get = mod->getFunction("c_get");
    assert(func_c_get);

    Function* func_c_call =  nullptr;

    // Go through all the exsiting wrapper functions and check if there is any one can be used directly
    for (Module::iterator fi = mod->begin(), fe = mod->end(); fi != fe; ++fi) {
	if (fi->getName().count("c_call_caller_only") == 1) {
	    int num_args_before = 2;
	    FunctionType *fiTy = fi->getFunctionType();
	    // Compare the return types
	    FunctionType *fiCalleeTy = (FunctionType *)(((PointerType *)fiTy->getParamType(num_args_before-1))->getElementType());
	    //DEBUG(dbgs() << *fiCalleeTy->getReturnType() <<"\n");
	    Type *fiCalleeRetTy = fiCalleeTy->getReturnType();
	    if (retTy != fiCalleeRetTy ) {
		continue;
	    }

	    // Compare number of arguments
	    unsigned int fiNumCalleeParams = fiTy->getNumParams() - num_args_before;
	    if(calleeArgTy.size() != fiNumCalleeParams)
		continue;
	    // Compare argument types 
	    unsigned int i = num_args_before;
	    std::vector<Type*>::iterator ai = calleeArgTy.begin(), ae = calleeArgTy.end();
	    while( ai!=ae) {
		if(*ai != fiTy->getParamType(i)) 
		    break;
		ai++;
		i++;
	    }
	    if (ai!=ae)
		continue;
	    // If all the above tests pass, then return the wrapper function
	    func_c_call = fi;
	    return func_c_call;
	}
    }

    // Create a function type for c_call it has not been created for corresponding function type
    if (!func_c_call) {
	std::vector<Type*> callArgs;
	// The first parameter should be a char pointer to caller name
	callArgs.push_back(ptrTy_int8);
	// The second parameter should be a callee function type pointer to callee address
	callArgs.push_back(calleeTyPtr);
	// The following parameters should be the callee arguments if passed in
	for (std::vector<Type*>::iterator ai = calleeArgTy.begin(), ae = calleeArgTy.end(); ai!=ae; ++ai)
	    callArgs.push_back(*ai);
	FunctionType* funcTy = FunctionType::get(
		retTy,
		callArgs,
		false);

	func_c_call = Function::Create(
		funcTy,
		GlobalValue::LinkOnceODRLinkage ,
		"c_call_caller_only", mod);
    }

    assert(func_c_call);

    // Get arguments for c_call
    Function::arg_iterator ai = func_c_call->arg_begin();
    // Get caller LMA from first argument
    Value* callerLMA = ai++;
    callerLMA->setName("caller_lma");
    // Skip callee type from the third argument (used to tell whether a c_call function can be reused)
    ai++;
    // Get addresses of callee arguments from following arguments if passed in
    std::vector<Value*> calleeArg;
    for (Function::arg_iterator ae = func_c_call->arg_end(); ai!=ae; ai++) {
	static int i = 0;
	Value* arg = ai;
	arg->setName("arg" + std::to_string(i++));
	calleeArg.push_back(arg);
    }

    // Create the entry basic block 
    BasicBlock* c_call_entry = BasicBlock::Create(context, "entry",func_c_call, 0);
    // Set insert point as the end of entry block
    builder.SetInsertPoint(c_call_entry);

    // Create local variables for callee arugments if passed in
    std::vector<AllocaInst*> calleeArgAddr;
    for (std::vector<Type*>::size_type i = 0; i < calleeArgTy.size(); i++) {	
	AllocaInst* arg_addr = builder.CreateAlloca(calleeArgTy[i], nullptr, "callee_arg" + std::to_string(i));
	calleeArgAddr.push_back(arg_addr);
    }

    // Allocate space for return value if its type is not void
    AllocaInst* ret_val;
    if (!retTy->isVoidTy()) {
	ret_val = builder.CreateAlloca(retTy, nullptr, "ret_val");
    }

    // Copy the callee arguments to the local variables if passed in
    for (std::vector<Value*>::size_type i = 0; i < calleeArg.size(); i++) {
	builder.CreateStore(calleeArg[i], calleeArgAddr[i], false);
    }

    // Read callee arguments and get their values if passed in
    std::vector<Value*> calleeArgVals;
    for (std::vector<AllocaInst*>::iterator ai = calleeArgAddr.begin(), ae = calleeArgAddr.end(); ai != ae; ai++) {
	LoadInst* arg_val = builder.CreateLoad(*ai);
	calleeArgVals.push_back(arg_val);
    }

    // Call the callee
    CallInst* calleeRet;

    // Get return value if its type is not void
    if (!retTy->isVoidTy()) {
	calleeRet = builder.CreateCall(callee, calleeArgVals, "callee_ret_val");
	builder.CreateStore(calleeRet, ret_val, false);
    } else
	calleeRet = builder.CreateCall(callee, calleeArgVals);

    // Ensure the caller is present after the callee returns
    builder.CreateCall(func_c_get, callerLMA, "caller_vma");

    // Read return value and return it if its type is not void
    if (!retTy->isVoidTy()) {
	LoadInst *ld_ret_val = builder.CreateLoad(ret_val);
	//ReturnInst::Create(context, ld_ret_val, c_call_entry);
	builder.CreateRet(ld_ret_val);
    } else {
	//ReturnInst::Create(context, c_call_entry);
	builder.CreateRetVoid();
    }
    return func_c_call;
}


