#ifndef __MNMT_H__
#define __MNMT_H__

#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"

using namespace llvm;

// Build the wrapper function: retTy c_call_complete(char *callerName, char *calleeName, calleeTy calleeAddr, ...)
Function *getOrInsertCCall(CallInst *call_inst); 

// Build the wrapper function: retTy c_call_callee_only(char *calleeName, calleeTy calleeAddr, ...)
Function *getOrInsertCCall2(CallInst *call_inst);


// Build the wrapper function: retTy c_call_complete(char *callerName, char *calleeName, calleeTy calleeAddr, ...)
Function *getOrInsertCCall3(CallInst *call_inst);

#endif
