#ifndef __MNMT_H__
#define __MNMT_H__

#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"

#include <unordered_map>
#include <unordered_set>
#include <vector>


using namespace llvm;

/* Transform begins */

void g2l_instrumentation(Module &, Function *, std::unordered_set<unsigned> &);
void l2g_instrumentation(Module &, CallInst *, std::unordered_set<unsigned> &);
void stack_frame_management_instrumentation (Module &, CallInst *);

/* Transform ends */

#endif
