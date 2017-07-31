#ifndef __MNMT_H__
#define __MNMT_H__

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Value.h"

#include <tuple>
#include <unordered_set>

using namespace llvm;

/* Misc */

// Get the size of data loaded or stored by the memory instruction
size_t getMemReqSize(Instruction *inst);

// Create a DMA call at the specified insertion point
void createDMACall(Module &mod, Value *spm_addr, Value *mem_addr, Value *size, int dir, Instruction *insert_pt);

/* Data Flow */

// Find out the innermost loops contained by the specified loop
std::unordered_set < BasicBlock *> getInnermostLoops(Loop * loop);

// Get the array accesses of the specifed loop
//std::unordered_map <Value*, std::map < User *, std::unordered_set <Instruction *> > >  getArrayAccesses(Loop *loop);
std::unordered_map <Value*, std::map < std::pair<User *, unsigned int>, std::unordered_set <Instruction *> > >  getArrayAccesses(Loop *loop);

/* Control Flow */

// Return true if the loop can be tiled by our technique, and preprocess the specified loop if needed so the subsequent analysis and transformation become easier and return true. Otherwise, return false
bool preprocess(Loop *loop);

// Tile the specifled loop with the specified tile size
std::tuple < PHINode *, BasicBlock *, BasicBlock *, Value *> createLoopTiling(Loop *loop, size_t tile_size);

#endif
