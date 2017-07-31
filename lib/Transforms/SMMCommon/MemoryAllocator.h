#ifndef __MEMORYALLOCATOR_H__
#define __MEMORYALLOCATOR_H__

#include "llvm/IR/Constant.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"

#include <unordered_map>

using namespace llvm;

enum MemUnit {LocalSPM, RemoteSPM, DRAM};

class MemoryAllocator {
    public:
	MemoryAllocator();
	void resetPos();
	size_t getPos();
	void setBase(Constant *mem_base);
	Constant *allocate(size_t size);
    protected:
	Constant *base; // Base of memory region
	size_t pos; // Pointer to the next free space
};

extern MemoryAllocator heap_allocator;

#endif
