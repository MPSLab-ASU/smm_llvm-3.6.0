#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/Support/Debug.h"

#include <unordered_map>
#include <vector>
#include <utility>

#include "MemoryAllocator.h"

using namespace llvm;

#define DEBUG_TYPE "smmeam"

//extern unsigned int allocated_size; 

MemoryAllocator spm_array_allocator;
MemoryAllocator spm_global_allocator;

MemoryAllocator::MemoryAllocator() {
    base = NULL;
    pos = 0;
}

void MemoryAllocator::resetPos() {
    pos = 0;
}

size_t MemoryAllocator::getPos() {
    return pos;
}

void MemoryAllocator::setBase(Constant *mem_base) {
    base = mem_base;
}

Constant *MemoryAllocator::allocate(size_t size) {
    LLVMContext &context = getGlobalContext();
    IRBuilder <> builder(context);
    ConstantInt* idx = builder.getInt64(this->pos);
    this->pos += size;
    return cast <Constant> (builder.CreateGEP(this->base, idx));
}

Constant *MemoryAllocator::allocateInBound(size_t size, size_t end) {
    LLVMContext &context = getGlobalContext();
    IRBuilder <> builder(context);
    ConstantInt* idx = builder.getInt64(this->pos);
    if (pos + size > end) {
	return NULL;
    }
    pos += size;
    return cast <Constant> (builder.CreateGEP(this->base, idx));
}
