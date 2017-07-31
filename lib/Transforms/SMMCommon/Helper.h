#ifndef __SMM_HELPER_H__
#define __SMM_HELPER_H__

#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Value.h"

#include <unordered_map>
#include <unordered_set>

#define DEFAULT_TRIP_COUNT 100

using namespace llvm;

enum Segment { DATA, HEAP, STACK, UNDEF };

// Check if the specified function is a library function
bool isLibraryFunction(Function *);
// Check if the specified function is introduced by management
bool isManagementFunction(Function *);
// Check if the specified global variable is introduced by management
bool isManagementVariable(GlobalVariable *gvar);
// Get the size of specified type by bytes
uint64_t getTypeSize(const DataLayout *dl, Type * ty);
//Return all the paths iteratively from a graph rooted at the node specified and recursive functions
std::pair<std::vector<std::vector<CallGraphNode::CallRecord *> >, std::unordered_set<CallGraphNode *> > getPaths(CallGraphNode::CallRecord *root);
// Return the possible declarations of the specified value
inline bool isHeapData(Value *val);
std::vector <std::pair<Value *, Segment> > getDeclarations(Value *, std::unordered_map <Function *, std::vector<CallInst *> > &);

#endif
