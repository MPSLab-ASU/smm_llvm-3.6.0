#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/Debug.h"

#include <queue>
#include <stack>
#include <unordered_set>

#include "Helper.h"


using namespace llvm;

// Checks whether a function is a library function (including intrinsic functions)
bool isLibraryFunction(Function *func) {
    return (func->isDeclaration() || func->getName().count("_allocate") == 1); 
} 

// Check if a function is any management function	
bool isManagementFunction(Function *func) {
    // common
    if (func->getName().count("dma") ==1)
	return true;
    // code
    if (func->getName().count("c_get") ==1)
	return true;
    if (func->getName().count("c_call") ==1)
	return true;
    if (func->getName().count("c_init") ==1)
	return true;
    // stack frame
    if (func->getName().count("_sstore") ==1)
	return true;
    if (func->getName().count("_sload") ==1)
	return true;
    // stack pointer
    if (func->getName().count("_g2l") ==1)
	return true;
    if (func->getName().count("_l2g") ==1)
	return true;
    if (func->getName().count("_ptr_wr") == 1)
	return true;
    // heap
    if (func->getName().count("_heap_size") == 1)
	return true;

    return false;
}

// Check if a global variable is used by mangagement    
bool isManagementVariable(GlobalVariable *gvar) {
    // common
    if (gvar->getName().count("_spm_") ==1)
	return true;
    if (gvar->getName().count("_cacheable_") ==1)
	return true;
    // stack 
    if (gvar->getName() == "_spm_stack_base")
	return true;
    if (gvar->getName() == "_mem_stack_base")
	return true;
    if (gvar->getName() == "_mem_stack_depth")
	return true;
    if (gvar->getName() == "_mem_stack")
	return true;
    if (gvar->getName() == "_stack_pointer")
	return true;
    if (gvar->getName() == "gaddr")
	return true;
    if (gvar->getName() == "laddr")
	return true;
    if (gvar->getName().count("_gvar_ret") ==1)
	return true;
    // code
    if (gvar->getName() == "_region_table")
	return true;
    /*
	*/
    if (gvar->getName() == "region_table_size")
	return true;
    if (gvar->getName() == "_mapping_table")
	return true;
    if (gvar->getName() == "mapping_table_size")
	return true;
    if (gvar->getName().count("__load_start_") ==1)
	return true;
    if (gvar->getName().count("__load_stop_") ==1)
	return true;
    if (gvar->getName().count(".name") ==1)
	return true;

    // heap
    if (gvar->getName().count("_noncacheable") ==1)
	return true;
     if (gvar->getName() == "_pos")
	return true;

    return false;
}

// Get the size of specified type by bytes
uint64_t getTypeSize(const DataLayout *dl, Type * ty) {
    return (uint64_t)ceil((double)(dl->getTypeSizeInBits(ty))/8);
}

//Return all the paths iteratively from a graph rooted at the node specified and recursive functions
std::pair<std::vector<std::vector<CallGraphNode::CallRecord *> >, std::unordered_set<CallGraphNode *> > getPaths(CallGraphNode::CallRecord *root) {
    unsigned int current_path_sel = 0; // This number always leads to next node of path that is going to be traversed
    unsigned int next_path_sel = 0; // This number always leads to the leftmost path that has not been traversed
    std::vector<std::vector<CallGraphNode::CallRecord *> > paths; // Used to keep the result
    std::unordered_set <CallGraphNode *> undecidable_cgns; // Used to keep undecidable functions
    std::queue <CallGraphNode::CallRecord *> current_path; // Used to keep a record of current path
    std::stack < std::pair< std::queue <CallGraphNode::CallRecord *>, unsigned int > > next_path; // Used to keep a record of paths that has not been completely traversed, the first element of each pair saves the nodes that have been visited, and second element indicates the next node to visit

    // Check on validity of root node
    if ((root == NULL || root->second == NULL) ) {
	errs() << "Try to generate paths for an empty graph!\n";
	exit(-1);
    }

    // Initialize the call stack
    current_path.push(root);
    int counter = 0; // This counter is used to stop the loop in case of mutual recurrsion is present
    int mutual_recursion_threshold = 500;
    while(!current_path.empty() && counter++ < mutual_recursion_threshold) { 
	// Pick up a node to visit
	CallGraphNode::CallRecord *v = current_path.back(); 

	bool only_recursive_edges = false;

	// Check if a node has only self-recursive edges
	if(v->second->size() > 0) {
	    unsigned int i;
	    for (i = 0; i < v->second->size(); i++) {
		if ((*v->second)[i] != v->second) {
		    break;
		}
	    }
	    if( i >= v->second->size())
		only_recursive_edges = true;
	}

	// Deal with endpoints - library function calls, leaf nodes, nodes with only recursive edges
	if ( (v->second->getFunction() && isLibraryFunction(v->second->getFunction())) || v->second->size() == 0 || only_recursive_edges) {
	    std::vector<CallGraphNode::CallRecord *> path;
	    counter = 0;
	    // Add current path to result if the endpoint is not an inline asm
	    bool is_valid_path = true;
	    if (current_path.back()->first) {
		CallInst *call_inst = dyn_cast<CallInst>(v->first);
		assert(call_inst);
		if (call_inst->isInlineAsm())
		    is_valid_path = false;
		
	    }
	    if (is_valid_path) {
		while(!current_path.empty()) {
		    CallGraphNode::CallRecord *call_record = current_path.front();
		    if(call_record->second->getFunction() && !isLibraryFunction(call_record->second->getFunction()))
			path.push_back(call_record);
		    current_path.pop();
		}
		if (path.size() > 1)
		    paths.push_back(path);

		// Keep a record if the the node is self-recursive or external
		if (only_recursive_edges || !v->second->getFunction()) {
		    undecidable_cgns.insert(v->second);
		}
	    }
	    // Go to next path that has not been completely travsed
	    if (!next_path.empty()) { 
		auto temp = next_path.top();
		next_path.pop();
		// Restore nodes that have been visited on this path
		current_path = temp.first;
		// Restore the next node to visit
		current_path_sel = temp.second;
	    }
	    // Finish current iteration
	    continue;
	}

	// If the node being visited is not an endpoint
	bool is_recursive = false;
	// Find the first non-recursursive edge of the node
	while ( current_path_sel < v->second->size()) { 
	    // Skip recursive edges
	    if ((*v->second)[current_path_sel] == v->second) {
		//undecidable_cgns.insert(v->second);
		is_recursive = true;
		current_path_sel++; 
	    }
	    else {
		break;
	    }
	}
	next_path_sel = current_path_sel + 1;

	// Decide next path to explore if there are any
	while ( next_path_sel < v->second->size()) { 
	    // Skip self-recursive edges
	    if ( (*v->second)[next_path_sel] == v->second ) {
		//undecidable_cgns.insert(v->second);
		is_recursive = true;
		next_path_sel++;
	    }
	    else { 
		// Record the next path to explore
		next_path.push(std::make_pair(current_path, next_path_sel));
		break;
	    }
	}
	//Keep a record of the found recursive node 
	if (is_recursive)
	    undecidable_cgns.insert(v->second);

	//Add selected node to current path
	unsigned int i = 0; 
	CallGraphNode::iterator cgni = v->second->begin();
	do {
	    if (i == current_path_sel) {
		current_path.push(&*cgni);
		break;
	    }
	    i++;
	    cgni++;
	} while (i < v->second->size());
	// Reset selector of next node to visit in current path
	current_path_sel = 0;
    }
    // Check the presence of mutual recursion
    if (counter >= mutual_recursion_threshold) {
	errs() << "Too many iterations, possible presence of mutual recursion\n";
	exit(-1);
    }

    return std::make_pair(paths, undecidable_cgns);
}

// Check if the specified value is in heap
inline bool isHeapData(Value *val) {
    if (CallInst *call_inst = dyn_cast<CallInst>(val))
	if (call_inst->getCalledFunction()->getName() == "malloc")
	    return true;
    return false;
}
// Return all the declarations and the specified value
std::vector <std::pair<Value *, Segment> > getDeclarations(Value *val, std::unordered_map <Function *, std::vector<CallInst *> > &call_sites) {
    static std::unordered_set <Value *> def_stack;
    std::vector <std::pair<Value *, Segment> > res;
    def_stack.insert(val);

    if(def_stack.size() > 100)
	exit(-1);

    if (ConstantExpr *const_expr = dyn_cast<ConstantExpr>(val)) {
	//inst = const_expr->getAsInstruction();
	val = const_expr->getOperand(0);
    }

    if (dyn_cast<GlobalVariable>(val) || val->getName() == "argv") { 
	// The Value uses global data
	res.push_back(std::make_pair(val, DATA));
    } else if (isHeapData(val)) { 
	// The Value uses heap data
	res.push_back(std::make_pair(val, HEAP));
    } else if (Argument *arg = dyn_cast<Argument>(val)) { // The value is an argument
	// Get the function that contains the argument
	Function* callee = arg->getParent();
	// Go through all the references of the function and recursively find the definitions of the argument value of interest
	for (size_t i = 0; i < call_sites[callee].size(); i++) {
	    CallInst *call_inst = call_sites[callee][i];
	    Value *call_arg = call_inst->getArgOperand(arg->getArgNo());
	    // Skip back edges
	    if (def_stack.find(call_arg) == def_stack.end()) {
		std::vector <std::pair<Value *, Segment >> sub_res = getDeclarations(call_arg, call_sites);
		for (size_t j = 0; j < sub_res.size(); j++)
		    res.push_back(sub_res[j]);
	    }
	}
    } else { 

	// Check if the Value is a function pointer
	if( PointerType *ptr_ty = dyn_cast<PointerType>(val->getType())) {
	    if (ptr_ty->getElementType()->isFunctionTy()) {
		res.push_back(std::make_pair(val, HEAP));
		return res;
	    }
	}
	// Preprocess the value
	Instruction *inst = dyn_cast <Instruction> (val);
	assert(inst);

	std::vector <std::pair<Value *, Segment >> sub_res;
	switch (inst->getOpcode()) {
	    case Instruction::Alloca: 
		// The Value specified uses stack variable
		res.push_back(std::make_pair(val, STACK));
		break;
	    case Instruction::Call:
		//The rationale is function call should only return pointers to heap or global data
		res.push_back(std::make_pair(val, HEAP));
		break;
	    case Instruction::BitCast:
	    case Instruction::GetElementPtr:
	    case Instruction::Load:
		// Ignore back edges
		if (def_stack.find(inst->getOperand(0)) == def_stack.end()) {
		    sub_res = getDeclarations(inst->getOperand(0), call_sites);
		    for (size_t j = 0; j < sub_res.size(); j++)
			res.push_back(sub_res[j]);
		}
		break;
	    case Instruction::Select: 
		{
		    SelectInst* select_inst = dyn_cast<SelectInst> (inst);
		    Value* true_branch = select_inst->getTrueValue();
		    Value * false_branch = select_inst->getFalseValue(); 
		    // Skip back edges
		    if (def_stack.find(true_branch) == def_stack.end()) {
			sub_res = getDeclarations(true_branch, call_sites);
			for (size_t j = 0; j < sub_res.size(); j++)
			    res.push_back(sub_res[j]);
		    }
		    // Skip back edges
		    if (def_stack.find(false_branch) == def_stack.end()) {
			sub_res = getDeclarations(false_branch, call_sites);
			for (size_t j = 0; j < sub_res.size(); j++)
			    res.push_back(sub_res[j]);
		    }
		}
		break;
	    case Instruction::PHI: 
		{
		    PHINode *phi_inst = dyn_cast<PHINode>(inst);
		    for (unsigned i = 0; i < phi_inst->getNumIncomingValues(); i++) {
			// Skip back edges
			if (def_stack.find(phi_inst->getIncomingValue(i)) == def_stack.end()) {
			    sub_res = getDeclarations(phi_inst->getIncomingValue(i), call_sites);
			    for (size_t j = 0; j < sub_res.size(); j++)
				res.push_back(sub_res[j]);
			}
		    }
		}
		break;
	    default:
		res.push_back(std::make_pair(val, UNDEF));
	}
    }
    def_stack.erase(val);
    return res;
}
