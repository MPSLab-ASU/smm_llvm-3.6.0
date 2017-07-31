//===- --------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements several methods that are used to extract functions,
// loops, or portions of a module from the rest of the module.
//
//===----------------------------------------------------------------------===//
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
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

#include <fstream>
#include <queue>
#include <tuple>
#include <stack>
#include <unordered_map>
#include <unordered_set>

#include "Mnmt.h"
#include "../SMMCommon/Helper.h"

#define DEBUG_TYPE "smmssm"

using namespace llvm;

cl::opt<std::string> size_constraint("size-constraint", cl::desc("Specify the size of available stack space in SPM"), cl::value_desc("a string"));
cl::opt<std::string> stack_frame_size("stack-frame-size", cl::desc("Specify the file that stores the sizes of stack frames"), cl::value_desc("a string"));

namespace {

    struct StackManagementPass : public ModulePass {
	static char ID; // Pass identification, replacement for typeid

	StackManagementPass() : ModulePass(ID) {
	}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	    AU.addRequired<LoopInfo>();
	}

	virtual bool runOnModule(Module &mod) {
	    LLVMContext &context = mod.getContext();

	    // Pointer Types
	    PointerType* ptrty_int8 = PointerType::get(IntegerType::get(context, 8), 0);
	    PointerType* ptrty_ptrint8 = PointerType::get(ptrty_int8, 0);
	    // Function Types
	    std::vector<Type*> call_args;
	    call_args.push_back(ptrty_ptrint8);
	    FunctionType* functy_inline_asm = FunctionType::get(
		    Type::getVoidTy(context), // Results
		    call_args, // Params
		    false); //isVarArg

	    // External Variables
	    GlobalVariable* spm_stack_end = new GlobalVariable(mod, // Module
		    IntegerType::get(context, 8), //Type
		    false, //isConstant
		    GlobalValue::ExternalLinkage, // Linkage
		    0, // Initializer
		    "_spm_stack_end");

	    // Global Variables
	    GlobalVariable* mem_stack_base = mod.getGlobalVariable("_mem_stack_base");
	    GlobalVariable* spm_stack_base = mod.getGlobalVariable("_spm_stack_base");
	    //GlobalVariable* spm_depth = mod.getGlobalVariable("_stack_depth");
	    //GlobalVariable* stack = mod.getGlobalVariable("_stack");

	    // Functions
	    Function *func_main = mod.getFunction("main");
	    Function *func_smm_main = mod.getFunction("smm_main");
	    assert(func_smm_main);

	    Function *func_sstore = mod.getFunction("_sstore");

	    // Inline Assembly
	    InlineAsm *func_putSP = InlineAsm::get(functy_inline_asm, "mov $0, %rsp;", "*m,~{rsp},~{dirflag},~{fpsr},~{flags}",true);
	    InlineAsm *func_getSP = InlineAsm::get(functy_inline_asm, "mov %rsp, $0;", "=*m,~{dirflag},~{fpsr},~{flags}",true);

	    // Call Graph 
	    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph(); // call graph
	    CallGraphNode *cgn_smm_main = cg[func_smm_main];
	    CallGraphNode::CallRecord *root;
	    std::vector<std::vector<CallGraphNode::CallRecord *> > paths;
	    std::unordered_set <CallGraphNode *> undecidable_cgns;

	    //Step 0: extract all the paths from original call graph

	    size_t sizeConstraint = std::stoul(size_constraint);
	    // Initialize root node by smm_main function
	    for (CallGraphNode::iterator cgni = cg.begin()->second->begin(), cgne = cg.begin()->second->end(); cgni != cgne; cgni++) {
		if (cgni->second == cgn_smm_main) {
		    root = &*cgni;
		    break;
		}
	    }
	    assert(CallGraphNode::iterator(root) != cg.begin()->second->end());

	    // Extarct all the paths from the root
	    auto res = getPaths(root);
	    paths = res.first;
	    undecidable_cgns = res.second; 

	    DEBUG(dbgs() <<  "Extract paths {\n");
	    // Print out all the paths
	    for (size_t i = 0; i < paths.size(); i++) {
		for (size_t j = 0; j < paths[i].size(); j++) {
		    if (paths[i][j]->second->getFunction()) {
			DEBUG(dbgs() << "\t" << paths[i][j]->first << " " << paths[i][j]->second->getFunction()->getName() << "\t");
		    } else {
			DEBUG(dbgs() << "\t" << paths[i][j]->first << " " << "externalNode" << "\t");
		    }
		}
		DEBUG(dbgs() << "\n");
	    }
	    DEBUG(dbgs() << "}\n\n");

	    // Step 1: get SSMD cuts

	    std::unordered_map <Function *, size_t> stackFrameSizes;
	    std::unordered_map <unsigned, std::vector <std::pair<unsigned, std::string> > > cuts;
	    std::ifstream ifs;
	    // Obtain stack frame sizes
	    ifs.open(stack_frame_size, std::fstream::in);
	    assert(ifs.good());
	    while (ifs.good()) {
		std::string func_name;
		size_t frame_size;
		ifs >> func_name >> frame_size;
		// Ignore white spaces after the last line
		if (func_name != "") {
		    DEBUG(errs() << "\t" << func_name << " " << frame_size << "\n");
		    if (func_name == "main") {
			func_name = "smm_main";
		    }
		    stackFrameSizes[mod.getFunction(func_name)] = frame_size;
		}
	    }
	    ifs.close();

	    // Decides locations of cuts
	    bool foundSolution = true;
	    // Try to avoid cuts in loops
	    for (size_t i = 0; i < paths.size(); i++) {
		size_t sum  = stackFrameSizes[func_smm_main];
		for (size_t j = 1; j < paths[i].size(); j++) {
		    Function *func = paths[i][j]->second->getFunction();
		    std::string func_name = func->getName();
		    // Found a candidate call in the current path to insert frame management functions
		    if (sum + stackFrameSizes[func] > sizeConstraint) {
			// Recrively traverse back until finding a call outside of loops or fail
			while (CallInst *funcCall = dyn_cast <CallInst> (paths[i][j]->first)) {
			    BasicBlock * bb = funcCall->getParent();
			    Function *caller = bb->getParent();
			    LoopInfo &lpi = getAnalysis<LoopInfo>(*caller);
			    // Go back to the last call in the current path until fail
			    if (lpi.getLoopFor(bb)) {
				--j; 
				if ((cuts[i].empty() && j == 0) || (!cuts[i].empty() && j == cuts[i].back().first) ) {
				    foundSolution = false;
				    //dbgs() << "cut in a loop when " << caller->getName() << " calls " << funcCall->getCalledFunction()->getName() << "\n";
				    break;
				}
				else {
				    //cuts[i].push_back( std::make_pair(j, paths[i][j]->second->getFunction()->getName()) );
				    //sum = 0;
				    continue;
				}
			    }
			    // Found a call not in loops
			    else {
				cuts[i].push_back( std::make_pair(j, paths[i][j]->second->getFunction()->getName()) );
				sum = 0;
				break;
			    }  

			}
			// Check if the search fails
			if (foundSolution == false)
			    break;
		    }
		    // Enough room left, skip to the next call int the current path
		    else 
			sum += stackFrameSizes[func];
		}
		if (foundSolution == false)
		    break;
	    }
	    // If cuts in loops are not avoidable, fall back to the default way of grouping
	    if (!foundSolution) {
		cuts.clear();
		for (size_t i = 0; i < paths.size(); i++) {
		    size_t sum  = stackFrameSizes[func_smm_main];
		    for (size_t j = 1; j < paths[i].size(); j++) {
			Function *func = paths[i][j]->second->getFunction();
			std::string func_name = func->getName();
			if (sum + stackFrameSizes[func] > sizeConstraint) {
			    cuts[i].push_back( std::make_pair(j, func_name) );
			    sum = 0;
			} else 
			    sum += stackFrameSizes[func];
		    }
		}
	    }

	    // Sort cuts acoording to paths
	    for (auto cutsi = cuts.begin(), cutse = cuts.end(); cutsi != cutse; cutsi++) {
		std::sort(cutsi->second.begin(), cutsi->second.end());
		DEBUG(dbgs() << "\tpath " << cutsi->first << " : ");
		for (size_t i = 0; i < cutsi->second.size(); i++) {
		    DEBUG(dbgs() << cutsi->second[i].first << " " << cutsi->second[i].second << "  ");
		}
		DEBUG(dbgs() << "\n");
	    }


	    // Step 2: Insert g2l function calls

	    DEBUG(dbgs() << "Pointer management functions instrumentation {\n");
	    DEBUG(dbgs() << "Inserting g2l functions... {\n");
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		CallGraphNode *cgn = cgi->second;
		Function *fi = cgn->getFunction();
		// Skip external nodes
		if (!fi)
		    continue;
		// Skip library functions
		if (isLibraryFunction(fi))
		    continue;
		// Skip management functions
		if (isManagementFunction(fi))
		    continue;
		// Skip main function
		if (fi == func_main)
		    continue;

		// Process user-defined functions
		g2l_pointer_management_instrumentation(mod, cgn);
	    }
	    DEBUG(dbgs() << "}\n");

	    // Step 3: Insert l2g functions

	    DEBUG(dbgs() << "Inserting l2g functions: {\n");
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second); 
		Function *fi = cgn->getFunction();
		// Skip external nodes
		if (!fi)
		    continue;
		DEBUG(dbgs() << "\t" << fi->getName() << "\n");
		// Skip library functions
		if (isLibraryFunction(fi))
		    continue;
		// Skip management functions
		if (isManagementFunction(fi))
		    continue;
		// Skip main function
		if (fi == func_main)
		    continue;
		// Process user-defined functions
		l2g_pointer_management_instrumentation(mod, cgn);
	    }
	    DEBUG(dbgs() << "}");
	    DEBUG(dbgs() << "}\n\n\n");
	    DEBUG(dbgs() << "Inserting management functions according to SSDM cuts: {\n");

	    // Step 4.0: Insert stack fame management functions

	    // Decide the insertion points of stack frame management function according to SSDM output
	    std::unordered_set <CallInst *> stack_frame_management_insert_pts;
	    for (auto cuti = cuts.begin(), cute = cuts.end(); cuti != cute; cuti++) {
		for (size_t vi = 0; vi < cuti->second.size(); vi++) {
		    unsigned i, j;
		    std::string func_name;
		    i = cuti->first;
		    j = cuti->second[vi].first;
		    func_name = cuti->second[vi].second;
		    assert(paths[i][j]->first && paths[i][j]->second);
		    CallInst *call_inst = dyn_cast<CallInst> (paths[i][j]->first);
		    assert(call_inst);
		    stack_frame_management_insert_pts.insert(call_inst);
		}
	    }
	    // Insert stack frame management functions accroding to SSDM cuts
	    for (auto si = stack_frame_management_insert_pts.begin(), se = stack_frame_management_insert_pts.end(); si != se; si++) {
		CallInst *call_inst = *si;
		DEBUG(dbgs() << call_inst->getParent()->getParent()->getName() << ":" << call_inst->getParent()->getName() <<  " -> " << call_inst->getCalledFunction()->getName() << "\n");
		// Insert stack frame management functions
		stack_frame_management_instrumentation(mod, call_inst);
	    }
	    DEBUG(dbgs() << "}\n");

	    // Step 4.1: Insert frame management functions at self-recursive calls

	    DEBUG(dbgs() << "Inserting frame management functions around recursive calls... {\n");
	    for (std::unordered_set <CallGraphNode *>::iterator si = undecidable_cgns.begin(), se = undecidable_cgns.end(); si != se; si++) {
		CallGraphNode * cgn = *si;
		// Skip external nodes
		if (!cgn->getFunction())
		    continue;
		DEBUG(dbgs() << cgn->getFunction()->getName() << "\n");
		for (CallGraphNode::iterator cgni = cgn->begin(), cgne = cgn->end(); cgni != cgne; cgni++) {
		    // Skip non-self-recursive calls
		    if (cgni->second != cgn)
			continue;
		    CallInst *call_inst = dyn_cast<CallInst> (cgni->first);
		    assert(call_inst);

		    // Check if stack frame management functions have been inserted
		    BasicBlock::iterator ii(call_inst);
		    BasicBlock::iterator pos = ii;
		    long k = 0;
		    do {
			if (pos == ii->getParent()->begin())
			    break;
			pos--;
			k++;
		    } while(k < 2);

		    if (k >= 2) {
			CallInst *call_inst = dyn_cast<CallInst>(pos);
			if (call_inst && call_inst->getCalledFunction() == func_sstore)
			    continue;
		    }
		    // Insert stack frame management functions
		    stack_frame_management_instrumentation(mod, call_inst);
		}
	    }

	    DEBUG(dbgs() << "}\n");

	    // Step 5: Insert starting and ending code in main function, which is now a wrapper function of the real main function (smm_main)

	    BasicBlock *entry_block = &func_main->getEntryBlock();
	    IRBuilder<> builder(entry_block);
	    for (BasicBlock::iterator ii = entry_block->begin(), ie = entry_block->end(); ii != ie; ii++) {
		Instruction *inst  = &*ii;
		if (CallInst *call_inst = dyn_cast<CallInst>(inst)) {
		    Function *callee = call_inst->getCalledFunction();
		    // Find the call to smm_main
		    if (callee == func_smm_main) {
			// Before the call
			builder.SetInsertPoint(&*ii);
			builder.CreateCall(func_getSP, mem_stack_base);
			builder.CreateStore(spm_stack_end, spm_stack_base);
			builder.CreateCall(func_putSP, spm_stack_base);
			// After the call
			++ii;
			builder.SetInsertPoint(&*ii);
			builder.CreateCall(func_putSP, mem_stack_base); 
			// Exit the loop
			break;
		    }

		}
	    }
	    return true;
	}
    };
}

char StackManagementPass::ID = 0; //Id the pass.
static RegisterPass<StackManagementPass> X("smmssm", "Smart Stack Management Pass"); //Register the pass.

