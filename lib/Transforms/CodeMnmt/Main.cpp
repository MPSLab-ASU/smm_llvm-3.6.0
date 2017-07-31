#include "llvm/Pass.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/YAMLTraits.h"

#include <cmath>
#include <deque>
#include <fstream>
#include <iostream>
#include <set>
#include <stack>
#include <string>
#include <utility>
#include <vector>
#include <unordered_set>
#include <unordered_map>

#include "Mnmt.h"
#include "../SMMCommon/Helper.h"

#define DEBUG_TYPE "smmcm"

using namespace llvm;

cl::opt<std::string> map("map", cl::desc("Specify the file that stores the map from overlays (at function granularity) to overlay regions"), cl::value_desc("a string"));

namespace {
    struct CodeManagement : public ModulePass { // Insert code management functions
	static char ID; // Pass identification, replacement for typeid
	CodeManagement() : ModulePass(ID) {}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	    AU.addRequired<LoopInfo>();
	}



	virtual bool runOnModule (Module &mod) {
	    int num_regions;

	    std::vector<Value*> call_args;
	    std::unordered_map <Function *, int> funcOverlay;
	    std::unordered_map <Function *, std::pair <Value *, Value *>> funcLMA;

	    // LLVM context
	    LLVMContext &context = mod.getContext();
	    // IR builder
	    IRBuilder<> builder(context);
	    // Call graph
	    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph(); 

	    // Types
	    IntegerType *ty_int8 = builder.getInt8Ty();

	    // External variables
	    GlobalVariable* gvar_spm_begin = mod.getGlobalVariable("_spm_begin");
	    if (!gvar_spm_begin) 
		gvar_spm_begin = new GlobalVariable(mod, // Module 
			ty_int8,
			false, //isConstant 
			GlobalValue::ExternalLinkage, // Linkage 
			0, // Initializer 
			"_spm_begin");


	    // Functions
	    Function *func_main = mod.getFunction("main");
	    Function *func_smm_main = mod.getFunction("smm_main");
	    assert(func_smm_main);
	    Function* func_c_init_regions = mod.getFunction("c_init_regions");
	    Function* func_c_init_map = mod.getFunction("c_init_map");
	    Function* func_c_get = mod.getFunction("c_get");
	    assert(func_c_get);

	    // Code management related
	    GlobalVariable* gvar_ptr_region_table = mod.getGlobalVariable("_region_table");
	    assert(gvar_ptr_region_table);
	    ConstantInt * const_num_regions = NULL;
	    ConstantInt * const_num_mappings = NULL;
	    std::ifstream ifs;
	    //std::ofstream ofs;
	    std::unordered_set<Function *> calledFuncs;

	    /* Get functions information: begin */
	    ifs.open(map, std::fstream::in);
	    assert(ifs.good());

	    ifs >> num_regions;
	    builder.SetInsertPoint(func_main->getEntryBlock().getFirstNonPHI());
	    while (ifs.good()) {
		int region_id;
		std::string func_name;
		ifs >> func_name >> region_id;
		if (func_name.empty())
		    continue;


		// Ignore white spaces after the last line
		if (func_name != "") {
		    //DEBUG(errs() << "\t" << func_name << " " << region_id << "\n");
		    Function *func;
		    if (func_name == "main")
			func = func_smm_main;
		    else
			func = mod.getFunction(func_name);

		    calledFuncs.insert(func);

		    // Get the overlay ID of this function
		    funcOverlay[func] = region_id;

		    // Create a seperate section for this function and record its load address except for the main function
		    if (func->getSection() != "."+func_name)
			func->setSection("."+func_name);
		    //DEBUG(errs() << fi->getSection() << "\n");

		    GlobalVariable* gvar_load_start = new GlobalVariable(mod,
			    IntegerType::get(context, 8),
			    true, //isConstant
			    GlobalValue::ExternalLinkage,
			    0, // Initializer
			    "__load_start_" + func_name);

		    GlobalVariable* gvar_load_stop = new GlobalVariable(mod,
			    IntegerType::get(context, 8), //Type
			    true, //isConstant
			    GlobalValue::ExternalLinkage, // Linkage
			    0, // Initializer
			    "__load_stop_" + func_name);
		    funcLMA[func] = std::make_pair(gvar_load_start, gvar_load_stop);


		}
	    }

	    ifs.close();

	    /* Get functions information: end */

	    /* Replace calls to user functions with calls to management functions: begin */
	    // Insert code management functions
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		if(CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second)) {
		    Function *caller = cgn->getFunction();
		    // Skip external nodes (inline asm and function pointers)
		    if(!caller)
			continue;
		    // Skip library functions
		    if (isLibraryFunction(caller))
			continue;
		    // Skip code management functions
		    if (isManagementFunction(caller))
			continue;
		    // Skip functions without references
		    if (calledFuncs.find(caller) == calledFuncs.end())
			continue;
		    // Skip main function
		    if (caller == func_main)
			continue;

		    // User-defined caller functions
		    std::string func_name = caller->getName().str();
		    DEBUG(errs() << func_name <<"\n");


		    for (CallGraphNode::iterator cgni = cgn->begin(), cgne = cgn->end(); cgni != cgne; cgni++) {
			CallInst *call_inst = dyn_cast <CallInst> (cgni->first);
			BasicBlock::iterator ii(call_inst);
			CallGraphNode *called_cgn = dyn_cast <CallGraphNode> (cgni->second);
			Function *callee = called_cgn->getFunction();
			assert(call_inst && called_cgn);

			builder.SetInsertPoint(call_inst);

			// Skip external nodes (inline asm and function pointers)
			if (!callee) 
			    continue;
			// Skip calls to management functions
			if(isManagementFunction(callee))
			    continue;

			// If the caller calls an user-defined function
			if (!isLibraryFunction(callee)) { 
			    DEBUG(errs() << "\tcalls " << callee->getName() <<" (U)\n");
			    // Create a wrapper function for callee
			    Function *func_c_call = getOrInsertCCall(call_inst);
			    // Pass arguments to the pointer to the wraper function
			    std::vector<Value*> call_args;

			    Value *callerLMA = funcLMA[caller].first;
			    Value *calleeLMA = funcLMA[callee].first;


			    // Pass caller address with char* type as the first argument
			    call_args.push_back(callerLMA);
			    // Pass callee name as the second argument
			    call_args.push_back(calleeLMA);
			    // Pass callee address as the third argument
			    call_args.push_back(callee);
			    // Pass callee arguments if there are any as the following arguments
			    for (unsigned int i = 0, num = call_inst->getNumArgOperands(); i < num; i++) {
				call_args.push_back(call_inst->getArgOperand(i));
			    }
			    // Create a new call instruction to the wrapper function
			    CallInst* call_c_call = CallInst::Create(func_c_call, call_args);
			    // Replace all the uses of the original call instruction with the new call instruction
			    ReplaceInstWithInst(call_inst->getParent()->getInstList(), ii, call_c_call);
			}
		    }
		}
	    }

	    /* Replace calls to user functions with calls to management functions: end */

	    /* Insert initialization code at smm_main: begin */
	    BasicBlock* main_entry = &func_main->getEntryBlock();
	    builder.SetInsertPoint(main_entry->getFirstNonPHI());
	    const_num_regions = builder.getInt32(num_regions);
	    const_num_mappings = builder.getInt32(funcLMA.size());
	    // Initalize regions
	    builder.CreateCall(func_c_init_regions, const_num_regions, "");
	    // Initialize mappings
	    LoadInst* region_table = builder.CreateLoad(gvar_ptr_region_table);
	    std::vector <Value *> regions;
	    for (int i = 0; i < num_regions; ++i) {
		regions.push_back(builder.CreateGEP(region_table, builder.getInt32(i)));
	    }
	    call_args.clear();
	    call_args.push_back(const_num_mappings);
	    for (auto ii = funcLMA.begin(), ie = funcLMA.end(); ii != ie; ii++) {
		DEBUG(errs() << ii->first->getName() << "->" << ii->second.first->getName() << " " << ii->second.second->getName() << "\n");
		Function *func = ii->first;
		call_args.push_back(ii->second.first);
		call_args.push_back(func);
		call_args.push_back(builder.CreateSub(builder.CreatePtrToInt(ii->second.second, builder.getInt64Ty()), builder.CreatePtrToInt(ii->second.first, builder.getInt64Ty())));
		call_args.push_back(regions[funcOverlay[func]]);
	    }
	    builder.CreateCall(func_c_init_map, call_args);
	    // Get the code of smm_main
	    builder.CreateCall(func_c_get, funcLMA[func_smm_main].first);
	    /* Insert initialization code at smm_main: end */

	    return true;
	}

    };
}

char CodeManagement::ID = 0;
static RegisterPass<CodeManagement> X("smmcm", "Code Management Pass)");
