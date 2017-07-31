#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/Debug.h"

#include <fstream>
#include <unordered_set>

#include "Mnmt.h"
#include "../CodeMnmtHelper/GCCFG.h"
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
	    AU.addRequired<DominatorTreeWrapperPass>();
	    AU.addRequired<LoopInfo>();
	}

	DominatorTree &getDominatorTree(Function *func) {
	    assert(func);
	    return getAnalysis<DominatorTreeWrapperPass>(*func).getDomTree();
	}


	virtual bool runOnModule (Module &mod) {
	    int num_regions;

	    //std::unordered_map <Function *, Value *> funcNameStr;
	    std::unordered_map <Function *, int> funcOverlay;
	    std::unordered_map <Function *, std::pair <Value *, Value *>> funcLMA;

	    // LLVM context
	    LLVMContext &context = mod.getContext();
	    // IR builder
	    IRBuilder<> builder(context);
	    // Call graph
	    //CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph(); 

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
	    ConstantInt * const_num_overlayss = NULL;
	    std::ifstream ifs;
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

		    // Create a global string of this function name
		    //funcNameStr[func] = builder.CreateGlobalStringPtr(func_name, func_name +".name");

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
	    // Find insert points
	    GCCFG gccfg(this);
	    gccfg.analyze(map);
	    analysisResult = gccfg.getAnalysisResult();

	    // Deal with calls that are not categorized as first-miss
	    for (auto ii = analysisResult.begin(), ie = analysisResult.end(); ii != ie; ++ii) {
		CallInst *call_inst = ii->first;
		BasicBlock::iterator it(call_inst);
		AnalysisResult calleeAnalysis = ii->second.first;
		AnalysisResult callerAnalysis = ii->second.second;
		BasicBlock *bb = call_inst->getParent();
		Function *caller = bb->getParent();
		Function *callee = call_inst->getCalledFunction();

		assert(bb && caller && callee);

		assert(calledFuncs.find(caller) != calledFuncs.end());


		// IRBuilder::SetInsertPoint must be called before builder can be used(?)
		builder.SetInsertPoint(call_inst);
		Value *callerLMA = funcLMA[caller].first;
		Value *calleeLMA = funcLMA[callee].first;
		

		assert(callerAnalysis != FirstMiss); // For caller, it should be either Uncategorized or AlwaysHit


		//DEBUG(errs() << caller->getName() << "\n");
		//DEBUG(errs() << "\tcalls " << callee->getName() <<" (U)\n");
		//DEBUG(std::cerr << "\t\t" <<calleeAnalysis << " " << callerAnalysis << "\n");


		// Check if first-miss function calls are in any loop
		if (calleeAnalysis ==  FirstMiss) {
		    LoopInfo &lpi = getAnalysis<LoopInfo>(*caller);
		    Loop *lp = lpi.getLoopFor(bb);

		    assert(lp);
		}

		if (calleeAnalysis == AlwaysHit) {
		    if (callerAnalysis == AlwaysHit) {
			continue;
		    } else {
			// Ensure the caller is present after the callee returns

			//DEBUG(errs() << "\tcalls " << callee->getName() <<" (U)\n");
			// Create a wrapper function for callee
			Function *func_c_call = getOrInsertCCall3(call_inst);
			// Pass arguments to the pointer to the wraper function
			std::vector<Value*> callArgs;

			// Pass caller name with char* type as the first argument
			callArgs.push_back(callerLMA);
			// Pass callee address
			callArgs.push_back(callee);
			// Pass callee arguments if there are any as the following arguments
			for (unsigned int i = 0, num = call_inst->getNumArgOperands(); i < num; i++) {
			    callArgs.push_back(call_inst->getArgOperand(i));
			}
			// Create a new call instruction to the wrapper function
			CallInst* call_c_call = CallInst::Create(func_c_call, callArgs);
			// Replace all the uses of the original call instruction with the new call instruction
			ReplaceInstWithInst(call_inst->getParent()->getInstList(), it, call_c_call);
		    }
		} else if (calleeAnalysis == Uncategorized) {
		    // Deal with the case when caller function are categorized as AlwaysHit
		    if (callerAnalysis == AlwaysHit) {
			//DEBUG(errs() << "\tcalls " << callee->getName() <<" (U)\n");
			// Create a wrapper function for callee
			Function *func_c_call = getOrInsertCCall2(call_inst);
			// Pass arguments to the pointer to the wraper function
			std::vector<Value*> callArgs;
			// Pass callee LMA as the second argument
			callArgs.push_back(calleeLMA);
			// Pass callee address
			callArgs.push_back(callee);
			// Pass callee arguments if there are any as the following arguments
			for (unsigned int i = 0, num = call_inst->getNumArgOperands(); i < num; i++) {
			    callArgs.push_back(call_inst->getArgOperand(i));
			}
			// Create a new call instruction to the wrapper function
			CallInst* call_c_call = CallInst::Create(func_c_call, callArgs);
			// Replace all the uses of the original call instruction with the new call instruction
			ReplaceInstWithInst(call_inst->getParent()->getInstList(), it, call_c_call);
		    } else {
			//DEBUG(errs() << "\tcalls " << callee->getName() <<" (U)\n");
			// Create a wrapper function for callee
			Function *func_c_call = getOrInsertCCall(call_inst);
			// Pass arguments to the pointer to the wraper function
			std::vector<Value*> callArgs;

			// Pass caller name with char* type as the first argument
			callArgs.push_back(callerLMA);
			// Pass callee name as the second argument
			callArgs.push_back(calleeLMA);
			// Pass callee address
			callArgs.push_back(callee);
			// Pass callee arguments if there are any as the following arguments
			for (unsigned int i = 0, num = call_inst->getNumArgOperands(); i < num; i++) {
			    callArgs.push_back(call_inst->getArgOperand(i));
			}
			// Create a new call instruction to the wrapper function
			CallInst* call_c_call = CallInst::Create(func_c_call, callArgs);
			// Replace all the uses of the original call instruction with the new call instruction
			ReplaceInstWithInst(call_inst->getParent()->getInstList(), it, call_c_call);
		    }
		}

	    }

	    // Deal with first-miss calls
	    std::unordered_map <BasicBlock *, std::unordered_set <Instruction *> > lpFirstMissCalls;

	    for (auto ii = gccfg.firstMissCalls.begin(), ie = gccfg.firstMissCalls.end(); ii != ie; ++ii) {
		Instruction *inst = ii->first;
		BasicBlock *lpHeader = ii->second;
		Function *func = lpHeader->getParent();
		assert(func);
		assert(calledFuncs.find(func) != calledFuncs.end());
		lpFirstMissCalls[lpHeader].insert(inst);
	    }

	    for (auto ii = lpFirstMissCalls.begin(), ie = lpFirstMissCalls.end(); ii != ie; ++ii) {
		BasicBlock *lpHeader = ii->first;
		Instruction *lpHeaderFirst = lpHeader->getFirstNonPHI();
		Function *func = lpHeader->getParent();
		DominatorTree &dt = getAnalysis<DominatorTreeWrapperPass>(*func).getDomTree();

		// Insert a preheader after each forward predecessor of the loop header
		for (pred_iterator pi = pred_begin(lpHeader), pe = pred_end(lpHeader); pi != pe; ++pi) {
		    BasicBlock *pred = *pi;

		    // Ignore predecessors from back edges
		    if (dt.dominates(lpHeaderFirst, pred) || lpHeader == pred)
			continue;

		    // Create a new basic block
		    std::string name = pred->getName().str() + ".succ";
		    BasicBlock *preheader = BasicBlock::Create(context, name, func, lpHeader);

		    // Set the new basic block as the successor of the predecessor
		    TerminatorInst *pred_term = pred->getTerminator();
		    for (unsigned i = 0; i < pred_term->getNumSuccessors(); i++) {
			if (pred_term->getSuccessor(i) == lpHeader)
			    pred_term->setSuccessor(i, preheader);
		    }

		    // Set the new basic block as an incoming block of the loop header
		    for (BasicBlock::iterator ii = lpHeader->begin(), ie = lpHeader->end(); ii != ie; ++ii) {
			PHINode *pn = dyn_cast<PHINode>(&*ii);
			if (!pn)
			    break;

			int i;
			while ((i = pn->getBasicBlockIndex(pred)) >= 0) {
			    pn->setIncomingBlock(i, preheader);
			}
		    }

		    // Insert code management code at the new preheader
		    builder.SetInsertPoint(preheader);
		    for (std::unordered_set <Instruction *>::iterator ji = ii->second.begin(), je = ii->second.end(); ji != je; ++ji) {
			CallInst *callInst = dyn_cast<CallInst>(*ji);
			BasicBlock::iterator it(callInst);
			AnalysisResult callerAnalysis = analysisResult[callInst].second;
			BasicBlock *bb = callInst->getParent();
			Function *caller = bb->getParent();
			Function *callee = callInst->getCalledFunction();

			//std::string func_name = caller->getName().str();

			// IRBuilder::SetInsertPoint must be called before builder can be used(?)
			Value *callerLMA = funcLMA[caller].first;
			Value *calleeLMA = funcLMA[callee].first;

			builder.CreateCall(func_c_get, calleeLMA, "epilogue");

			// Ensure the caller is present after the callee returns
			if (callerAnalysis != AlwaysHit) {

			    // Create a wrapper function for callee
			    Function *func_c_call = getOrInsertCCall3(callInst);
			    // Pass arguments to the pointer to the wraper function
			    std::vector<Value*> callArgs;

			    // Pass caller LMA with char* type as the first argument
			    callArgs.push_back(callerLMA);
			    // Pass callee address
			    callArgs.push_back(callee);
			    // Pass callee arguments if there are any as the following arguments
			    for (unsigned int i = 0, num = callInst->getNumArgOperands(); i < num; i++) {
				callArgs.push_back(callInst->getArgOperand(i));
			    }
			    // Create a new call instruction to the wrapper function
			    CallInst* call_c_call = CallInst::Create(func_c_call, callArgs);
			    // Replace all the uses of the original call instruction with the new call instruction
			    ReplaceInstWithInst(callInst->getParent()->getInstList(), it, call_c_call);

			}
		    }

		    // Create a terminator to the loop header
		    builder.CreateBr(lpHeader);
		}

	    }
	    /* Replace calls to user functions with calls to management functions: end */

	    /* Insert initialization code at smm_main: begin */
	    BasicBlock* main_entry = &func_main->getEntryBlock();
	    builder.SetInsertPoint(main_entry->getFirstNonPHI());
	    const_num_regions = builder.getInt32(num_regions);
	    const_num_overlayss = builder.getInt32(funcLMA.size());
	    // Initalize regions
	    builder.CreateCall(func_c_init_regions, const_num_regions, "");
	    // Initialize mappings
	    LoadInst* region_table = builder.CreateLoad(gvar_ptr_region_table);
	    std::vector <Value *> regions;
	    for (int i = 0; i < num_regions; ++i) {
		regions.push_back(builder.CreateGEP(region_table, builder.getInt32(i)));
	    }
	    std::vector<Value*> callArgs;
	    //callArgs.clear();
	    callArgs.push_back(const_num_overlayss);
	    for (auto ii = funcLMA.begin(), ie = funcLMA.end(); ii != ie; ii++) {
		DEBUG(errs() << ii->first->getName() << "->" << ii->second.first->getName() << " " << ii->second.second->getName() << "\n");
		Function *func = ii->first;
		callArgs.push_back(ii->second.first);
		callArgs.push_back(func);
		callArgs.push_back(builder.CreateSub(builder.CreatePtrToInt(ii->second.second, builder.getInt64Ty()), builder.CreatePtrToInt(ii->second.first, builder.getInt64Ty())));

		callArgs.push_back(regions[funcOverlay[func]]);
	    }
	    builder.CreateCall(func_c_init_map, callArgs);
	    // Copy the code of smm_main into the SPM
	    builder.CreateCall(func_c_get, funcLMA[func_smm_main].first);
	    /* Insert initialization code at smm_main: end */

	    return true;
	}

	std::unordered_map <CallInst *, std::pair<AnalysisResult, AnalysisResult> > analysisResult;

    };
}

char CodeManagement::ID = 0;
static RegisterPass<CodeManagement> X("smmecm", "Efficient Code Management Pass)");
