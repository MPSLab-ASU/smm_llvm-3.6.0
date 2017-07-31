#include "llvm/Pass.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Value.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

#include <fstream>
#include <iostream>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "Mnmt.h"
#include "MemoryAllocator.h"
#include "../SMMCommon/Helper.h"

using namespace llvm;

#define DEBUG_TYPE "smmegm"

//cl::opt<std::string> tileSize("tile-size", cl::desc("Specify the number of elements of each tile"), cl::value_desc("a string"));
cl::opt<std::string> size_constraint("size-constraint", cl::desc("Specify the size of the SPM space for non-stack data management"), cl::value_desc("a string"));
//cl::opt<std::string> output_file("output-file", cl::desc("Specify the name of the file saves output information"), cl::value_desc("a string"));
//cl::opt<std::string> of_alloc_size("of-alloc-size", cl::desc("Specify the output file for saving the size of allocated space"), cl::value_desc("a string"));


bool comp(std::pair <Value *, double> p1, std::pair <Value *, double> p2) {
    double v1 = p1.second;
    double v2 = p2.second;
    return v1 < v2;
}

namespace {
    struct EfficientDataManagement : public ModulePass {
	static char ID; // Pass identification, replacement for typeid
	EfficientDataManagement() : ModulePass(ID) {}

	virtual void getAnalysisUsage(AnalysisUsage &AU) const {
	    AU.addRequired<CallGraphWrapperPass>();
	    AU.addRequired<DominatorTreeWrapperPass>();
	    //AU.addRequired<LoopInfoWrapperPass>();
	    AU.addRequired<LoopInfo>();
	    AU.addRequired<ScalarEvolution> ();
	}


	inline Loop * getLoop(Function *func, BasicBlock *bb) {
	    return getAnalysis<LoopInfo>(*func).getLoopFor(bb);
	}

	inline unsigned getSmallConstantTripCount(Function *func, Loop *lp) {
	    return getAnalysis<ScalarEvolution>(*func).getSmallConstantTripCount(lp);
	}

	std::unordered_set <Instruction *> getMemInsts(Value *val) {
	    std::unordered_set <Instruction *> results;
	    for (Value::use_iterator ui = val->use_begin(), ue = val->use_end(); ui != ue; ++ui) {
		User *user = ui->getUser();
		//dbgs () << "\t" << *user << "\n";
		if(Instruction *inst = dyn_cast<Instruction>(user)) {
		    unsigned opcode = inst->getOpcode();
		    switch(opcode) {
			case Instruction::Load:
			    //dbgs() << "\t\t" << "true\n";
			    results.insert(inst);
			    break;
			case Instruction::Store:
			    //dbgs() << "\t\t" << "true\n";
			    results.insert(inst);
			    break;
			case Instruction::GetElementPtr: 
			case Instruction::BitCast: 
			    std::unordered_set <Instruction *> sub_results = getMemInsts (inst);
			    results.insert(sub_results.begin(), sub_results.end());
			    break;
		    }

		} else if (ConstantExpr *expr = dyn_cast<ConstantExpr>(user)){
		    std::unordered_set <Instruction *> sub_results = getMemInsts (expr);
		    results.insert(sub_results.begin(), sub_results.end());
		} else
		    assert(false);

	    }
	    return results;
	}
	

	// Estimate the number of accesses of the specified value
	std::unordered_map <Function *, unsigned long> estimateNumAccess(Value *val) {
	    std::unordered_map <Function *, unsigned long> num_accesses;
	    std::unordered_set <Instruction *> mem_insts = getMemInsts(val);

	    for (auto ii = mem_insts.begin(), ie = mem_insts.end(); ii != ie; ++ii) {
		Instruction *inst = *ii;
		BasicBlock *bb = inst->getParent();
		Function *func = bb->getParent();
		if (num_accesses.find(func) == num_accesses.end())
		    num_accesses[func] = 0;
		ScalarEvolution &se = getAnalysis<ScalarEvolution> (*func);
		// Check if the value is accessed within any loop
		if (Loop *lp = getLoop(func, bb)) {
		    unsigned lp_num_accesses = se.getSmallConstantTripCount(lp);
		    if (lp_num_accesses == 0)
			// Assign a constant value if the trip count of the current loop is unknow
			lp_num_accesses = DEFAULT_TRIP_COUNT;
		    // Check if the current loop has any parent loops
		    lp = lp->getParentLoop();
		    while (lp) {
			unsigned trip_count = se.getSmallConstantTripCount(lp);
			if (trip_count == 0)
			    trip_count = DEFAULT_TRIP_COUNT;
			lp_num_accesses *= trip_count;
			lp = lp->getParentLoop();
		    }
		    num_accesses[func] += lp_num_accesses;
		}
		// If the value is accessed outside any loops, then just increase the counter by one
		else
		    ++num_accesses[func];
	    }

	    return num_accesses;
	}

	bool runOnModule(Module &mod) override {
	    LLVMContext &context = getGlobalContext();
	    IRBuilder<> builder(context);
	    CallGraph &cg = getAnalysis < CallGraphWrapperPass>().getCallGraph(); 
	    const DataLayout *dl = mod.getDataLayout();
	    // External Variables
	    GlobalVariable *spm_array_begin = mod.getGlobalVariable("_spm_array_begin");
	    if (!spm_array_begin) {
		spm_array_begin = new GlobalVariable(mod, // Module 
			Type::getInt8Ty(context),
			false, //isConstant 
			GlobalValue::ExternalLinkage, // Linkage 
			0, // Initializer 
			"_spm_array_begin");
	    }

	    GlobalVariable *spm_global_begin = mod.getGlobalVariable("_spm_global_begin");
	    if (!spm_global_begin) {
		spm_global_begin = new GlobalVariable(mod, // Module 
			Type::getInt8Ty(context),
			false, //isConstant 
			GlobalValue::ExternalLinkage, // Linkage 
			0, // Initializer 
			"_spm_global_begin");
	    }

	    // Initialize memory allocators
	    spm_array_allocator.setBase(spm_array_begin);
	    spm_global_allocator.setBase(spm_global_begin);

	    // Functions
	    Function *func_main = mod.getFunction("main");
	    Function *func_smm_main = mod.getFunction("smm_main");
	    Function *func_heap_allocator = mod.getFunction("_allocate_in_bound");

	    // parameters
	    //size_t tile_size = std::stoul(tileSize);
	    size_t sizeConstraint = std::stoul(size_constraint);
	    size_t global_size = 0;
	    size_t heap_size = 0;
	    std::unordered_map <Value *, Value *> spm_allocation;

	    // Global management 
	    std::unordered_set <GlobalVariable *> globalVars;
	    std::unordered_map <GlobalVariable *, std::unordered_map<Function *, unsigned long> > gvarNumAccessesByFunction;
	    std::unordered_map <GlobalVariable *, unsigned long > gvarNumAccesses;
	    std::vector< std::pair <GlobalVariable *, double> > gvarAllocPriority;

	    if (!sizeConstraint)
		return false;

	    // Step 1: Estimate number of access frequencies of global variables
	    // Get call path
	    CallGraphNode *cgn_smm_main = cg[func_smm_main];
	    CallGraphNode::CallRecord *root;
	    std::vector<std::vector<CallGraphNode::CallRecord *> > paths;
	    std::unordered_set <CallGraphNode *> undecidable_cgns;
	    // Initialize root node by main function
	    for (CallGraphNode::iterator cgni = cg.begin()->second->begin(), cgne = cg.begin()->second->end(); cgni != cgne; cgni++) {
		if (cgni->second == cgn_smm_main) {
		    root = &*cgni;
		    break;
		}
	    }
	    assert(CallGraphNode::iterator(root) != cg.begin()->second->end());
	    // Get the possible paths of the call graph
	    auto res = getPaths(root);
	    paths = res.first;
	    undecidable_cgns = res.second;
	    // Estimate number of accesses to global variables of each function
	    for (Module::global_iterator gi = mod.global_begin(), ge = mod.global_end(); gi != ge; ++gi) {
		GlobalVariable *gvar = &*gi;
		StringRef gvar_name = gvar->getName();
		PointerType *gvar_type = gvar->getType();
		assert(gvar_type);
		if (isManagementVariable(gvar))
		    continue;
		if (gvar_name.startswith(".str"))
		    continue;
		if (gvar_name.startswith("str"))
		    continue;
		if (gvar_name.startswith("_spm"))
		    continue;
		if (gvar_name == "stdin")
		    continue;
		if (gvar_name == "stdout")
		    continue;
		if (gvar_name == "stderr")
		    continue;
		globalVars.insert(gvar);
		gvarNumAccessesByFunction[gvar] = estimateNumAccess(gvar);
	    }

	    for (auto ii = gvarNumAccessesByFunction.begin(), ie = gvarNumAccessesByFunction.end(); ii != ie; ++ii) {
		GlobalVariable *gvar = ii->first;
		dbgs() << gvar->getName() << "\n";
		for (auto ji = ii->second.begin(), je = ii->second.end(); ji != je; ++ji) {
		    Function *func = ji->first;
		    unsigned long num = ji->second;
		    dbgs() << "\t" << func->getName() << "\t" << num << "\n";
		}
	    }

	    dbgs() << "\n\n";

	    // Count the number of overall accesses
	    for (size_t i = 0; i < paths.size(); i++) {
		//dbgs () << "path " << i << " : ";
		Function *func = paths[i][0]->second->getFunction();
		std::string func_name = func->getName();
		//dbgs () << func_name << "\t";
		unsigned num_overall_iterations = 1;
		// The number of accesses to global variables in this path path
		std::unordered_map <Value *, unsigned long> num_overall_accesses;
		// Initiate the number of accesses of global variables in current path with the number of accesses in smm_main
		for (auto gi = globalVars.begin(), ge = globalVars.end(); gi != ge; ++gi) {
		    GlobalVariable *gvar = *gi;
		    num_overall_accesses[gvar] = gvarNumAccessesByFunction[gvar][func_smm_main];
		}
		// Count the number of accesses of the rest of current path
		for (size_t j = 1; j < paths[i].size(); j++) {
		    CallInst *call_inst = dyn_cast <CallInst> (paths[i][j]->first);
		    BasicBlock *bb = call_inst->getParent();
		    Function *caller = bb->getParent();
		    Function *callee = paths[i][j]->second->getFunction();
		    std::string callee_name = callee->getName();
		    LoopInfo &lpi = getAnalysis<LoopInfo>(*caller);
		    ScalarEvolution &se = getAnalysis<ScalarEvolution> (*caller);
		    unsigned num_iterations = 1;
		    // Estimate the number of iterations if the call happens within a loop nest
		    if (Loop *lp = lpi.getLoopFor(bb)) {
			// Estimate the number of iterations of the innermost loop
			num_iterations = se.getSmallConstantTripCount(lp);
			if (num_iterations == 0)
			    num_iterations = DEFAULT_TRIP_COUNT;
			// Estimate the number of overall iterations
			lp = lp->getParentLoop();
			while (lp) {
			    unsigned trip_count = se.getSmallConstantTripCount(lp);
			    if (trip_count == 0)
				trip_count = DEFAULT_TRIP_COUNT;
			    num_iterations *= trip_count;
			    lp = lp->getParentLoop();
			}
		    }
		    // Accummulate the number of iterations
		    num_overall_iterations *= num_iterations;
		    // Accumulate the number of accesses for each global variables
		    for (auto gi = globalVars.begin(), ge = globalVars.end(); gi != ge; ++gi) {
			GlobalVariable *gvar = *gi;
			num_overall_accesses[gvar] += num_overall_iterations * gvarNumAccessesByFunction[gvar][callee];
		    }
		}
		// Add the number of accesses of the current path
		for (auto gi = globalVars.begin(), ge = globalVars.end(); gi != ge; ++gi) {
		    GlobalVariable *gvar = *gi;
		    gvarNumAccesses[gvar] += num_overall_accesses[gvar];
		}
	    }
	    //for (auto ii = undecidable_cgns.begin(), ie = undecidable_cgns.end(); ii != ie; ++ii) {
		//dbgs() << (*ii)->getFunction()->getName() << "\n";
	    //}

	    // Calculate the priority of arrays for allocation
	    for (auto  gi = globalVars.begin(), ge = globalVars.end(); gi != ge; ++gi) {
		GlobalVariable *gvar = *gi;
		PointerType *gvar_type = gvar->getType();
		assert(gvar_type);
		size_t gvar_size = getTypeSize(dl, gvar_type->getElementType());
		dbgs() << gvar->getName() << "\t" << gvarNumAccesses[gvar] << "\n";
		gvarAllocPriority.push_back(std::make_pair(gvar, (double)gvarNumAccesses[gvar]/(double)gvar_size));
	    }
	    dbgs() << "\n\n";

	    sort(gvarAllocPriority.rbegin(), gvarAllocPriority.rend(), comp);
	    // Allocate arrays into the available SPM space as much as possible
	    //dbgs() << "\n";
	    builder.SetInsertPoint(func_main->getEntryBlock().getFirstNonPHI());
	    for (auto ii = gvarAllocPriority.begin(), ie = gvarAllocPriority.end(); ii != ie; ++ii) {
		GlobalVariable *gvar = ii->first;
		StringRef gvar_name = gvar->getName();
		PointerType *gvar_type = gvar->getType();
		assert(gvar_type);
		size_t gvar_size = getTypeSize(dl, gvar_type->getElementType());
		Constant * spm_addr = spm_global_allocator.allocateInBound(gvar_size, sizeConstraint);
		dbgs() << gvar_name << "\t" << *gvar_type << "\t" << gvar_size << "\n";
		if (spm_addr) {
		    dbgs() << "\t->" << *spm_addr << "\n";
		    Value *gvar_spm_addr = builder.CreatePointerCast(spm_addr, gvar_type);
		    spm_allocation[gvar] = gvar_spm_addr;
		    //size_t allocated_size = spm_global_allocator.getPos();
		    //if (allocated_size > global_size)
			//global_size = allocated_size;
		}
	    }
	    global_size = spm_global_allocator.getPos();
	    /*
	    // Step 2: Loop tiling for affine array accesses
	    // Go through all the functions
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		if(CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second)) {
		    Function *caller = cgn->getFunction();
		    // Skip external nodes
		    if(!caller)
			continue;
		    // Skip library functions
		    if (isLibraryFunction(caller))
			continue;
		    // Skip management functions
		    if (isManagementFunction(caller))
			continue;
		    if (func_smm_main && caller == func_main)
			continue;
		    DEBUG(errs() << caller->getName() << "\n");
		    LoopInfo &lpi = getAnalysis<LoopInfo>(*caller);
		    //ScalarEvolution &se = getAnalysis<ScalarEvolution> (*caller);
		    std::unordered_set <BasicBlock *> innermost_loops;

		    // Find out the innermost loops in the current function
		    for (LoopInfo::iterator li = lpi.begin(), le = lpi.end(); li != le; ++li) {
			Loop *loop = *li;
			std::unordered_set < BasicBlock *> temp  = getInnermostLoops(loop);
			innermost_loops.insert(temp.begin(), temp.end());
		    }
		    // Reorganize innerstmost loops to accelerate the array accesses within them
		    for (auto ii = innermost_loops.begin(), ie = innermost_loops.end(); ii != ie; ++ii) {
			BasicBlock *loop_header = *ii;
			DEBUG(dbgs() << "\t" << loop_header->getName() << "\n");
			Loop *loop = lpi.getLoopFor(loop_header);

			PHINode *new_indvar;
			BasicBlock *new_loop_header, *new_loop_body;
			Value *new_loop_bound;
			// Skip the current loop if it is not analyzable
			if (!preprocess(loop))
			    continue;

			PHINode *indvar = loop->getCanonicalInductionVariable();
			DEBUG(dbgs() << "\t\tLoop index: " << *indvar<< "\n");


			// Get accesses to arrays within the current loop
			std::unordered_map <Value*, std::map < std::pair<User *, unsigned int>, std::unordered_set <Instruction *> > > array_mem_insts = getArrayAccesses(loop);
			// DMA requests
			std::unordered_map < Value*, std::map < std::vector <Value *>, std::pair <Value *, long > > >  dma_reqs;
			// Rule out arrays that have been allocated to the SPM
			for (auto ii = spm_allocation.begin(), ie = spm_allocation.end(); ii != ie; ++ii) {
			    Value * gvar = ii->first;
			    array_mem_insts.erase(gvar);
			}
			if (array_mem_insts.empty())
			    continue;
			for (auto ii = array_mem_insts.begin(), ie = array_mem_insts.end(); ii != ie; ++ii) {
			    //Value * array_var = ii->first;
			    //DEBUG(dbgs() << "\t\t\t" << *array_var << "\n");
			    assert(ii->second.size() == 1);
			    for (auto ji = ii->second.begin(), je = ii->second.end(); ji != je; ++ji) {

				std::pair <User*, unsigned int> p = ji->first;
				User* gep = std::get<0>(p);
				//DEBUG(dbgs() << "\t\t\t\t" << *gep << "\n");



				for (auto ki = ji->second.begin(), ke = ji->second.end(); ki != ke; ++ki) {
				    Instruction *inst = *ki;
				    //DEBUG(dbgs() << "\t\t\t\t\t" << *inst << "\n");
				}

			    }
			}
			// Loop tiling
			//dbgs() << "tile size = " << tile_size << "\n";
			assert(tile_size > 0);
			auto t = createLoopTiling(getLoop(caller, loop_header), tile_size);
			new_indvar = std::get<0>(t);
			new_loop_header = std::get<1>(t);
			new_loop_body = std::get<2>(t);
			new_loop_bound = std::get<3>(t);
			// (1) Create necessary DMA transfers and (2) replace memory accesses with SPM accesses
			//DEBUG(dbgs() << "\n\n");
			for (auto ii = array_mem_insts.begin(), ie = array_mem_insts.end(); ii != ie; ++ii) {
			    //Value * array_var = ii->first;
			    for (auto ji = ii->second.begin(), je = ii->second.end(); ji != je; ++ji) {
				//const std::vector<Value *> &indices = ji->first;
				std::pair <User*, unsigned int> p = ji->first;
				User* gep = std::get<0>(p);
				unsigned int indvar_pos = std::get<1>(p);
				size_t req_size = 0;
				bool hasLoads = false, hasStores = false;

				//(1) Create DMA transfers 
				// Allocate SPM space
				for (auto ki = ji->second.begin(), ke = ji->second.end(); ki != ke; ++ki) {
				    Instruction *inst = *ki;
				    unsigned opcode = inst->getOpcode();
				    if (opcode == Instruction::Load)
					hasLoads = true;
				    else if (opcode == Instruction::Store)
					hasStores = true;
				    if (!req_size) {
					req_size = getMemReqSize(inst);
				    }
				}
				Constant * spm_base_addr = spm_array_allocator.allocate(req_size * tile_size);
				DEBUG(dbgs() << "\t\t\t\t" << *gep << " -> " << *spm_base_addr << "\n");
				//DEBUG(dbgs() << "\t\t\t\t\t" << req_size << "\n");
				// Get the start address of the main memory location
				Value * mem_loc_base = gep->getOperand(0);
				std::vector <Value *> mem_loc_indices;
				for (unsigned int i = 1; i < gep->getNumOperands(); ++i) {
				    if (i != indvar_pos)
					mem_loc_indices.push_back(gep->getOperand(i));
				    else
					mem_loc_indices.push_back(new_indvar);
				}

				// Insert DMA calls
				IRBuilder<> builder(context);
				if (hasLoads) {
				    //createDMACall(mod, spm_base_addr, mem_loc, size * tile_size, 1, new_loop_header_end);
				    int trans_dir = 1;
				    Instruction *insert_pt = new_loop_header->getTerminator();
				    builder.SetInsertPoint(insert_pt);
				    Value *mem_loc = builder.CreateGEP(mem_loc_base, mem_loc_indices, "mem_loc");
				    Value *size = builder.CreateMul(builder.getInt64(req_size), builder.CreateSExtOrTrunc(new_loop_bound, builder.getInt64Ty()));
				    createDMACall(mod, spm_base_addr, mem_loc, size, trans_dir, insert_pt);
				} 
				if (hasStores) {
				    //createDMACall(mod, spm_base_addr, mem_loc, size * tile_size, 0, new_loop_body_begin);
				    int trans_dir = 0;
				    Instruction *insert_pt = new_loop_body->getFirstInsertionPt();
				    builder.SetInsertPoint(insert_pt);
				    Value *mem_loc = builder.CreateGEP(mem_loc_base, mem_loc_indices, "mem_loc");
				    Value *size = builder.CreateMul(builder.getInt64(req_size), builder.CreateSExtOrTrunc(new_loop_bound, builder.getInt64Ty()));
				    createDMACall(mod, spm_base_addr, mem_loc, size, trans_dir, insert_pt);
				}
				// (2) Redirect memory accesses to the SPM
				Instruction *gep_inst = dyn_cast <Instruction> (gep);
				assert(gep_inst);
				builder.SetInsertPoint(gep_inst);
				Value *spm_addr = builder.CreateGEP(builder.CreateBitCast(spm_base_addr, gep->getType()), indvar);
				for (auto ki = ji->second.begin(), ke = ji->second.end(); ki != ke; ++ki) {
				    Instruction *inst = *ki;
				    DEBUG(dbgs() << "\t\t\t\t\t" << *inst << "\n");
				    for (unsigned int i = 0; i < inst->getNumOperands(); ++i)
					if (inst->getOperand(i) == gep) {
					    inst->setOperand(i, spm_addr);
					    break;
					}
				}


			    }

			}
			// Reset SPM memory allocator
			spm_array_allocator.resetPos();
		    }
		}
	    }
	    */


	    // Step 3: substitute the arrays with the allocated SPM locations
	    for (auto ii = spm_allocation.begin(), ie = spm_allocation.end(); ii != ie; ++ii) {
		Value * gvar = ii->first;
		Value * gvar_spm_addr = ii->second;
		PointerType *gvar_type = cast <PointerType> (gvar->getType());
		size_t gvar_size = getTypeSize(dl, gvar_type->getElementType());
		// Replace uses of the array with the allocated SPM location
		gvar->replaceAllUsesWith(gvar_spm_addr);

		// Copy the existing values into the SPM location
		int trans_dir = 1;
		Instruction *insert_pt = func_main->getEntryBlock().getFirstNonPHI();
		builder.SetInsertPoint(insert_pt);

		Value *mem_loc = builder.CreateBitCast(gvar, builder.getInt8PtrTy(), "mem_loc");
		Value *spm_loc = builder.CreateBitCast(gvar_spm_addr, builder.getInt8PtrTy(), "spm_loc");
		Value *size = builder.getInt64(gvar_size) ;
		//createDMACall(mod, gvar_spm_addr, mem_loc, size, trans_dir, insert_pt);
		createDMACall(mod, spm_loc, mem_loc, size, trans_dir, insert_pt);
	    }

	    // Step 4: Allocate as much heap objects on SPM as possible
	    if (sizeConstraint < global_size)
		heap_size = 0;
	    else
		heap_size = sizeConstraint - global_size;
	    DEBUG(dbgs() << "heap_size =  " << heap_size << "\n");
	    // Substitute calls to malloc with calls to allocate
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		if(CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second)) {
		    Function *caller = cgn->getFunction();
		    // Skip external nodes
		    if(!caller)
			continue;
		    // Skip library functions
		    if (isLibraryFunction(caller))
			continue;
		    // Skip management functions
		    if (isManagementFunction(caller))
			continue;
		    // Skip the wrapper of the main function
		    if (func_smm_main && caller == func_main)
			continue;

		    DEBUG(dbgs() << caller->getName() << "\n");
		    for (CallGraphNode::iterator cgni = cgn->begin(), cgne = cgn->end(); cgni != cgne; ++cgni) {
			if (!cgni->first) 
			    continue;
			CallInst *call_inst = dyn_cast <CallInst> (cgni->first);
			if (call_inst->isInlineAsm())
			    continue;
			CallGraphNode *callee_cgn = cgni->second;
			Function *callee = callee_cgn->getFunction();
			if (!callee) {
			    callee = dyn_cast <Function> (call_inst->getCalledValue()->stripPointerCasts());
			    assert(callee);
			}
			if (callee->getName() == "malloc") {
			    assert(call_inst->getNumArgOperands() == 1);


			    builder.SetInsertPoint(call_inst);
			    std::vector <Value *> args;
			    args.push_back(call_inst->getArgOperand(0));
			    args.push_back(builder.getInt64(heap_size));
			    assert(func_heap_allocator);
			    CallInst *new_malloc =  builder.CreateCall(func_heap_allocator, args);
			    DEBUG(dbgs() << "\t" << *call_inst << " --> " <<  *new_malloc <<"\n");

			    call_inst->replaceAllUsesWith (new_malloc);

			}
		    }



		}
	    }

	    // erase all the free
	    for (CallGraph::iterator cgi = cg.begin(), cge = cg.end(); cgi != cge; cgi++) {
		if(CallGraphNode *cgn = dyn_cast<CallGraphNode>(cgi->second)) {
		    Function *caller = cgn->getFunction();
		    // Skip external nodes
		    if(!caller)
			continue;
		    // Skip library functions
		    if (isLibraryFunction(caller))
			continue;
		    // Skip management functions
		    if (isManagementFunction(caller))
			continue;
		    // Skip the wrapper of the main function
		    if (func_smm_main && caller == func_main)
			continue;

		    //DEBUG(dbgs() << caller->getName() << "\n");
		    for (CallGraphNode::iterator cgni = cgn->begin(), cgne = cgn->end(); cgni != cgne; ++cgni) {
			if (!cgni->first) 
			    continue;
			CallInst *call_inst = dyn_cast <CallInst> (cgni->first);
			if (call_inst->isInlineAsm())
			    continue;
			CallGraphNode *callee_cgn = cgni->second;
			Function *callee = callee_cgn->getFunction();
			if (!callee) {
			    callee = dyn_cast <Function> (call_inst->getCalledValue()->stripPointerCasts());
			    assert(callee);
			}
			if (callee->getName() == "free") {
			    DEBUG(dbgs() << "\t" << *call_inst << "\n");

			    call_inst->eraseFromParent();

			}
		    }

		}
	    }
	    return true;
	}

    };
}

char EfficientDataManagement::ID = 0;
static RegisterPass<EfficientDataManagement> X("smmegm", "Efficient Array Management Pass");
