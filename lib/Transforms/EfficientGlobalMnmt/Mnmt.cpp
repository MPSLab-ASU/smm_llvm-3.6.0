
#include "llvm/Pass.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Value.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

#include <map>
#include <queue>
#include <stack>
#include <unordered_map>
#include <unordered_set>
#include <utility>

#include "../SMMCommon/Helper.h"

using namespace llvm;

#define DEBUG_TYPE "smmegm"

/* Misc */

size_t getMemReqSize(Instruction *inst) {
    size_t size = 0;
    unsigned opcode = inst->getOpcode();
    Value *pointerOperand;
    const DataLayout *dl = inst->getParent()->getParent()->getParent()->getDataLayout();
    if (opcode == Instruction::Load) {
	pointerOperand = (cast<LoadInst>(inst))->getPointerOperand();
    } else if (opcode == Instruction::Store) {
	pointerOperand = (cast<StoreInst>(inst))->getPointerOperand();
    }
    size = getTypeSize(dl, pointerOperand->getType()->getPointerElementType());
    return size;
}

void createDMACall(Module &mod, Value *spm_addr, Value *mem_addr, Value *size, int dir, Instruction *insert_pt) {
    LLVMContext &context = getGlobalContext();
    PointerType* ptr_ty_int8 = PointerType::get(IntegerType::get(context, 8), 0);
    Function *func_dma = mod.getFunction("dma");
    assert(func_dma);
    IRBuilder<> builder(insert_pt);


    Value* int8_spm_addr = builder.CreatePointerCast(spm_addr, ptr_ty_int8, "spm_addr");
    Value * int8_mem_addr = builder.CreatePointerCast(mem_addr, ptr_ty_int8, "mem_addr");
    //ConstantInt *int64_size = builder.getInt64(size);
    Value *int64_size = builder.CreateSExtOrTrunc(size, builder.getInt64Ty());
    ConstantInt *int32_dir = builder.getInt32(dir);

    std::string name = (dir == 1) ? "m2s_dma" : "s2m_dma" ;

    // Transfer data from memory to SPM at the beginning of the basic block
    std::vector<Value*> dma_params;
    dma_params.push_back(int8_spm_addr);
    dma_params.push_back(int8_mem_addr);
    dma_params.push_back(int64_size);
    dma_params.push_back(int32_dir);
    builder.CreateCall(func_dma, dma_params, name);
}

/* Data Flow */

std::unordered_set < BasicBlock *> getInnermostLoops(Loop * loop) {
    std::unordered_set < BasicBlock *> result;
    // Check if the current loop is an innermost loop
    if (loop->getSubLoops().size() == 0) 
	result.insert(loop->getHeader());
    // Otherwise, recursively visit the sub loops
    else {
	for (Loop::iterator sli = loop->begin(), sle = loop->end(); sli != sle; ++sli) {
	    Loop *sub_loop = *sli;
	    std::unordered_set < BasicBlock *> sub_result = getInnermostLoops(sub_loop);
	    result.insert(sub_result.begin(), sub_result.end());
	}
    } 
    return result;
}

std::unordered_map <Value*, std::map < std::pair<User *, unsigned int>, std::unordered_set <Instruction *> > >  getArrayAccesses(Loop *loop) {
    //std::unordered_map <Value*, std::map < std::vector<Value *>, std::unordered_set <Instruction *> > > array_mem_insts;
    std::unordered_map <Value*, std::map < std::pair<User *, unsigned int>, std::unordered_set <Instruction *> > > array_mem_insts;
    std::unordered_set <Value *> nonaffine_arrays;

    PHINode *indvar = loop->getCanonicalInductionVariable();

    // Find array accesses in the innestmost loops
    for (Loop::block_iterator bi = loop->block_begin(), be = loop->block_end(); bi != be; ++bi) {
	BasicBlock *bb = *bi;
	for (BasicBlock::iterator ii = bb->begin(), ie = bb->end(); ii != ie; ++ii) {
	    Instruction *inst = &*ii;
	    unsigned opcode = inst->getOpcode();
	    Value *ptr_operand = NULL;
	    User *gep = NULL;
	    if (opcode == Instruction::Load)
		ptr_operand = inst->getOperand(0);
	    else if (opcode == Instruction::Store) 
		ptr_operand = inst->getOperand(1);
	    else
		continue;

	    if (Instruction *inst = dyn_cast <Instruction> (ptr_operand)) {
		if (inst->isCast()) {
		    ptr_operand = inst->getOperand(0);
		}
	    }


	    // Arrays should be accessed via GEP instructions or GEP expressions
	    if (GetElementPtrInst *gep_inst = dyn_cast<GetElementPtrInst>(ptr_operand))
		gep = cast<User> (gep_inst);
	    else if (ConstantExpr *gep_expr = dyn_cast<ConstantExpr>(ptr_operand)) {
		if (gep_expr->getOpcode() == Instruction::GetElementPtr) {
		    gep = cast<User> (gep_expr);
		    assert(false);
		}
	    }
	    if (gep) {
		/*
		   std::vector<Value *> indices;
		   for (unsigned i = 1; i < gep->getNumOperands(); ++i)
		   indices.push_back(gep->getOperand(i));
		 */ 
		unsigned indvar_pos = 0;
		for (unsigned i = 1; i < gep->getNumOperands(); ++i)
		    if (gep->getOperand(i) == indvar) {
			indvar_pos = i;
			break;
		    }
		Value *array_var = gep->getOperand(0);

		// Skip non-global arrays
		PointerType *array_type = cast <PointerType> (array_var->getType());
		if (!array_type->getElementType()->isArrayTy())
		    continue;


		if (indvar_pos) {
		    array_mem_insts[array_var][std::make_pair(gep, indvar_pos)].insert(inst);
		} else 
		    nonaffine_arrays.insert(array_var);
		//DEBUG(dbgs() << "\t" << *inst << "\n");
		//DEBUG(dbgs() << "\t\t" << *ptr_operand << "\n");
	    }

	}
    }

    for (auto ii = nonaffine_arrays.begin(), ie = nonaffine_arrays.end(); ii != ie; ++ii) {
	Value * array_var = *ii;
	array_mem_insts.erase(array_var);
    }

    return array_mem_insts;
}


/* Control FloW */


bool preprocess(Loop *loop) {
    IRBuilder <> builder(getGlobalContext());
    BasicBlock *header, *exiting_block, *predecessor;
    TerminatorInst *exiting_inst;
    CmpInst *exitcond;
    Value *exitcond_lhs;
    PHINode *indvar;
    Instruction *indvar_next;

    // Not analyzable if the loop does not have a canonical induction variable
    indvar = loop->getCanonicalInductionVariable();
    if (!indvar)
	return false;


    // Not analyzable if the loop does not have the value of canonical induction variable for the next iteration
    indvar_next = NULL;
    for (unsigned i = 0; i < indvar->getNumIncomingValues(); i++) {
	if (indvar->getIncomingBlock(i) == loop->getLoopLatch()) {
	    indvar_next = dyn_cast <Instruction> (indvar->getIncomingValue(i));
	    break;
	}
    }
    if (!indvar_next) 
	return false;

    // Not analyzable if the condition of the exiting instruction is not based on the canonical induction variable
    exiting_block = loop->getLoopLatch();
    exiting_inst = exiting_block->getTerminator();
    BranchInst *br_inst = cast<BranchInst>(exiting_inst);
    assert(br_inst->isConditional());
    exitcond = dyn_cast<CmpInst>(br_inst->getCondition());
    exitcond_lhs = exitcond->getOperand(0);
    Value *which_indvar = exitcond_lhs;
    if (Instruction *inst = dyn_cast <Instruction>(which_indvar))
	if (inst->getOpcode() == Instruction::Trunc)
	    which_indvar = inst->getOperand(0);
    if (which_indvar != indvar && which_indvar != indvar_next)
	return false;

    // Deal with phi nodes that contains the result of a GEP, a load, or a store in the header
    header = loop->getHeader();
    DEBUG(dbgs() << "\t\tphi nodes:\n");
    predecessor = loop->getLoopPredecessor();
    assert(predecessor);
    for (BasicBlock::iterator ii = header->begin(), ie = header->end(); ii != ie; ++ii) {
	PHINode *pn = dyn_cast<PHINode>(ii);
	if (!pn)
	    break;
	DEBUG(dbgs() << "\t\t\t" << *pn << "\n");
	// Skip the loop index
	if (pn == indvar)
	    continue;


	// Find the index of the predecessor and the latch block of current loop
	unsigned pred_index = pn->getNumIncomingValues(), latch_index = pn->getNumIncomingValues();
	for (unsigned i = 0; i < pn->getNumIncomingValues(); ++i) {
	    BasicBlock *bb = pn->getIncomingBlock(i);
	    if (bb == predecessor) {
		pred_index = i;
	    } else if (bb == exiting_block) {
		latch_index = i;
	    }
	}
	assert(pred_index < pn->getNumIncomingValues() && latch_index < pn->getNumIncomingValues());

	Instruction *inst = dyn_cast<Instruction>(pn->getIncomingValue(pred_index));
	ConstantExpr *expr = dyn_cast<ConstantExpr>(pn->getIncomingValue(pred_index));
	if (inst || expr) {
	    unsigned opcode;
	    if (inst)
		opcode = inst->getOpcode();
	    else 
		opcode = expr->getOpcode();
	    if (opcode == Instruction::GetElementPtr || opcode == Instruction::Load || opcode == Instruction::Store) {
		// Return false if the incoming value of the latch block is not an induction variable
		if (Instruction * inst = dyn_cast<Instruction> (pn->getIncomingValue(latch_index))) {
		    bool isInductionVariable = false;
		    for (unsigned int i = 0; i < inst->getNumOperands(); ++i) {
			Value *val = inst->getOperand(i);
			if (val == indvar_next || val == indvar) 
			    isInductionVariable = true;
		    }
		    if (!isInductionVariable)
			return false;
		}

		// If the incoming value of the latch block is a GEP and is an indcution variable, then replace it with a new GEP based on the loop index
		if (opcode == Instruction::GetElementPtr) {
		    if (GetElementPtrInst * gep_inst = dyn_cast<GetElementPtrInst> (pn->getIncomingValue(latch_index))) {
			std::vector <Value *> idxList;
			bool isInductionVariable = false;
			for (unsigned int i = 1; i < gep_inst->getNumOperands(); ++i) {
			    Value * idx = gep_inst->getOperand(i);
			    if (idx == indvar_next || idx == indvar) {
				isInductionVariable = true;
				idxList.push_back(indvar);
			    }
			    else
				idxList.push_back(idx);
			}
			// Return false if the GEP expression is not an indcution variable
			if (!isInductionVariable)
			    return false;
			DEBUG(dbgs() << "\t\tpreprocess:\n");
			DEBUG(dbgs() << "\t\t\t" << *pn << "\n");
			for (Value::use_iterator ui = pn->use_begin(), ue = pn->use_end(); ui != ue; ++ui) {
			    DEBUG(dbgs() << "\t\t\t\t" << *ui->getUser() << "\n");
			}
			builder.SetInsertPoint(header->getFirstInsertionPt());
			Value * new_gep = builder.CreateGEP(gep_inst->getOperand(0), idxList);
			pn->replaceAllUsesWith(new_gep);

		    }
		}
		// TODO: Handle load and store instructions

	    }

	}
    }




    return true;
}

BasicBlock* createBasicBlock(const Twine &name, Function *parent, BasicBlock *pred, BasicBlock *succ) {
    LLVMContext &context = getGlobalContext();

    // Create a new basic block
    BasicBlock *new_bb = BasicBlock::Create(context, name, parent, succ);

    // Set the new basic block as the successor of the predecessors of the previous basic block
    TerminatorInst *pred_exting_inst = pred->getTerminator();
    for (unsigned i = 0; i < pred_exting_inst->getNumSuccessors(); i++) {
	if (pred_exting_inst->getSuccessor(i) == succ)
	    pred_exting_inst->setSuccessor(i, new_bb);
    }

    // Set the new basic block as an incoming block of the subsequent basic block
    for (BasicBlock::iterator ji = succ->begin(), je = succ->end(); ji != je; ++ji) {
	PHINode *pn = dyn_cast<PHINode>(ji);
	if (!pn)
	    break;
	int i;
	while ((i = pn->getBasicBlockIndex(pred)) >= 0) {
	    pn->setIncomingBlock(i, new_bb);
	}
    }
    return new_bb;
}


std::tuple < PHINode *, BasicBlock *, BasicBlock *, Value *> createLoopTiling(Loop *loop, size_t tile_size) {
    BasicBlock *pred, *header, *exiting_block, *exit_block;
    TerminatorInst *exiting_inst;
    CmpInst *exitcond;
    Value *exitcond_lhs, *exitcond_rhs;
    Value *exitcond_final_rhs;
    PHINode *indvar;
    Instruction *indvar_next;

    BasicBlock *new_loop_header, *new_loop_body;
    Value *new_exitcond;
    PHINode *new_indvar;
    Value *new_indvar_next;

    std::vector<Use *> affected_indvar_uses;

    LLVMContext &context = getGlobalContext();
    IRBuilder <> builder(context);

    // Get the predecessor of the loop
    pred = loop->getLoopPredecessor();
    // Get the loop header
    header = loop->getHeader();
    // Get canonical induction variable
    indvar = loop->getCanonicalInductionVariable();
    assert(indvar);
    Function *fi = header->getParent();


    // Get the value of induction variable for the next iteration
    indvar_next = NULL;
    for (unsigned i = 0; i < indvar->getNumIncomingValues(); i++) {
	if (indvar->getIncomingBlock(i) == loop->getLoopLatch()) {
	    indvar_next = dyn_cast <Instruction> (indvar->getIncomingValue(i));
	    break;
	}
    }

    assert(indvar_next);



    // Get the use of the induction variable that should maintain the same value
    for (Value::use_iterator ui = indvar->use_begin(), ue = indvar->use_end(); ui != ue; ++ui) {
	Instruction *user_inst = dyn_cast <Instruction> (ui->getUser());
	if (user_inst == indvar_next)
	    continue;
	affected_indvar_uses.push_back(&*ui);
    }



    // Get the exiting block of the loop
    exiting_block = loop->getLoopLatch();
    // Get the exiting instruction
    exiting_inst = exiting_block->getTerminator();
    BranchInst *br_inst = cast<BranchInst>(exiting_inst);
    assert(br_inst->isConditional());
    // Get the exit block of the loop
    exit_block = NULL;
    for (unsigned i = 0; i < br_inst->getNumSuccessors (); ++i) {
	BasicBlock *succ = br_inst->getSuccessor(i);
	if (succ != header) {
	    exit_block = succ;
	    break;
	}
    }
    assert(exit_block);
    // Get the exit condition of the original exiting block
    exitcond = dyn_cast<CmpInst>(br_inst->getCondition());
    exitcond_lhs = exitcond->getOperand(0);
    exitcond_rhs = exitcond->getOperand(1);



    // Create a basic block as the header of the new loop between the predecessor and the header
    new_loop_header = createBasicBlock("new_loop_header", fi, pred, header);

    // Create a basic block as the latch of the new loop between the exiting and the exit block
    new_loop_body = createBasicBlock("new_loop_body", fi, exiting_block, exit_block);


    // Create the body for the outer loop header
    builder.SetInsertPoint(new_loop_header);
    Value *const_tile_size = builder.getIntN(indvar->getType()->getIntegerBitWidth(), tile_size);
    // Create a placeholder for new_indvar_next
    Argument* fwdref = new Argument(indvar->getType());
    // Create a new induction variable at the outer loop header
    new_indvar = builder.CreatePHI(indvar->getType(), indvar->getNumIncomingValues(), "new_indvar");
    new_indvar->addIncoming(fwdref, new_loop_body);
    for (unsigned i = 0; i < indvar->getNumIncomingValues(); i++) 
	if (indvar->getIncomingBlock(i) == new_loop_header) 
	    new_indvar->addIncoming(indvar->getIncomingValue(i), pred);
    // Change insert point to be right before the exit condition if its RHS is defined within the current loop (e.g. a global variable)
    if (Instruction * inst = dyn_cast<Instruction>(exitcond_rhs)) {
	if (inst->getParent() == exiting_block) {
	    builder.SetInsertPoint(exitcond);
	}
    }
    // Calculate the bound for the inner loop as if the comparison is always done using indvar_next
    Value *which_indvar = exitcond_lhs;
    if (Instruction *inst = dyn_cast <Instruction>(which_indvar))
	if (inst->getOpcode() == Instruction::Trunc)
	    which_indvar = inst->getOperand(0);
    assert(which_indvar == indvar || which_indvar == indvar_next);
    if (which_indvar == indvar) 
	exitcond_final_rhs = builder.CreateAdd(exitcond_rhs, builder.getIntN(exitcond_rhs->getType()->getIntegerBitWidth(), 1));
    else 
	exitcond_final_rhs = exitcond_rhs;
    Value *remaining_trip_count = builder.CreateSub(builder.CreateSExtOrTrunc(exitcond_final_rhs, indvar->getType()), new_indvar);
    Value *new_loop_bound = builder.CreateSelect(builder.CreateICmpSLT(remaining_trip_count, const_tile_size), remaining_trip_count, const_tile_size);
    // Calculate the final RHS for the original exitcond. Final LHS has to be done later since indvar_next has not been defined
    new_loop_bound = builder.CreateSExtOrTrunc(new_loop_bound, exitcond_rhs->getType());
    // Create a terminator at the end of the outer loop header
    builder.SetInsertPoint(new_loop_header);
    builder.CreateBr(header);


    // Create the body for the outer loop body block
    builder.SetInsertPoint(new_loop_body);
    // Increase the induction variable of the outer loop
    new_indvar_next = builder.CreateAdd (new_indvar, const_tile_size, "new_indvar.next");
    // Create the exiting condition for the outer loop
    new_exitcond = builder.CreateICmpSGE(new_indvar_next, builder.CreateSExtOrTrunc(exitcond_final_rhs, indvar->getType()), "new_exitcond");
    // Create a terminator
    builder.CreateCondBr(new_exitcond, exit_block, new_loop_header);
    fwdref->replaceAllUsesWith(new_indvar_next); delete fwdref;


    //  Replace some of the uses of the original induction variable that need to keep the same value
    builder.SetInsertPoint(header->getFirstInsertionPt());
    Value *original_indvar = builder.CreateAdd(indvar, new_indvar);
    for (auto ui = affected_indvar_uses.begin(), ue = affected_indvar_uses.end(); ui != ue; ++ui) {
	Use * u = *ui;
	u->set(original_indvar);
    }

    // Modifiy the exiting condition to be the minimum of the remaining trip count and the tile size
    builder.SetInsertPoint(exitcond);
    // Always use indvar_next for comparison. Notice: the LHS of exit condition will be changed in previous steps in case it has multiple users. Therefore, this step has to be done at the last
    exitcond->setOperand(0, builder.CreateSExtOrTrunc(indvar_next, exitcond_lhs->getType()));
    // Use the calculated bound in the inner loop
    exitcond->setOperand(1, new_loop_bound);


    return std::make_tuple(new_indvar, new_loop_header, new_loop_body, new_loop_bound);
}


