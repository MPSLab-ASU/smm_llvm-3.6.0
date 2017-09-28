#define DEBUG_TYPE "printstacksize"
#include "X86.h"
#include "llvm/Pass.h"
//#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineFrameInfo.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/Support/raw_ostream.h"
using namespace llvm;
namespace {
    class StackSizePass : public MachineFunctionPass {
	public:
	    static char ID;
	    StackSizePass() : MachineFunctionPass(ID) {}
	    virtual bool runOnMachineFunction(MachineFunction &mf) {
		errs() << mf.getName() << " " << mf.getFrameInfo()->getStackSize() << "\n";
		return false;
	    }
    };
}

FunctionPass *llvm::createPrintStackSizePass() {
    return new StackSizePass();
}
char StackSizePass::ID = 0;
static RegisterPass<StackSizePass> X("printstacksize", "Print Estimated Stack Frame Size");
