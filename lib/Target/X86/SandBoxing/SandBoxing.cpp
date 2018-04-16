#include "X86.h"
#include "X86FrameLowering.h"
#include "X86InstrBuilder.h"
#include "X86InstrInfo.h"
#include "X86MachineFunctionInfo.h"
#include "X86Subtarget.h"
#include "llvm/Analysis/EHPersonalities.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/Passes.h" // For IDs of passes that are preserved.
#include "llvm/IR/GlobalValue.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/MC/MCInstrDesc.h"


#include <bits/stdc++.h>

using namespace llvm;

#define DEBUG_SANDBOXING(command)


cl::opt<bool> SandBoxLoads("sandbox-loads", cl::desc("Insert sand boxing checks for loads"), cl::value_desc("bool"));
cl::opt<bool> SandBoxStores("sandbox-stores", cl::desc("Insert sand boxing checks for stores"), cl::value_desc("bool"));
cl::opt<bool> InstrumentSandboxingCFI("instrument-sandbox-cfi", cl::desc("Insert CFI instrumentation for sandboxing"), cl::value_desc("bool"));

/*typedef struct {
	int base_register;
	int index_register;
	int stride;
} mem_operand_struct;
*/


typedef std::tuple<int, int, int> mem_operand_struct;
typedef std::set<mem_operand_struct> register_cache_type;

namespace {

	class DummyPass : public MachineFunctionPass {
		public: 
			static char ID;
			DummyPass() : MachineFunctionPass(ID) {}
			bool runOnMachineFunction(MachineFunction &MF) {
				return false;
			}
		
	};

	class SandBoxingPass : public MachineFunctionPass {
		public:
			static char ID;
			SandBoxingPass() : MachineFunctionPass(ID) {}

			int getMemLocation(const MachineInstr *MI) {
				int i = 0;
				for (auto MO = MI->getDesc().OpInfo; MO != NULL; MO++){
					if (MO->OperandType == MCOI::OPERAND_MEMORY)
						return i;
					i++;
				}
				return -1;
			}
			int isPush(const MachineInstr &MI) {
				switch(MI.getOpcode()) {
					case X86::PUSH64r:
						return 1;
					default:
						return 0;
				}
				return 0;
			}
			int isPop(const MachineInstr &MI) {
				switch(MI.getOpcode()) {
					case X86::POP64r:
						return 1;
					default:
						return 0;
				}
				return 0;
			}

			int updateRegisterCache(const MachineInstr &MI, register_cache_type &register_cache) {
				if (MI.isCall()){
					register_cache.clear();
					return 0;
				}
				if (isPush(MI) || isPop(MI))
					return 0;
				for(register_cache_type::iterator mem_operand = register_cache.begin(); mem_operand != register_cache.end(); mem_operand++){
					int base_register = std::get<0>(*mem_operand);
					int index_register = std::get<1>(*mem_operand);
					if(MI.definesRegister(base_register) || (index_register != X86::NoRegister && MI.definesRegister(index_register))){
						register_cache.erase(mem_operand);	
					}
				}
				return 0;
			}
			int insertBoundCheckBeforeInstruction(MachineInstr &MI, register_cache_type &register_cache) {
				const TargetInstrInfo *TII;
				const X86Subtarget *STI;
				STI = &MI.getParent()->getParent()->getSubtarget<X86Subtarget>();
				TII = STI->getInstrInfo();
				MachineBasicBlock::iterator BNDL;
				MachineBasicBlock::iterator BNDU;
				mem_operand_struct mem_operand;
				if(isPush(MI) || isPop(MI)) {
					std::get<0>(mem_operand) = X86::RSP;
					std::get<1>(mem_operand) = X86::NoRegister;
					std::get<2>(mem_operand) = 1;
					if (register_cache.find(mem_operand) != register_cache.end())
						return 1;
					BNDL = BuildMI(*(MI.getParent()), &MI, MI.getDebugLoc(), TII->get(X86::BNDCL64rr), X86::BND0).addReg(X86::RSP);
					BNDU = BuildMI(*(MI.getParent()), &MI, MI.getDebugLoc(), TII->get(X86::BNDCU64rr), X86::BND0).addReg(X86::RSP);
					register_cache.insert(mem_operand);
				}else{
					int mem_index = getMemLocation(&MI);
					if (mem_index == -1) {
						errs() << "No mem operand for \n";
						MI.print(errs());
						return -1;
					}
					if (MI.getOperand(2 + mem_index).getReg() == X86::NoRegister){
						if (MI.getOperand(0 + mem_index).getReg() == X86::NoRegister)
							return 1;
						std::get<0>(mem_operand) = MI.getOperand(0 + mem_index).getReg();
						std::get<1>(mem_operand) = X86::NoRegister;
						std::get<2>(mem_operand) = 1;
						if (register_cache.find(mem_operand) != register_cache.end())
							return 1;
						BNDL = BuildMI(*(MI.getParent()), &MI, MI.getDebugLoc(), TII->get(X86::BNDCL64rr), X86::BND0).addReg(MI.getOperand(0 + mem_index).getReg());
						BNDU = BuildMI(*(MI.getParent()), &MI, MI.getDebugLoc(), TII->get(X86::BNDCU64rr), X86::BND0).addReg(MI.getOperand(0 + mem_index).getReg());	
						register_cache.insert(mem_operand);
					} else {
						std::get<0>(mem_operand) = MI.getOperand(0 + mem_index).getReg();
						std::get<1>(mem_operand) = MI.getOperand(2 + mem_index).getReg();
						std::get<2>(mem_operand) = MI.getOperand(1 + mem_index).getImm();
						if (register_cache.find(mem_operand) != register_cache.end())
							return 1;
						BNDL = BuildMI(*(MI.getParent()), &MI, MI.getDebugLoc(), TII->get(X86::BNDCL64rm), X86::BND0).add(MI.getOperand(0 + mem_index)).add(MI.getOperand(1 + mem_index)).add(MI.getOperand(2 + mem_index)).add(MI.getOperand(3 + mem_index)).add(MI.getOperand(4 + mem_index));
						BNDU = BuildMI(*(MI.getParent()), &MI, MI.getDebugLoc(), TII->get(X86::BNDCL64rm), X86::BND0).add(MI.getOperand(0 + mem_index)).add(MI.getOperand(1 + mem_index)).add(MI.getOperand(2 + mem_index)).add(MI.getOperand(3 + mem_index)).add(MI.getOperand(4 + mem_index));
						register_cache.insert(mem_operand);
					}
				}
				return 0;
			}

			bool addBoundChecks(MachineFunction &MF) {
				DEBUG_SANDBOXING(errs () << "Running on function " << MF.getName().str() << "\n");
				for (MachineFunction::iterator BasicBlockIterator = MF.begin(); BasicBlockIterator != MF.end(); BasicBlockIterator++ ) {
					register_cache_type register_cache;
					for(MachineBasicBlock::iterator MachineInstructionIterator = BasicBlockIterator->begin(); MachineInstructionIterator != BasicBlockIterator->end(); MachineInstructionIterator++) {
						MachineInstr &MI = *MachineInstructionIterator;
						DEBUG_SANDBOXING(MI.print(errs()));
						DEBUG_SANDBOXING(errs() << "\n");
						if (MI.mayLoadOrStore()) {
							if ((SandBoxStores && MI.mayStore()) || (SandBoxLoads && MI.mayLoad())) {
								insertBoundCheckBeforeInstruction(MI, register_cache);
							}
						}
						
						updateRegisterCache(MI, register_cache);
					}

				}
				return true;
			}
			bool runOnMachineFunction(MachineFunction &MF) {
				addBoundChecks(MF);
				return 0;
			}
	};
}

char SandBoxingPass::ID = 0;
char DummyPass::ID = 0;

FunctionPass *llvm::createSandBoxingPass() {
	return new SandBoxingPass();
}
FunctionPass *llvm::createDummyPass() {
	return new DummyPass();
}
