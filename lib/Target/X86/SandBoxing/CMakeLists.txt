include_directories(
	${LLVM_MAIN_INCLUDE_DIR}/../lib/Target/X86
)

add_llvm_library(LLVMSandBoxing
	SandBoxing.cpp	
	ADDITIONAL_HEADER_DIRS
	${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms
	${LLVM_MAIN_INCLUDE_DIR}/../lib/Target/X86
	${LLVM_MAIN_INCLUDE_DIR}/../lib/Target/X86/SandBoxing
)

target_link_libraries(LLVMSandBoxing)
add_dependencies(LLVMSandBoxing intrinsics_gen)
