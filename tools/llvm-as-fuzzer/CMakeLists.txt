set(LLVM_LINK_COMPONENTS
    AsmParser
    BitWriter
    Core
    Support
)
add_llvm_fuzzer(llvm-as-fuzzer llvm-as-fuzzer.cpp)
