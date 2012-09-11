MPI-Type-checker
================

A program build as a clang plugin in order to enhance communication safety of MPI programs. This is performed by extracting the MPI primitives and the language constructs from a given source code. Following that a global protocol given to the program will be projected into local protocols. The type checker checks the conformance between the trees generated from the extractor and the trees representing their corresponding local protocols. If type checking is successful then the communication safety is preserved. Otherwise, the type checker will print the trees showing the errors found.

Installation:
- Install LLVM
- Install clang which is part of LLVM
- Compile Session C source files
- Compile MPI Type checker

Program runs using the following command from a terminal:

clang -Xclang -load -Xclang /llvm/Debug+Asserts/lib/libclang.so -Xclang -load -Xclang /llvm/Debug+Asserts/lib/libMPITypeChecker.so -Xclang -add-plugin -Xclang mpi-type-check -Xclang -plugin-arg-mpi-type-check -Xclang "Put number of processors here" -Xclang -plugin-arg-mpi-type-check -Xclang "Global protocol location path here" -I sessionC/include "MPI cource file location path here" -I /usr/include

Note: Quotes in the command above are only for demonstration purposes.
    