TODO:
1. The programmer should be able to read C0/C1 programs and emit a new Boole file translation
2. The programmer should be able to inline C0/C1 programs in Lean files and emit a Boole translation
3. The programmer should be able to inline C0/C1 programs in Lean files, then reason about the Boole program
4. Not sure how this would work in its entirety, but maybe the programmer can inline C0/C1 programs in Lean files, and then reason directly about the annotations, which translate back down to Boole (?) In other words, goals are lifted up to C0, proved under C0 semantics, and then projected back down to Boole.
5. Since there is no dedicated compiler for C0, it may be worthwhile emitting LLVM IR such that programs can be tested and ran.
6. One of the end goals may be: prove the translations hold! I.e., obligations/annotations proven to be true in Boole => these hold also in C0
    -  this means we can do pretty interesting things, no? We can make proving obligations easier by having our elaboration stage elaborate away unrelated proof material, which makes it easier for statements to be shown true/false in Boole, and the translation correctness theorem gives you Boole Correctness => Elaborated C0 correctness => C0 correctness for free

Compiler name: c0vc (C0 verified compiler).
