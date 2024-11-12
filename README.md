# sec_comp_lift

This is the Coq code for the paper Do You Even Lift? Strengthening Compiler Security Guarantees Against Spectre Attacks that appears at POPL 2025.

Defining Definitions used in the paper.
The goal is to prove the meta theoretic properties we define and the corollaries we devise.
Especially for our lifting theorem.

These include the notions of for example:
- Independence
- Safe Nesting
- Trapped Speculation

and the base notions of RSS and SNI etc.

The development is known to compile with Coq 8.18.0.
Generate the Makefile from the _CoqProject file using
```
coq_makefile -f _CoqProject -o CoqMakefile
```
and then
```
make -f CoqMakefile
```

Note that Lemma 1 (Syn. Independence implies Independence) is not proven and we do not claim it to be.