## Formal Reasoning About Bernstein-Vazirani Algorithm
  This repository contains the fully-formal model and verification of the Bernstein–Vazirani algorithm carried out in the HOL Light theorem prover.
  Beyond the core proof, the project demonstrates practical impact by instantiating the verified algorithm in two realistic settings:
1. Quantum-key-distribution (QKD) error-correction
2. Quantum image encryption / decryption
All proofs are machine-checked; no axioms beyond standard HOL Light are required.
## Dependencies  
To run this library, please make sure the following dependencies are installed:
- **Multivariate/transcendentals.ml**: Contains transcendental functions relevant to multivariate analysis.
- **Multivariate/cross.ml**: Provides cross product operations and related computations.
- **Multivariate/realanalysis.ml**: Offers real analysis functions and utilities.
- **Library/grouptheory.ml**: Supplies group theory-related library functions.
- **Multivariate/cvectors.ml**: Real vectors in Euclidean space, and elementary linear algebra.
- **Multivariate/vectors.ml**: Real vectors in Euclidean space, and elementary linear algebra.
- **Library/binary.ml**: Implements binary arithmetic operations.
- **Library/words.ml**: Primarily used for the representation and manipulation of binary words.

## Quick Start
Prerequisites
- **OCaml ≥ 4.10**
- **HOL Light (latest Git snapshot)**
- **Install instructions: https://hol-light.github.io/**
Running the Formal Proofs
- **cd hol-light**
   - **ledit ocaml**
  - **#use "hol.ml";;**
  - **loads "Bernstein-Vazirani.ml";;**
