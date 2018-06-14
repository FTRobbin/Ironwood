# Project Ironwood (Work In Progress)
---
A correct-by-construction blockchain protocol implmentation.

## How to run
The author's version is [Coq 8.7.1](https://github.com/coq/coq/releases/tag/V8.7.1). To complie/check, run `make clean; make`.

## Roadmap
* [Version 1](https://github.com/FTRobbin/Ironwood) [DONE]
  * Synchornous network
  * No adversaries
  * Concensus on a boolean value
  * Implmenting [BOSCO](https://pdfs.semanticscholar.org/3958/98b44d23be8d0227d403ec7928391880e79f.pdf) concensus protocol
  * Proving agreement property: all decisions made are the equal
  * Not executable
* Next steps:
  * Improving proof code quality
  * Add crash/Byzantine adversaries
  * Asynchronous network
  * Liveness prorperty
  * More complex protocol
  * Extract to executables

## Proof organization
| File | Description |
| --- | --- |
| Assumption.v | Assumptions |
| High_def.v | Abstract protocol semantics |
| High_proof.v | Abstract agreement proof |
| Low_def.v | Protocol implmentation, basic properties |
| Low_proof.v | Agreement proof |
| Quorum.v | Quorum abstraction |
| Refinement.v | Refinement theorem (and all the lemmas)|
| Temporal.v | (A not so successful atempt) to adopt temporal logic |

The core theorem is `Refinement` in `Refinement.v`, it relies solely on lemma `coreCase` which is decomposed into a handful of smaller lemmas. These lesser lemmas are built top-down. They form a tree-like structure rooting from the `coreCase`, which are named recursively in the form of `CoreX_Y_Z_...` means it is the `Z`-th lemma to support lemma `CoreX_Y`. Though some lemmas are moved around and reused in other places.

---
Haobin Ni, Cornell University, 2018
