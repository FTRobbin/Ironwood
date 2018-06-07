# Project Ironwood (Work In Progress)
---
A correct-by-construction blockchain protocol implmentation.

## How to run
The author's version is [Coq 8.7.1](https://github.com/coq/coq/releases/tag/V8.7.1). To complie/check, run `coqc Low_proof.v`.

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

## File structure
| Assumption.v |  |
| High_def.v | High-level protocol semantics |
| High_proof.v | High-level agreement proof |
| Low_def.v | Low-level protocol semantics, Low-level state properties |
| Low_proof.v | Low-level agreement proof |
| Quorum.v | Quorum abstraction |
| Refinement.v | Proof of the refinement theorem |
| Temporal.v | (Not so successful atempt) to adopt temporal logic |

## Proof organization
`Low_def.v` contains the protocol, `Low_Level_Monotonicity` and `Low_Level_Witness`.

`Refinement.v` contains almost all the proof code. The core theorem is `Refinement`, it relies solely on lemma `coreCase` which is decomposed into a handful of smaller lemmas. These lesser lemmas are built top-down. They form a tree-like structure rooting from the `coreCase`, which are named recursively in the form of `CoreX_Y_Z_...` means it is the `Z`-th lemma to support lemma `CoreX_Y`. Though some lemmas are moved around and reused in other places.

---
Haobin Ni, Cornell University, 2018
