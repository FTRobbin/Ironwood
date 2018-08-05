# Project Ironwood (Work In Progress)
---
A correct-by-construction blockchain protocol implmentation.

## How to run
The author's version is [Coq 8.8.0](https://github.com/coq/coq/releases/tag/V8.8.0). To complie/check, run `make clean; make`.

## Roadmap
* Version 2.0 [In progress]
  * Add Byzantine adversaries

* [Version 1.1](https://github.com/FTRobbin/Ironwood/releases/tag/V1.1) [DONE]
  * Sensible names for lemmas
  * Improved proof structure and implementation
  * Human-readable high-level proof

* [Version 1.0](https://github.com/FTRobbin/Ironwood/releases/tag/V1.0) [DONE]
  * Synchornous network
  * No adversaries
  * Concensus on a boolean value
  * Implmenting [BOSCO](https://pdfs.semanticscholar.org/3958/98b44d23be8d0227d403ec7928391880e79f.pdf) concensus protocol
  * Proving agreement property: all decisions made are the equal
  * Not executable

* Future steps:
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
| Low_proof.v | Agreement proof + readable version |
| Quorum.v | Quorum abstraction |
| Refinement.v | Refinement theorem (and all the lemmas)|
| Temporal.v | (A not so successful atempt) to adopt temporal logic |

The core theorem is `Refinement` in `Refinement.v` or you can try read the pretty proof `Readable_Low_Level_Agreement` in `Low_proof.v` which comes with comments that serves as a pen-and-paper proof.

## Lemma naming

The lemmas in `Refinement.v` are ordered logically and named based on their forms. Different letters refers to properties about different formal concepts. Here's the reference list:

```
   V  = Validity
   S' = Step
   S  = Steps
   D  = Decision
   E  = Estimate
   R  = Round
   H  = History
   M  = Message
   L  = deLivery
   T  = sTate
   C  = Condition
   Q  = Quorum
   I  = Initial
   _  = Arrow
   c? = exact step ? changed
   l? = local ?
   g? = global ?
   ?p = ?'s properties
   eq = equality
```

For example, `Lem_VR_E` resembles a lemma that assumes validity of the global state and some constrains on the round number and concludes something about estimation.

```coq
Lemma Lem_VR_E : forall params gs r i, isValid params gs -> r <= round_no gs -> i < n gs -> exists b, extract_estimationr i gs r = Some b.
```

---
[Haobin Ni](https://github.com/FTRobbin), Cornell University, 2018
