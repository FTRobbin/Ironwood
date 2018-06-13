(* Theorems about low level protocol *)

Require Import Program.

Require Import Refinement Temporal Low_def High_proof.

Theorem Low_Level_Agreement : forall params, isValidP params -> Always (compose agree ref_map) (initGS params).
Proof.
  unfold Always.
  intros.
  unfold compose.
  eapply (HAgreement (ref_mapp params)).
  eapply Refinement'.
  unfold isValid.
  auto.
Qed.