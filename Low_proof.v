(* Theorems about low level protocol *)

Require Import Program.

Load Refinement.

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