(* Definition for quorum used in BOSCO *)

Inductive n_Quorum :=
| Q (n : nat) (m : nat) (sq : nat -> (nat -> bool)).

Definition n_Quorum_valid (q : n_Quorum) :=
  match q with
  | Q n m sq => (forall i j, i < m -> j < m -> (exists k, k < n -> (sq i k) = true /\ (sq j k) = true)) -> True
  end.

Inductive n_CoQuorum :=
| CO_Q (m : nat) (sq : nat -> (nat -> bool)) (k : nat) (csq : nat -> (nat -> bool)).

Definition n_CoQuorum_valid (cq : n_CoQuorum) (n : nat) :=
  match cq with
  | CO_Q m sq k csq => (n_Quorum_valid (Q n m sq)) ->
          (forall i j, i < m -> j < k -> (exists t, t < n -> (sq i t) = true /\ (csq j k) = true)) -> True
  end.
