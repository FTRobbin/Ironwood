(* Definition for quorum used in BOSCO *)

Record n_Quorum := Q {q_n : nat; q_m : nat; sq : nat -> (nat -> bool)}.

Definition n_Quorum_valid (q : n_Quorum) :=
  let n := q_n q in
  let m := q_m q in
  let sq := sq q in
  (forall i j, i < m -> j < m -> (exists k, k < n /\ (sq i k) = true /\ (sq j k) = true)).
  
Record n_CoQuorum := CO_Q {coq_m : nat; coq_sq : nat -> (nat -> bool); coq_k : nat; coq_csq : nat -> (nat -> bool)}.

Definition n_CoQuorum_valid (cq : n_CoQuorum) (n : nat) :=
  let m := coq_m cq in
  let sq := coq_sq cq in
  let k := coq_k cq in
  let csq := coq_csq cq in
  n_Quorum_valid (Q n m sq) /\
  (forall i j, i < m -> j < k -> (exists t, t < n /\ (sq i t) = true /\ (csq j k) = true)).