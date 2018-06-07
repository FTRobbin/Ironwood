(* Definition for quorum used in BOSCO *)

Record n_Quorum := Q {q_n : nat; q_m : nat; sq : nat -> (nat -> bool)}.

Definition n_Quorum_valid (q : n_Quorum) :=
  let n := q_n q in
  let m := q_m q in
  let sq := sq q in
  (forall i j, i < m -> j < m -> (exists k, k < n /\ (sq i k) = true /\ (sq j k) = true)).


Fixpoint check_quorum_infer' (n : nat) (q : nat -> bool) (b : nat -> bool) :=
  match n with
  | O => true
  | S n' => if (q n') then (if b n' then check_quorum_infer' n' q b else false) else check_quorum_infer' n' q b
  end.

Definition check_quorum_infer (n : nat) (q : nat -> bool) (b : nat -> option bool) :=
  let bt := (fun i => match b i with | Some true => true | _ => false end ) in
  let bf := (fun i => match b i with | Some false => true | _ => false end) in
  match (check_quorum_infer' n q bt, check_quorum_infer' n q bf) with
  | (true, false) => Some true
  | (false, true) => Some false
  | _ => None
  end.

Record n_CoQuorum := CO_Q {coq_m : nat; coq_sq : nat -> (nat -> bool); coq_k : nat; coq_csq : nat -> (nat -> bool)}.

Definition n_CoQuorum_valid (cq : n_CoQuorum) (n : nat) (exist_cond : nat -> (nat -> option bool) -> Prop) :=
  let m := coq_m cq in
  let sq := coq_sq cq in
  let k := coq_k cq in
  let csq := coq_csq cq in
  (forall s, exist_cond n s -> exists j b0 t, j < k /\ check_quorum_infer n (csq j) s = Some b0 /\ t < n /\ (csq j t) = true) /\
  n_Quorum_valid (Q n m sq) /\
  (forall i j, i < m -> j < k -> (exists t, t < n /\ (sq i t) = true /\ (csq j t) = true)).