(* Definition of low-level model and semantics *)

Require Import Program Arith List.

Load Quorum.

(* Model *)

Record Message := MSG {m_round_no : nat; sender_id : nat; receiver_id : nat; vote : option bool}.

Record HonestNode := HLS {hl_round_no : nat; input : bool; estimation : nat -> option bool; history : nat -> nat -> option Message; decision : option bool}.

Inductive LocalState :=
| Honest (ls : HonestNode).

Record GlobalState := GS {round_no : nat; n : nat; f : nat; CQ : n_CoQuorum; local_states : nat -> option LocalState; undelivered : list Message}.

(* Semantics *)

Fixpoint testone' (n : nat) (st : nat -> bool) (h : nat -> option Message) (b : bool): option bool :=
  match n with
  | O => Some b
  | S n' => match st n' with
    | true => match h n' with
      | Some m => let v' := vote m in
        match v' with
        | Some b => testone' n' st h b
        | _ => None
        end 
      | None => None
      end
    | false => testone' n' st h b
    end
  end.

Fixpoint testone (n : nat) (st : nat -> bool) (h : nat -> option Message) : option bool :=
  match n with
  | O => None
  | S n' => match st n' with
    | true => match h n' with
      | Some m => let v := vote m in
        match v with
        | Some b => testone' n' st h b
        | None => None
        end
      | None => None
      end
    | false => testone n' st h
    end
  end.

(* The universe is [0..n-1], there are m quorums to test in sq, hr is the set of messages for the current round
   Returns some bool when there is a unaminous quorum
*)
Fixpoint testall (n : nat) (m : nat) (sq : nat -> (nat -> bool)) (h : nat -> option Message) : option bool :=
  match m with
  | O => None
  | S m' => match testone n (sq m') h with
    | Some b => Some b
    | None => testall n m' sq h
    end
  end.

Definition decide (n : nat) (cq : n_CoQuorum) (hr : nat -> option Message) := 
  match cq with
  | CO_Q m sq _ _ => testall n m sq hr
  end.

Definition estimate (n : nat) (cq : n_CoQuorum) (hr : nat -> option Message) := 
  match cq with
  | CO_Q _ _ k csq => testall n k csq hr
  end.

Definition step_round_loc (n : nat) (cq : n_CoQuorum) (ls : LocalState) : LocalState :=
  match ls with
  | Honest ls' => 
    let r := hl_round_no ls' in
    let b := input ls' in
    let e := estimation ls' in
    let h := history ls' in
    let d := decision ls' in
    Honest (HLS (r + 1) b (fun r' => if (r' =? r + 1) then (estimate n cq (h r)) else e r') h d)
  end.

Definition step_round (n : nat) (cq : n_CoQuorum) (lss : nat -> option LocalState) :=
  fun (i : nat) => 
    match (lss i) with
    | Some ls => Some (step_round_loc n cq  ls)
    | None => None
    end.

Definition step_message_from_to (ls : LocalState) (source : nat) (dest : nat) : Message :=
  match ls with
  | Honest ls' => let r := hl_round_no ls' in
    MSG r source dest (estimation ls' r)
  end.

Definition step_message_from (n : nat) (lss : nat -> option LocalState) (source : nat) :=
  match (lss source) with
  | Some ls => map (step_message_from_to ls source) (seq 0 n)
  | None => []
  end.

Definition step_message (n : nat) (lss : nat -> option LocalState) : list Message :=
  flat_map (step_message_from n lss)(seq 0 n).

Definition step_deliver_loc (n : nat) (cq : n_CoQuorum) (ls : LocalState) (m : Message) : LocalState := 
  let rm := m_round_no m in
  let sender_id := sender_id m in
    match ls with
    | Honest ls' => 
      let r := hl_round_no ls' in
      let b := input ls' in
      let e := estimation ls' in
      let h := history ls' in
      let d := decision ls' in
      let nh := (match h rm sender_id with
        | Some _ => h
        | None => (fun r' s' => (if (andb (r' =? rm) (s' =? sender_id)) then Some m else (h r' s')))
        end) in
      match d with
      | Some _ => Honest (HLS r b e nh d)
      | None => Honest (HLS r b e nh (decide n cq (nh r)))
      end
    end.

Definition step_deliver (n : nat) (cq : n_CoQuorum) (lss : nat -> option LocalState) (m : Message) :=
  fun (i : nat) =>
    let receiver := receiver_id m in
    if (i =? receiver) then 
        match (lss receiver) with
        | Some ls => Some (step_deliver_loc n cq ls m)
        | None => None
        end
    else lss i.

Definition step (gs : GlobalState) : GlobalState :=
  let r := round_no gs in
  let n := n gs in
  let f := f gs in
  let cq := CQ gs in
  let lss := local_states gs in
  let msg := undelivered gs in
    match msg with
    | nil => let nlss := step_round n cq lss in 
        GS (r + 1) n f cq nlss (step_message n nlss)
    | m :: msg' => GS r n f cq (step_deliver n cq lss m) msg'
    end.

Inductive Step : GlobalState -> GlobalState -> Prop :=
  | ONE : forall gs gs', (gs' = step gs) -> Step gs gs'.

Inductive Steps : GlobalState -> GlobalState -> Prop :=
  | ZERO : forall gs gs', gs = gs' -> Steps gs gs'
  | MANY : forall gs gs' gs'', Steps gs gs' /\ Step gs' gs'' -> Steps gs gs''.

(* Initial value & validity *)

Record InitialParams := InitP {inputs : nat -> bool; numf : nat; coq_cq : n_CoQuorum}.

Definition initLS (i : nat) (b : bool) :=
  Honest (HLS 0 b (fun r => None) (fun r j => None) None).

Definition f_to_n f := 5 * f + 1.

Definition initGS (params : InitialParams) :=
  let input := inputs params in
  let f := numf params in 
  let cq := coq_cq params in
  let n := f_to_n f in
  GS 0 n f cq (fun i => if (i <? n) then Some (initLS i (input i)) else None) [].

Definition isValid (params : InitialParams) (gs : GlobalState) :=
  n_CoQuorum_valid (coq_cq params) (f_to_n (numf params)) /\ Steps (initGS params) gs.

(* TODO use monads to abstract the low-level semantics for later updates 
  With the non-deter monads, we can let the steps go non-deterly for advers
  Or param with input by giving extra input

  e.g.
  Stream A := nat x ( nat -> A) 
  or co-induction 
  forall f, Stream A f ...
*)
