(* Definition of low-level model and semantics *)

Require Import Program Arith List.

Load Quorum.
Load Temporal.

(* Model *)

Record Message := MSG {sender_id : nat; receiver_id : nat; m_round_no : nat; vote : option bool}.

Record HonestNode := HLS {hl_round_no : nat; input : bool; estimation : nat -> option bool; history : nat -> nat -> option Message; decision : option bool}.

Inductive LocalState :=
| Honest (ls : HonestNode).

Record GlobalState := GS {round_no : nat; n : nat; f : nat; CQ : n_CoQuorum; local_states : nat -> option LocalState; 
                          message_archive : nat -> nat -> nat -> option Message; delivered : nat -> nat -> nat -> bool}.

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

Definition step_message (n : nat) (lss : nat -> option LocalState) : nat -> nat -> option Message :=
  fun i j => match (lss i) with
  | None => None
  | Some ls => Some (step_message_from_to ls i j)
  end.

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

Definition d1_map {A : Type} (n : nat) (m : nat -> nat -> A) : nat -> list A :=
  fun i => map (m i) (seq 0 n).

Definition d2_map {A : Type} (n : nat) (m : nat -> nat -> A) : list A :=
  flat_map (d1_map n m) (seq 0 n).

Fixpoint ext_first {A : Type} (l : list (option A)) (r : list bool) : option A :=
  match (l, r) with
  | (nil, _) => None
  | (_, nil) => None
  | (h :: t, h' :: t') =>
    if (h') then h else ext_first t t'
  end.

Definition get_undelivered (n : nat) (msg : nat -> nat -> option Message) (d : nat -> nat -> bool) :=
  let msg_list := d2_map n msg in
  let flag_list := d2_map n d in
  ext_first msg_list flag_list.

Definition update_messages (r : nat) (msg : nat -> nat -> nat -> option Message) (nmsg : nat -> nat -> option Message) :=
  fun r' i j => if (r' =? r) then (nmsg i j) else msg r' i j.

Definition update_delivered (r : nat) (d : nat -> nat -> nat -> bool) (m : Message) :=
  fun r' i' j' => match m with
  | MSG i j _ _ => if (andb (andb (r' =? r) (i' =? i)) (j' =? j)) then true else (d r' i' j')
  end.

Definition step (gs : GlobalState) : GlobalState :=
  let r := round_no gs in
  let n := n gs in
  let f := f gs in
  let cq := CQ gs in
  let lss := local_states gs in
  let msgs := message_archive gs in
  let d := delivered gs in
  let m' := get_undelivered n (msgs r) (d r) in
  match m' with
  | None => let nlss := step_round n cq lss in
            let nmsg := step_message n nlss in
      GS (r + 1) n f cq nlss (update_messages r msgs nmsg) d
  | Some m => GS r n f cq (step_deliver n cq lss m) msgs (update_delivered r d m)
  end.

(*
Inductive Step : GlobalState -> GlobalState -> Prop :=
  | ONE : forall gs gs', (gs' = step gs) -> Step gs gs'.

Inductive Steps : GlobalState -> GlobalState -> Prop :=
  | ZERO : forall gs gs', gs = gs' -> Steps gs gs'
  | MANY : forall gs gs' gs'', Steps gs gs' /\ Step gs' gs'' -> Steps gs gs''.
*)

(* Initial value & validity *)

Record InitialParams := InitP {inputs : nat -> bool; numf : nat; coq_cq : n_CoQuorum}.

Definition initLS (i : nat) (b : bool) :=
  Honest (HLS 0 b (fun r => if (r =? 0) then Some b else None) (fun r j => None) None).

Definition f_to_n f := 5 * f + 1.

Definition initGS (params : InitialParams) :=
  let input := inputs params in
  let f := numf params in 
  let cq := coq_cq params in
  let n := f_to_n f in
  GS 0 n f cq (fun i => if (i <? n) then Some (initLS i (input i)) else None) (fun r i j => None) (fun r i j => false).


(* TODO use monads to abstract the low-level semantics for later updates 
  With the non-deter monads, we can let the steps go non-deterly for advers
  Or param with input by giving extra input

  e.g.
  Stream A := nat x ( nat -> A) 
  or co-induction 
  forall f, Stream A f ...
*)

Inductive Low_leq : GlobalState -> GlobalState -> Prop :=
| Zero : forall s, Low_leq s s
| Many : forall s s', Low_leq s s' -> Low_leq s (step s').

Instance LowState : @State GlobalState Low_leq step := {}.
  constructor.
  intro ; eapply (Many s s) ; constructor.
  intros.
  induction H0.
  auto.
  eapply (Many s s').
  auto.
Defined.

Notation "A <<= B" := (Low_leq A B) (at level 80).

Definition isValidP (params : InitialParams) :=
  n_CoQuorum_valid (coq_cq params) (f_to_n (numf params)).

Definition isValid (params : InitialParams) (gs : GlobalState) :=
  isValidP params /\ (initGS params) <<= gs.

(*
Record HonestNode := HLS {hl_round_no : nat; input : bool; estimation : nat -> option bool; history : nat -> nat -> option Message; decision : option bool}.

Record GlobalState := GS {round_no : nat; n : nat; f : nat; CQ : n_CoQuorum; local_states : nat -> option LocalState; 
                          message_archive : nat -> nat -> nat -> option Message; delivered : nat -> nat -> nat -> bool}.
*)

Definition LowL_mono : LocalState -> LocalState -> Prop :=
  fun lls lls' =>
  match (lls, lls') with
  | (Honest ls, Honest ls') => 
    (hl_round_no ls) <= (hl_round_no ls') /\
    (input ls) = (input ls') /\
    (forall i b, ((estimation ls) i) = Some b -> ((estimation ls') i) = Some b) /\
    (forall i j m, (history ls i j) = Some m -> (history ls' i j) = Some m) /\
    (forall b, (decision ls) = Some b -> (decision ls') = Some b)
  end.

Definition Low_mono : GlobalState -> GlobalState -> Prop :=
  fun gs gs' =>
  (round_no gs) <= (round_no gs') /\
  (n gs) = (n gs') /\
  (f gs) = (f gs') /\
  (CQ gs) = (CQ gs') /\
  (forall i ls, ((local_states gs) i) = Some ls -> (exists ls', (local_states gs') i = Some ls' /\ (LowL_mono ls ls'))) /\
  (forall i j k m, (message_archive gs i j k) = Some m -> (message_archive gs' i j k) = Some m) /\
  (forall i j k, (delivered gs i j k) = true -> (delivered gs' i j k) = true).

Notation "A <== B" := (Low_mono A B) (at level 80).

(* Monotonicity & Witness *)

(* Medium *)
Theorem Low_Level_Monotonicity : forall s s', (s <<= s') -> (s <== s').
Proof.
Admitted.

(* Medium *)
(* TODO To write the witness as a function *)
Theorem Low_Level_Witness : forall (A : Type) s s' (f : GlobalState -> A), (s <<= s') -> (f s <> f s') -> (exists s'', s <<= s'' /\ (step s'') <<= s' /\ (f s = f s'') /\ (f s <> f (step s''))).
Proof.
Admitted.
