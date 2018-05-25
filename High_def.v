(* Definition of high-level semantics *)

Require Import Program Arith.

(* Model *)

Record HLocalState := HHonest {hhl_input : bool; hhl_decision : option bool}.

Record HGlobalState := HGS {hg_n : nat; h_localstates : nat -> option HLocalState}.

(* Semantics *)

Definition Hstep_decide_loc (ls : HLocalState) (b : bool) : HLocalState :=
  HHonest (hhl_input ls) (Some b).

Definition Hstep_decide (gs : HGlobalState) (i : nat) (b : bool) : HGlobalState :=
  let n := hg_n gs in
  let ls := h_localstates gs in
  HGS n 
    (fun j => 
    if j =? i then 
      match ls i with
      | Some ls => Some (Hstep_decide_loc ls b)
      | None => None
      end
    else
      ls j).

Definition Hextract_loc (ls : option HLocalState) : option bool :=
  match ls with
  | Some (HHonest _ d) => d
  | _ => None
  end.

Definition mergeb (l : option bool) (r : option bool) : option bool :=
  match l with
  | Some b => Some b
  | None => r
  end.

Definition Hextract (gs : HGlobalState) (i : nat) : option bool :=
  match gs with
  | HGS n ls => if i <? n then Hextract_loc (ls i) else None
  end.

(* TODO Hide behind a monad, so it can be written as a fun *)
Inductive HStep : HGlobalState -> HGlobalState -> Prop :=
  | NOTHING : forall gs, HStep gs gs
  | DECIDE : forall gs i b gs', ((forall j, Hextract gs j = None) /\ (gs' = Hstep_decide gs i b)) -> HStep gs gs'
  | AGREE : forall gs i b gs', ((exists j, Hextract gs j = Some b) /\ (gs' = Hstep_decide gs i b)) -> HStep gs gs'.

Inductive HSteps : HGlobalState -> HGlobalState -> Prop :=
  | HONE : forall gs gs', HStep gs gs' -> HSteps gs gs'
  | HMANY : forall gs gs' gs'', HSteps gs gs' -> HStep gs' gs'' -> HSteps gs gs''.
