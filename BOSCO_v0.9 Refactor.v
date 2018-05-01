(* Formalization of BOSCO consensus protocol *)

(* Version 1: Synchornous, No adversary *)

(* Refactored v0.9 *)

Require Import Program List Bool Arith Omega Lia CpdtTactics PeanoNat.

Axiom fun_eqiv : forall {A: Type} {B: Type} (f : A -> B) (g : A -> B), (forall (x : A), f x = g x) -> f = g.

Section Quorum.

(* Cannot find a suitable finite set library to use here *)

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

End Quorum.

Section Low_level.

Section Model.

Record Message := MSG {m_round_no : nat; sender_id : nat; receiver_id : nat; vote : option bool}.

Record HonestNode := HLS {hl_round_no : nat; input : bool; estimation : nat -> option bool; history : nat -> nat -> option Message; decision : option bool}.

Inductive LocalState :=
| Honest (ls : HonestNode).

Record GlobalState := GS {round_no : nat; n : nat; f : nat; CQ : n_CoQuorum; local_states : nat -> option LocalState; undelivered : list Message}.

End Model.

Section Semantics.

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

End Semantics.

End Low_level.

Section High_level.

Section Model.

Record HLocalState := HHonest {hhl_input : bool; hhl_decision : option bool}.

Record HGlobalState := HGS {hg_n : nat; h_localstates : nat -> option HLocalState}.

End Model.

Section Semantics.

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

End Semantics.

Section Agreement.

Definition agree' (bi : option bool) (bj : option bool) : Prop :=
  match bi, bj with
  | Some bi, Some bj => bi = bj
  | _, _ => True
  end.

Definition agree (gs : HGlobalState) : Prop := forall i j, agree' (Hextract gs i) (Hextract gs j).

Record HInitialParams := HInitP {h_inputs : nat -> bool; h_n : nat}.

Definition HinitLS (b : bool) :=
  HHonest b None.

Definition HinitGS (params : HInitialParams) :=
  let input := h_inputs params in
  let n := h_n params in
  HGS n (fun i => if (i <? n) then Some (HinitLS (input i)) else None).

Definition HisValid (params : HInitialParams) (gs : HGlobalState) :=
  HSteps (HinitGS params) gs.

Lemma Hextract_agree : forall gs b, (exists i, Hextract gs i = Some b) -> agree gs -> (forall i, agree' (Hextract gs i) (Some b)).
Proof.
  intros.
  inversion H.
  clear H.
  unfold agree in H0.
  specialize (H0 i x).
  rewrite H1 in H0.
  auto.
Qed.

Lemma agree_same_or_none : forall b' b, agree' (b') (Some b) -> b' = None \/ b' = Some b.
Proof.
  intros.
  destruct b'.
  right.
  inversion H.
  auto.
  left.
  auto.
Qed.

Lemma Hextract_agree_same_or_none : forall gs b, (exists i, Hextract gs i = Some b) -> agree gs -> (forall i, (Hextract gs i) = None \/ (Hextract gs i) = Some b).
Proof.
  intros.
  apply agree_same_or_none.
  apply Hextract_agree ; auto.
Qed.


Lemma HStep_keeps_agreement : forall gs gs', HStep gs gs' -> agree gs -> agree gs'.
Proof.
  intros.
  inversion H.
  - subst ; auto.
  - subst.
    inversion H1.
    clear H1.
    unfold agree.
    destruct gs'.
    destruct gs.
    intros.
    unfold Hstep_decide in H3.
    inversion H3.
    subst.
    unfold agree in H0.
    specialize (H0 i0 j).
    clear H H3.
    unfold Hextract.
    remember (i0 <? hg_n1) as inrange_i0.
    remember (j <? hg_n1) as inrange_j.
    destruct (inrange_i0) ; unfold agree'; auto.
    destruct (inrange_j).
    + remember (i0 =? i) as isi_i0.
      remember (j =? i) as isi_j.
      destruct (isi_i0).
      destruct (isi_j).
      * remember (Hextract_loc match h_localstates1 i with
                   | Some ls => Some (Hstep_decide_loc ls b)
                   | None => None
                   end) as hi.
        destruct hi ; auto.
      * remember (Hextract_loc match h_localstates1 i with
                   | Some ls => Some (Hstep_decide_loc ls b)
                   | None => None
                   end) as hi.
        specialize (H2 j).
        simpl in H2.
        rewrite <- Heqinrange_j in H2.
        rewrite H2.
        destruct hi ; auto.
      * specialize (H2 i0).
        simpl in H2.
        rewrite <- Heqinrange_i0 in H2.
        rewrite H2.
        auto.
    + destruct (Hextract_loc (if i0 =? i then match h_localstates1 i with
                                    | Some ls => Some (Hstep_decide_loc ls b)
                                    | None => None
                                    end else h_localstates1 i0)) ; auto.
  - subst.
    specialize (Hextract_agree_same_or_none gs b).
    inversion H1.
    clear H1.
    intros.
    unfold agree.
    intros.
    assert (Hextract gs i0 = None \/ Hextract gs i0 = Some b).
    crush.
    assert (Hextract gs j = None \/ Hextract gs j = Some b).
    crush.
    destruct gs.
    destruct gs'.
    intros.
    unfold agree.
    unfold Hstep_decide in H3.
    inversion H3.
    subst.
    clear H H3.
    unfold Hextract.
    unfold Hextract in H4.
    unfold Hextract in H5.
    intros.
    remember hg_n0 as n.
    remember h_localstates0 as localstates.
    remember (i0 <? n) as inrange_i0.
    remember (j <? n) as inrange_j.
    destruct (inrange_i0) ; unfold agree'; auto.
    destruct (inrange_j).
    + remember (i0 =? i) as isi_i0.
      remember (j =? i) as isi_j.
      destruct (isi_i0).
      destruct (isi_j).
      * remember (Hextract_loc match localstates i with
                   | Some ls => Some (Hstep_decide_loc ls b)
                   | None => None
                   end) as hi.
        destruct hi ; auto.
      * remember (Hextract_loc match localstates i with
                   | Some ls => Some (Hstep_decide_loc ls b)
                   | None => None
                   end) as hi.
        inversion H5.
        { rewrite H. destruct hi ; auto. }
        { rewrite H.
          specialize (beq_nat_true i0 i).
          intros.
          rewrite <- H3 in Heqhi.
          inversion H4.
          unfold Hextract_loc in H6.
          destruct (localstates i0).
          simpl in Heqhi.
          destruct h.
          simpl in Heqhi.
          rewrite Heqhi ; auto.
          simpl in Heqhi.
          rewrite Heqhi.
          auto.
          unfold Hextract_loc in H6.
          destruct (localstates i0).
          destruct h.
          simpl in Heqhi.
          rewrite Heqhi ; auto.
          inversion H6.
          rewrite <- Heqisi_i0.
          auto. }
      * inversion H4.
        rewrite H. auto.
        rewrite H.
        destruct (isi_j).
        { destruct (localstates i).
          simpl.
          destruct h.
          simpl.
          auto.
          simpl.
          auto. }
        { inversion H5 ; rewrite H3 ; auto. }
    + destruct (Hextract_loc (if i0 =? i then match localstates i with
                                    | Some ls => Some (Hstep_decide_loc ls b)
                                    | None => None
                                    end else localstates i0)) ; auto.
Qed.

Theorem HSteps_keeps_agreement : forall gs gs', HSteps gs gs' -> agree gs -> agree gs'.
Proof.
  intros.
  induction H.
  - apply (HStep_keeps_agreement gs gs' H H0).
  - specialize (IHHSteps H0).
    apply (HStep_keeps_agreement gs' gs'' H1 IHHSteps).
Qed. 

Theorem HinitGS_keeps_agreement : forall input n, agree (HinitGS (HInitP input n)).
Proof.
  intros.
  unfold HinitGS.
  unfold agree.
  intros.
  simpl.
  destruct (i <? n0) ; destruct (j <? n0) ; unfold agree' ; unfold HinitLS ; unfold Hextract_loc ; auto.
Qed.

Theorem HAgreement : forall params gs, HisValid params gs -> agree gs.
Proof.
  intros.
  apply (HSteps_keeps_agreement (HinitGS params) gs H).
  apply HinitGS_keeps_agreement.
Qed.

End Agreement.

End High_level.

Section Refinement.

(* Refinement Theorem *)

Definition ref_map_local (lls : option LocalState) : (option HLocalState) :=
  match lls with
  | Some ls => 
    match ls with
    | Honest ls' => Some (HHonest (input ls') (decision ls'))
    end
  | None => None
  end.

Definition ref_map (lgs : GlobalState) : HGlobalState :=
  HGS (n lgs) (compose ref_map_local (local_states lgs)).

Ltac matchFun :=
  match goal with
  | H : _ |- HStep (HGS _ ?f1) (HGS _ ?f2) => assert (f1 = f2) as hfeq
  | H : _ |- (HGS _ ?f1) = (HGS _ ?f2) => assert (f1 = f2) as hfeq
  end.

Ltac caseNothing m Heqls :=
  match goal with
  | H : _ |- HStep (HGS _ ?f1) (HGS _ ?f2) => 
    assert (f1 = f2) as feq ; [
    apply fun_eqiv;
    intros rid;
    unfold compose;
    unfold ref_map_local;
    remember (rid =? receiver_id m) as is_receiver;
    destruct is_receiver; 
    [ specialize (beq_nat_true rid (receiver_id m));
      intros rseq;
      rewrite rseq; 
    [ rewrite <- Heqls | ] | ]; auto
    | rewrite feq;
      constructor ]
  end.

Ltac caseSomething m Heqls :=
  unfold Hstep_decide;
  simpl;
  match goal with
  | H : _ |- ( _ ?f1) = ( _ ?f2) => 
    assert (f1 = f2) as feq ; [
    apply fun_eqiv;
    intros rid;
    unfold ref_map_local;
    remember (rid =? receiver_id m) as is_receiver;
    destruct is_receiver ; [rewrite <- Heqls | ] | rewrite feq] ; unfold Hstep_decide_loc; crush
  end.

Fixpoint rseq (n : nat) : list nat :=
  match n with
  | O => nil
  | S n' => n' :: (rseq n')
  end.

Lemma finiteNone : forall (n : nat) (f : nat -> option bool) (i : nat), None = fold_right mergeb None (map f (rseq n)) -> i < n -> f i = None.
Proof.
  intros.
  generalize dependent i.
  induction n0.
  - crush.
  - intros.
    inversion H0.
    + simpl in H.
      destruct (f0 n0).
      auto.
      auto.
    + apply IHn0.
      * simpl in H.
        destruct (f0 n0) ; crush.
      * destruct n0 ; crush.
Qed.

Lemma finiteSome : forall (n : nat) (f : nat -> option bool) (b : bool), Some b = fold_right mergeb None (map f (rseq n))  -> (exists i, i < n /\ f i = Some b).
Proof.
  intros.
  induction n0.
  - crush.
  - intros.
    inversion H.
    remember (f0 n0) as v.
    destruct v.
    + inversion H1.
      rewrite <- H2.
      exists n0.
      crush.
    + inversion H1.
      remember (IHn0 H2) as H3.
      inversion H3.
      exists x.
      crush.
Qed.

Theorem Refinement : forall params gs gs', isValid params gs -> Step gs gs' -> HStep (ref_map gs) (ref_map gs').
Proof.
  intros.
  induction H0.
  unfold step in H0.
  destruct (undelivered gs).
  - (* ROUND : NOTHING *)
    unfold ref_map.
    inversion H0.
    simpl.
    matchFun.
    + unfold compose.
      eapply fun_eqiv.
      intros.
      unfold step_round.
      unfold step_round_loc.
      destruct (local_states gs x).
      destruct l.
      auto.
      auto.
    + rewrite hfeq.
      constructor.
  - (* DELIVER *)
    unfold ref_map.
    inversion H0.
    simpl.
    unfold compose.
    remember (local_states gs (receiver_id m)) as lsi.
    remember (local_states gs' (receiver_id m)) as lsi'.
    unfold step_deliver.
    rewrite H1 in Heqlsi'.
    simpl in Heqlsi'.
    unfold step_deliver in Heqlsi'.
    specialize (beq_nat_refl (receiver_id m)) as ht.
    rewrite <- ht in Heqlsi'.
    clear ht.
    simpl in Heqlsi'.
    destruct lsi.
    + rewrite <- Heqlsi in Heqlsi'.
      rewrite <- Heqlsi.
      unfold step_deliver_loc.
      unfold step_deliver_loc in Heqlsi'.
      destruct l0.
      remember (decision ls) as di.
      destruct di.
      * (* Has decided: NOTHING *)
        rewrite  Heqdi.
        caseNothing m Heqlsi.
      * (* Haven't decided *)
        destruct lsi'.
        { destruct l0.
          inversion Heqlsi'.
          rewrite <- H3.
          remember (decision ls0) as di'.
          destruct di'.
          - match goal with
            | H : _ |- HStep ?GS _ => remember GS as Hgs
            end.
            remember (fold_right mergeb  None (map (Hextract Hgs) (rseq (hg_n Hgs)))) as Hstateb.
            destruct Hstateb.
            + (* AGREE *)
              specialize (finiteSome (hg_n Hgs) (Hextract Hgs) b0).
              intros.
              remember (H2 HeqHstateb) as Hjexist.
              clear HeqHjexist H2.
              assert (b = b0).
              * clear HeqHstateb H3.
                admit.
              * eapply (AGREE Hgs (receiver_id m) b0).
                split.
                { inversion Hjexist.
                  exists x; crush. }
                { rewrite HeqHgs.
                  caseSomething m Heqlsi.
                }
            + (* DECIDE *)
              eapply (DECIDE Hgs (receiver_id m) b).
              split.
              * rewrite HeqHgs.
                rewrite HeqHgs in HeqHstateb.
                intro.
                remember (j <? n gs) as j_inrange.
                destruct j_inrange.
                { specialize (Nat.ltb_lt j (n gs)) as j_inrange'.
                  rewrite <- Heqj_inrange in j_inrange'.
                  simpl in j_inrange'.
                  match goal with
                  | H : _ |- ?f _ = None => remember f as g
                  end.
                  simpl in HeqHstateb.
                  remember (n gs) as n.
                  clear Heqj_inrange Heqg HeqHgs Hgs Heqdi' H3 Heqlsi' Heqdi ls0 Heqlsi ls H1 H0 l m gs' H params b gs Heqn.
                  apply (finiteNone n g j) ; crush.
                }
                { simpl. rewrite <- Heqj_inrange ; auto. }
              * rewrite HeqHgs.
                caseSomething m Heqlsi.
          - (* Didn't decide: NOTHING *)
            caseNothing m Heqlsi.
            rewrite <- Heqdi.
            rewrite <- Heqdi'.
            inversion H3.
            auto.
        }
        inversion Heqlsi'.
    + (* Out of range: NOTHING *)
      caseNothing m Heqlsi.
Admitted.

End Refinement.