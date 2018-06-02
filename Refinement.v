(* Refinement Theorem *)

Require Import Program Arith PeanoNat List CpdtTactics.

Load Assumption.
Load Low_def.
Load High_proof.

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

Definition ref_mapp (p : InitialParams) : HInitialParams :=
  HInitP (inputs p) (f_to_n (numf p)).

Theorem Refinementp : forall params, isValidP params -> HisValid (ref_mapp params) (ref_map (initGS params)).
Proof.
  intros.
  unfold HisValid.
  eapply HONE.
  assert ((HinitGS (ref_mapp params)) = (ref_map (initGS params))).
  unfold HinitGS.
  unfold ref_map.
  unfold ref_mapp.
  unfold initGS.
  destruct params.
  simpl.
  unfold ref_map_local.
  match goal with
    | H : _ |- (HGS _ ?f1) = (HGS _ ?f2) => assert (f1 = f2) as hfeq
  end.
  unfold compose.
  apply fun_eqiv.
  intros.
  unfold HinitLS.
  unfold initLS.
  destruct (x <? f_to_n numf0).
  auto.
  auto.
  rewrite hfeq.
  auto.
  rewrite H0.
  eapply NOTHING.
Qed.

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

Definition extract_decision (i : nat) (gs : GlobalState) :=
  match (local_states gs) i with
  | Some (Honest ls) => decision ls
  | None => None
  end.

Definition extract_history (i : nat) (gs : GlobalState) :=
  match (local_states gs) i with
  | Some (Honest ls) => Some (history ls (hl_round_no ls))
  | None => None
  end.

Definition extract_historyrj (i : nat) (gs : GlobalState) (r : nat) (j : nat):=
  match (local_states gs) i with
  | Some (Honest ls) => (history ls r j)
  | None => None
  end.

Definition extract_estimationr (i : nat) (gs : GlobalState) (r : nat) :=
  match (local_states gs) i with
  | Some (Honest ls) => (estimation ls r)
  | None => None
  end.

Lemma Core1_1 : forall params i, extract_decision i (initGS params) = None.
Proof.
Admitted.

Lemma Core1_2 : forall s : option bool, s <> None -> exists b, s = Some b.
Proof.
Admitted.

Lemma Core1_3 : forall gs gs' i b, extract_decision i gs = Some b -> gs <<= gs' -> extract_decision i gs' = Some b.
Proof.
Admitted.

Lemma Core1 : forall params gs i b, isValid params gs -> extract_decision i gs = Some b -> 
  exists gs', isValid params gs' /\ step gs' <<= gs /\ extract_decision i gs' = None /\ extract_decision i (step gs') = Some b.
Proof.
Admitted.

Ltac forget v :=
  match goal with
  | [Heq : v = ?v' |- _] => repeat (
    match goal with
    | [H : context[v] |- _] => rewrite Heq in H
    end) ; clear v Heq
  | [Heq : ?v' = v |- _] => repeat (
    match goal with
    | [H : context[v] |- _] => rewrite <- Heq in H
    end) ; clear v Heq
  end.
  

Lemma Core3_1 : forall gs i b, extract_decision i gs = Some b -> exists h, extract_history i gs = Some h.
Proof.
Admitted.

Lemma Core3_2 : forall gs i b h, extract_decision i gs = None -> extract_decision i (step gs) = Some b ->
  extract_history i (step gs) = Some h ->
  exists qi, qi < coq_m (CQ (step gs)) /\ testone (n (step gs)) (coq_sq (CQ (step gs)) qi) h = Some b.
Proof.
Admitted.

Lemma Core3_3 : forall params gs, isValid params gs -> coq_cq params = CQ gs.
Proof.
Admitted.

Lemma Core3_4 : forall params gs, isValid params gs -> isValid params (step gs).
Proof.
Admitted.

Lemma Core3_5 : forall params gs, isValid params gs -> n_CoQuorum_valid (CQ gs) (n gs).
Proof.
Admitted.

Lemma Core3_6 : forall gs b h sq k, testone (n gs) sq h = Some b -> sq k = true -> 
  exists m, h k = Some m /\ vote m = Some b.
Proof.
Admitted.

Lemma Core3_7 : forall gs gs', gs <<= gs' -> (n gs = n gs').
Proof.
Admitted.

Lemma Core3_8 : forall params gs gs' i h j m, isValid params gs -> gs <<= gs' -> extract_history i gs = Some h -> h j = Some m -> extract_historyrj i gs' (round_no gs) j = Some m.
Proof.
Admitted.

Lemma Core3_9 : forall gs i b, extract_decision i gs = None -> extract_decision i (step gs) = Some b -> round_no gs = round_no (step gs).
Proof.
Admitted.

Lemma Core3_10 : forall params gs r i j k mj mk, isValid params gs -> extract_historyrj j gs r i = Some mj -> extract_historyrj k gs r i = Some mk ->
  vote mj = vote mk.
Proof.
Admitted.

Lemma Core4_1 : forall params gs i b, isValid params gs -> extract_decision i gs = Some b -> 
  (forall gs', gs <<= gs' -> (round_no gs < round_no gs') -> (forall j b0, extract_estimationr j gs' (round_no gs') = Some b0 ->
  b = b0)).
Proof.
Admitted.

Lemma Core4_2 : forall params gs r i, isValid params gs -> 0 < r -> r <= round_no gs -> i < (n gs) -> (exists b, extract_estimationr i gs r = Some b).
Proof.
Admitted.

(* Low_Level_Validity *)
Lemma Core4_3 : forall params gs i b b0, isValid params gs -> extract_decision i gs = None -> extract_decision i (step gs) = Some b -> 
  (forall j, j < (n gs) -> extract_estimationr j gs (round_no gs) = Some b0) -> b = b0.
Proof.
Admitted.

Theorem coreCase : forall params gs gs' i j b b0, isValid params gs -> gs' = step gs ->
  extract_decision i gs = None -> extract_decision j gs = Some b0 -> extract_decision i gs' = Some b ->
  b = b0.
Proof.
  (* 1. apply witness theorem *)
  intros.
  specialize (Core1 params gs j b0 H H2).
  intros.
  destruct H4.
  remember x as gs0.
  forget x.
  destruct H4.
  destruct H5.
  destruct H6.
  (* 2. split into same/different round case *)
  assert (gs0 <<= gs).
  apply (transit gs0 (step gs0) gs).
  constructor.
  constructor.
  assumption.
  specialize (Low_Level_Monotonicity gs0 gs H8).
  intros.
  destruct H9.
  clear H10.
  inversion H9.
  - (* 3. Same round *)
    specialize (Core3_1 (step gs0) j b0 H7).
    specialize (Core3_1 gs' i b H3).
    intros.
    destruct H10.
    remember x as hi.
    forget x.
    destruct H12.
    remember x as hj.
    forget x.
    forget gs'.
    specialize (Core3_2 gs0 j b0 hj H6 H7 H12).
    specialize (Core3_2 gs i b hi H1 H3 H10).
    intros.
    destruct H0.
    remember x as qi.
    forget x.
    destruct H13.
    remember x as qj.
    forget x.
    destruct H0.
    destruct H13.
    assert ((CQ (step gs)) = (CQ (step gs0))).
    rewrite <- (Core3_3 params (step gs)).
    rewrite <- (Core3_3 params (step gs0)).
    reflexivity.
    apply (Core3_4 params gs0).
    assumption.
    apply (Core3_4 params gs).
    assumption.
    rewrite <- H16 in H15.
    rewrite <- H16 in H13.
    specialize (Core3_4 params gs H).
    intros.
    specialize (Core3_5 params (step gs) H17).
    intros.
    unfold n_CoQuorum_valid in H18.
    destruct H18.
    unfold n_Quorum_valid in H18.
    simpl in H18.
    specialize (H18 qi qj H0 H13) as H20.
    destruct H20.
    remember x as k.
    forget x.
    destruct H20.
    destruct H21.
    specialize (Core3_6 (step gs) b hi (coq_sq (CQ (step gs)) qi) k H14 H21).
    assert (step gs0 <<= step gs).
    apply (transit (step gs0) gs (step gs)).
    assumption.
    apply (succ gs).
    rewrite (Core3_7 (step gs0) (step gs) H23) in H15.
    specialize (Core3_6 (step gs) b0 hj (coq_sq (CQ (step gs)) qj) k H15 H22).
    intros.
    destruct H24.
    remember x as mkj.
    forget x.
    destruct H25.
    remember x as mki.
    forget x.
    destruct H24.
    destruct H25.
    specialize (Core3_8 params (step gs) (step gs) i hi k mki H17 (reflex (step gs)) H10 H25).
    specialize (Core3_8 params (step gs0) (step gs) j hj k mkj (Core3_4 params gs0 H4) H23 H12 H24).
    intros.
    specialize (Core3_9 gs0 j b0 H6 H7).
    intros.
    rewrite H11 in H30.
    rewrite <- H30 in H28.
    specialize (Core3_9 gs i b H1 H3).
    intros.
    rewrite H31 in H28.
    specialize (Core3_10 params (step gs) (round_no (step gs)) k i j mki mkj H17 H29 H28).
    intros.
    rewrite H26 in H32.
    rewrite H27 in H32.
    inversion H32.
    reflexivity.
  - (* 4. Different round *)
    assert (round_no gs0 < round_no gs).
    induction m ; crush.
    clear m H9 H11 H10.
    specialize (Core3_9 gs0 j b0 H6 H7).
    intros.
    rewrite H9 in H12.
    forget gs'.
    specialize (Core4_1 params (step gs0) j b0 (Core3_4 params gs0 H4) H7 gs H5 H12).
    intros.
    assert (forall j, j < (n gs) -> extract_estimationr j gs (round_no gs) = Some b0).
    + intros.
      assert (0 < round_no gs).
      destruct (round_no (step gs0)) ; crush.
      assert (round_no gs <= round_no gs).
      crush.
      specialize (Core4_2 params gs (round_no gs) j0 H H11 H13 H10).
      intros.
      destruct H14.
      rewrite (H0 j0 x H14).
      auto.
    + clear H0.
      apply (Core4_3 params gs i b b0 H H1 H3 H10).
Qed.

(*
  intros.
  inversion H.
  remember (initGS params) as gs0.
  remember (extract_decision j) as fj.
  assert (fj gs0 <> fj gs).
  rewrite H2.
  rewrite Heqfj.
  rewrite Heqgs0.
  unfold extract_decision.
  unfold initGS.
  simpl.
  unfold initLS.
  destruct (j <? f_to_n (numf params)) ; simpl ; discriminate.
  specialize (Low_Level_Witness (option bool) gs0 gs fj H5 H6).
  intros.
  inversion H7.
  remember x as gs0'.
  clear H7 x Heqgs0'.
  inversion H8.
  inversion H9.
  inversion H11.
  clear H8 H9 H11.
  remember (fj (step gs0')) as djgs0'.
  destruct djgs0'.
  - specialize (Low_Level_Monotonicity (step gs0') gs H10).
    intros.
    unfold Low_mono in H8.
    inversion H8.
    inversion H11.
    inversion H15.
    inversion H17.
    inversion H19.
    inversion H21.
    clear H8 H11 H15 H17 H19 H21.
    remember ((local_states (step gs0')) j) as lsj0''.
    destruct lsj0''.
    + assert (local_states (step gs0') j = Some l) as Heqlsj0''r.
      auto.
      remember (H20 j l Heqlsj0''r) as H8.
      inversion H8.
      inversion H11.
      clear H8 H11 HeqH8.
      unfold LowL_mono in H17.
      destruct l.
      destruct x.
      inversion H17.
      inversion H11.
      inversion H21.
      inversion H25.
      clear H17 H11 H21 H25.
      rewrite Heqfj in Heqdjgs0'.
      unfold extract_decision in Heqdjgs0'.
      rewrite <- Heqlsj0'' in Heqdjgs0'.
      assert (decision ls = Some b1) as Heqdlsj0'r.
      auto.
      remember (H27 b1 Heqdlsj0'r) as Hdls0.
      rewrite Heqfj in H2.
      unfold extract_decision in H2.
      destruct (local_states gs j) ; [ | inversion H2].
      destruct l.
      inversion H15.
      rewrite H17 in H2.
      clear HeqHdls0.
      rewrite H2 in Hdls0.
      inversion Hdls0.
      subst.
    + rewrite Heqfj in Heqdjgs0'.
      unfold extract_decision in Heqdjgs0'.
      rewrite <- Heqlsj0'' in Heqdjgs0'.
      inversion Heqdjgs0'.
  - rewrite Heqgs0 in H13.
    unfold initGS in H13.
    rewrite Heqfj in H13.
    unfold extract_decision in H13.
    simpl in H13.
    unfold initLS in H13.
    destruct (j <? f_to_n (numf params)) ; simpl in H13 ; crush.
Admitted.
*)

Theorem Refinement : forall params gs, isValid params gs -> HStep (ref_map gs) (ref_map (step gs)).
Proof.
  intros.
  remember (step gs) as gs'.
  unfold step in Heqgs'.
  match goal with
  | [ H: context [match ?m with | _ => _ end] |- _] => remember m as m'
  end.
  destruct m'.
  - (* DELIVER *)
    rewrite Heqgs'.
    unfold ref_map.
    simpl.
    unfold compose.
    remember (local_states gs (receiver_id m)) as lsi.
    remember (local_states gs' (receiver_id m)) as lsi'.
    unfold step_deliver.
    rewrite Heqgs' in Heqlsi'.
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
      destruct l.
      remember (decision ls) as di.
      destruct di.
      * (* Has decided: NOTHING *)
        rewrite  Heqdi.
        caseNothing m Heqlsi.
      * (* Haven't decided *)
        destruct lsi'.
        { destruct l.
          inversion Heqlsi'.
          rewrite <- H1.
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
              remember (H0 HeqHstateb) as Hjexist.
              clear HeqHjexist H0.
              assert (b = b0).
              * clear HeqHstateb H1.
                (* The core case *)
                (* First get back to the original forms *)
                assert (gs' = step gs) as Hgsstep.
                rewrite Heqgs'.
                unfold step.
                rewrite <- Heqm'.
                auto.
                remember (receiver_id m) as i.
                assert (Some (Honest ls0) = local_states gs' i).
                rewrite Heqgs'.
                rewrite Heqlsi'.
                unfold step_deliver.
                simpl.
                rewrite <- Heqi.
                assert (i =? i = true).
                eapply Nat.eqb_eq.
                auto.
                rewrite H0.
                rewrite <- Heqlsi.
                unfold step_deliver_loc.
                rewrite <- Heqdi.
                auto.
                clear Heqgs' Heqlsi'.
                rename H0 into Heqlsi'.
                rename Hgsstep into Heqgs'.
                inversion Hjexist.
                remember x as j.
                clear x Heqj.
                rewrite HeqHgs in H0.
                simpl in H0.
                inversion H0.
                assert (j <? (n gs) = true).
                eapply Nat.ltb_lt.
                auto.
                rewrite H3 in H2.
                remember (local_states gs j) as lsj.
                destruct lsj.
                {
                  destruct l.
                  unfold Hextract_loc in H2.
                  unfold ref_map_local in H2.
                  clear H1 H3 H0 HeqHgs Hjexist.
                  eapply (coreCase params gs gs' i j b b0 H Heqgs') ; unfold extract_decision ; auto.
                  rewrite <- Heqlsi ; rewrite Heqdi ; auto.
                  rewrite <- Heqlsj ; rewrite H2 ; auto.
                  rewrite <- Heqlsi' ; rewrite Heqdi' ; auto.
                }
                inversion H2.
              * eapply (AGREE Hgs (receiver_id m) b0).
                split.
                { inversion Hjexist.
                  exists x; crush. }
                { rewrite HeqHgs.
                  rewrite H1 in Heqdi'.
                  simpl in Heqdi'.
                  rewrite <- Heqdi' in H1.
                  rewrite H1.
                  simpl.
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
                  clear Heqj_inrange Heqg HeqHgs Hgs Heqdi' Heqlsi' Heqdi ls0 Heqlsi Heqm' Heqgs' ls H1 m gs' H params b gs Heqn.
                  apply (finiteNone n g j) ; crush.
                }
                { simpl. rewrite <- Heqj_inrange ; auto. }
              * rewrite HeqHgs.
                caseSomething m Heqlsi.
          - (* Didn't decide: NOTHING *)
            caseNothing m Heqlsi.
            rewrite <- Heqdi.
            rewrite <- Heqdi'.
            inversion H1.
            auto.
        }
        inversion Heqlsi'.
    + (* Out of range: NOTHING *)
      caseNothing m Heqlsi.
  - (* ROUND : NOTHING *)
    unfold ref_map.
    simpl.
    matchFun.
    + unfold compose.
      eapply fun_eqiv.
      rewrite Heqgs'.
      simpl.
      intros.
      unfold step_round.
      unfold step_round_loc.
      destruct (local_states gs x).
      destruct l.
      auto.
      auto.
    + rewrite hfeq.
      rewrite Heqgs'.
      constructor.
Qed.


Theorem Refinement' : forall params gs, isValid params gs -> HisValid (ref_mapp params) (ref_map gs).
Proof.
  intros.
  inversion H.
  remember (initGS params) as inits.
  induction H1.
  - rewrite Heqinits.
    apply Refinementp.
    auto.
  - unfold HisValid.
    assert (isValid params s').
    + unfold isValid.
      split ; auto.
      inversion H.
      inversion H3.
      * clear H H0 s Heqinits H1 IHLow_leq H2 H3 s0 H4.
        unfold initGS in H6.
        destruct params.
        destruct s'.
        simpl in H6.
        unfold step in H6.
        simpl in H6.
        match goal with
        | [ H : context [match ?m with | _ => _ end] |- _ ] => destruct m
        end.
        { inversion H6.
          unfold update_delivered in H7.
          destruct m.
          clear H6 H0 H1 H2 H3 H4 H5.
          match goal with
          | [ H : ?l = ?r |- _ ] => remember l as fl ; remember r as fr
          end.
          assert (fl 0 sender_id0 receiver_id0 = fr 0 sender_id0 receiver_id0).
          rewrite H7 ; auto.
          rewrite Heqfl in H.
          rewrite Heqfr in H.
          simpl in H.
          assert ((sender_id0 =? sender_id0) = true).
          eapply Nat.eqb_eq.
          auto.
          assert ((receiver_id0 =? receiver_id0) = true).
          eapply Nat.eqb_eq.
          auto.
          rewrite H0 in H.
          rewrite H1 in H.
          simpl in H.
          inversion H.
        }
        inversion H6.
        destruct round_no0 ; inversion H0.
      * rewrite <- Heqinits ; auto.
    + remember (IHLow_leq H2 Heqinits) as H'.
      unfold HisValid in H'.
      eapply HMANY.
      apply H'.
      eapply Refinement.
      apply H2.
Qed.
