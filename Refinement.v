(* Refinement Theorem *)
Require Import Program Arith PeanoNat List CpdtTactics EquivDec.
Require Import Assumption Quorum Low_def High_def High_proof Temporal.

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
  destruct (x <? f_to_n numf).
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
  induction n.
  - crush.
  - intros.
    inversion H0.
    + simpl in H.
      destruct (f n).
      auto.
      auto.
    + apply IHn.
      * simpl in H.
        destruct (f n) ; crush.
      * destruct n ; crush.
Qed.

Lemma finiteSome : forall (n : nat) (f : nat -> option bool) (b : bool), Some b = fold_right mergeb None (map f (rseq n))  -> (exists i, i < n /\ f i = Some b).
Proof.
  intros.
  induction n.
  - crush.
  - intros.
    inversion H.
    remember (f n) as v.
    destruct v.
    + inversion H1.
      rewrite <- H2.
      exists n.
      crush.
    + inversion H1.
      remember (IHn H2) as H3.
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

Definition extract_historyr (i : nat) (gs : GlobalState) (r : nat) :=
  match (local_states gs) i with
  | Some (Honest ls) => Some (history ls r)
  | None => None
  end.

Definition extract_historyrj (i : nat) (gs : GlobalState) (r : nat) (j : nat):=
  match (local_states gs) i with
  | Some (Honest ls) => history ls r j
  | None => None
  end.

Definition extract_estimationr (i : nat) (gs : GlobalState) (r : nat) :=
  match (local_states gs) i with
  | Some (Honest ls) => (estimation ls r)
  | None => None
  end.

Definition extract_estimationr' (i : nat) (r : nat) (gs : GlobalState) :=
  match (local_states gs) i with
  | Some (Honest ls) => (estimation ls r)
  | None => None
  end.

Lemma extract_estimationr_eqiv : forall i r gs, extract_estimationr i gs r = extract_estimationr' i r gs.
Proof.
  crush.
Qed.

Definition extract_round (i : nat) (gs : GlobalState) :=
  match (local_states gs) i with
  | Some (Honest ls) => Some (hl_round_no ls)
  | None => None
  end.

(* Trivial *)
Lemma Core1_1 : forall params i, extract_decision i (initGS params) = None.
Proof.
  intros.
  unfold extract_decision.
  unfold initGS.
  unfold initLS.
  simpl.
  destruct (i <? f_to_n (numf params)) ; auto.
Qed.

(* Trivial *)
Lemma Core1_2 : forall s : option bool, s <> None -> exists b, s = Some b.
Proof.
  intros.
  destruct s.
  exists b.
  auto.
  congruence.
Qed.

(* Simple *)
Lemma Core1_3 : forall gs gs' i b, extract_decision i gs = Some b -> gs <<= gs' -> extract_decision i gs' = Some b.
Proof.
  intros.
  specialize (Low_Level_Monotonicity gs gs' H0).
  intros.
  destruct H1.
  destruct H2.
  destruct H3.
  destruct H4.
  destruct H5.
  unfold extract_decision in H.
  unfold extract_decision.
  remember (local_states gs i) as ls.
  destruct ls.
  destruct l.
  specialize (H5 i (Honest ls) (eq_sym Heqls)).
  destruct H5.
  destruct H5.
  rewrite H5.
  unfold LowL_mono in H7.
  destruct x.
  crush.
  congruence.
Qed.

(* Simple *)
Lemma Core1 : forall params gs i b, isValid params gs -> extract_decision i gs = Some b -> 
  exists gs', isValid params gs' /\ step gs' <<= gs /\ extract_decision i gs' = None /\ extract_decision i (step gs') = Some b.
Proof.
  intros.
  specialize (Core1_1 params i).
  intros.
  remember (initGS params) as gs0.
  assert (EqDec (option bool) eq).
  unfold EqDec.
  intros.
  destruct x ; destruct y ; try destruct b0 ; try destruct b1 ; try (left ; reflexivity) ; try (right ; discriminate).
  destruct H.
  rewrite <- Heqgs0 in H2.
  assert (extract_decision i gs0 <> extract_decision i gs).
  congruence.
  specialize (Low_Level_Witness gs0 gs (extract_decision i) H2 H3).
  intros.
  destruct H4.
  destruct H4.
  destruct H5.
  destruct H6.
  exists x.
  split.
  unfold isValid.
  crush.
  split.
  auto.
  split.
  congruence.
  rewrite H1 in H7.
  specialize (Core1_2 (extract_decision i (step x)) (not_eq_sym H7)).
  intros.
  destruct H8.
  specialize (Core1_3 (step x) gs i x0 H8 H5).
  congruence.
Qed.

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
  
(* Trivial *)
Lemma Core3_1 : forall gs i b, extract_decision i gs = Some b -> exists h, extract_history i gs = Some h.
Proof.
  intros.
  unfold extract_decision in H.
  unfold extract_history.
  destruct (local_states gs i).
  destruct l.
  exists (history ls (hl_round_no ls)).
  auto.
  inversion H.
Qed.

(* Trivial *)
Lemma Core3_9 : forall gs i b, extract_decision i gs = None -> extract_decision i (step gs) = Some b -> round_no gs = round_no (step gs).
Proof.
  intros.
  remember (step gs) as gs'.
  unfold step in Heqgs'.
  remember (get_undelivered (n gs) (message_archive gs (round_no gs)) (delivered gs (round_no gs))) as sm.
  destruct sm.
  - rewrite Heqgs'.
    auto.
  - rewrite Heqgs' in H0.
    unfold extract_decision in H.
    unfold extract_decision in H0.
    simpl in H0.
    unfold step_round in H0.
    destruct (local_states gs i).
    unfold step_round_loc in H0.
    destruct l.
    destruct (estimation ls (hl_round_no ls + 1)).
    simpl in H0.
    congruence.
    simpl in H0.
    congruence.
    inversion H0.
Qed.

Lemma Core3_2_1 : forall n m sq h b, testall n m sq h = Some b -> exists i, i < m /\ testone n (sq i) h = Some b.
Proof.
  intros.
  unfold testall in H.
  induction m.
  - inversion H.
  - rename sq into sq0.
    remember (testone n (sq0 m) h) as sq.
    destruct sq.
    + exists m.
      crush.
    + remember (IHm H) as H1.
      clear HeqH1.
      destruct H1.
      exists x.
      crush.
Qed.

Lemma Core3_2 : forall gs i b h, extract_decision i gs = None -> extract_decision i (step gs) = Some b ->
  extract_history i (step gs) = Some h ->
  exists qi, qi < coq_m (CQ (step gs)) /\ testone (n (step gs)) (coq_sq (CQ (step gs)) qi) h = Some b.
Proof.
  intros.
  specialize (Core3_9 gs i b H H0).
  intros.
  assert (n gs = n (step gs)).
  specialize (Low_Level_Monotonicity gs (step gs) (succ gs)).
  intros.
  unfold Low_mono in H3.
  crush.
  assert (CQ gs = CQ (step gs)).
  specialize (Low_Level_Monotonicity gs (step gs) (succ gs)).
  intros.
  unfold Low_mono in H4.
  crush.
  rewrite <- H3.
  rewrite <- H4.
  clear H3 H4.
  remember (step gs) as gs'.
  unfold step in Heqgs'.
  remember (get_undelivered (n gs) (message_archive gs (round_no gs)) (delivered gs (round_no gs))) as sm.
  destruct sm.
  - rewrite Heqgs' in H0.
    unfold extract_decision in H0.
    simpl in H0.
    unfold extract_history in H1.
    rewrite Heqgs' in H1.
    simpl in H1.
    remember (step_deliver (n gs) (CQ gs) (local_states gs) m i) as ls'.
    destruct ls'.
    + destruct l.
      unfold step_deliver in Heqls'.
      remember (i =? receiver_id m) as is_receiver.
      destruct is_receiver.
      * assert ((i =? receiver_id m) = true).
        auto.
        specialize (beq_nat_true i (receiver_id m) H3).
        intros.
        rewrite <- H4 in Heqls'.
        remember (local_states gs i) as ls0.
        destruct ls0.
        { 
          unfold step_deliver_loc in Heqls'.
          unfold extract_decision in H.
          rewrite <- Heqls0 in H.
          destruct l.
          rewrite H in Heqls'.
          inversion Heqls'.
          clear Heqls'.
          rewrite H6 in H0.
          simpl in H0.
          rewrite H6 in H1.
          simpl in H1.
          inversion H1.
          rewrite H7 in H0.
          clear H1 H6.
          rewrite H7.
          unfold decide in H0.
          destruct (CQ gs).
          simpl.
          eapply (Core3_2_1).
          assumption.
        }
        inversion Heqls'.
      * unfold extract_decision in H.
        rewrite <- Heqls' in H.
        congruence.
    + inversion H0.
  - destruct gs'.
    inversion Heqgs'.
    simpl in H2.
    crush.
Qed.

(* Trivial *)
Lemma Core3_3 : forall params gs, isValid params gs -> coq_cq params = CQ gs.
Proof.
  intros.
  destruct H.
  specialize (Low_Level_Monotonicity (initGS params) gs H0).
  intros.
  destruct H1.
  destruct H2.
  destruct H3.
  destruct H4.
  rewrite <- H4.
  unfold initGS.
  auto.
Qed.

(* Trivial *)
Lemma Core3_4_1 : forall params gs gs', isValid params gs -> gs <<= gs' -> isValid params gs'.
Proof.
  intros.
  unfold isValid.
  destruct H.
  split.
  assumption.
  eapply transit.
  apply H1.
  apply H0.
Qed.

(* Trivial *)
Lemma Core3_4 : forall params gs, isValid params gs -> isValid params (step gs).
Proof.
  intros.
  apply (Core3_4_1 params gs (step gs) H (succ gs)).
Qed.


(* Trivial *)
Lemma Core3_7 : forall gs gs', gs <<= gs' -> (n gs = n gs').
Proof.
  intros.
  specialize (Low_Level_Monotonicity gs gs' H).
  unfold Low_mono.
  tauto.
Qed.


(* Trivial *)
Lemma Core3_5 : forall params gs, isValid params gs -> n_CoQuorum_valid (CQ gs) (n gs) (cond params).
Proof.
  intros.
  rewrite <- (Core3_3 params gs H).
  destruct H.
  rewrite <- (Core3_7 (initGS params) gs H0).
  destruct params.
  simpl.
  unfold isValidP in H.
  auto.
Qed.

Lemma Core3_6_1 : forall n q b, check_quorum_infer' n q b = false ->
  exists i, i < n /\ q i = true /\ b i = false.
Proof.
  intros.
  induction n.
  - inversion H.
  - unfold check_quorum_infer' in H.
    remember (q n) as qn0.
    remember (b n) as bn0.
    destruct qn0.
    destruct bn0.
    fold check_quorum_infer' in H.
    specialize (IHn H).
    destruct IHn.
    exists x.
    crush.
    exists n.
    auto.
    fold check_quorum_infer' in H.
    specialize (IHn H).
    destruct IHn.
    exists x.
    crush.
Qed.

Lemma Core3_6_2 : forall n q b i, check_quorum_infer' n q b = true -> i < n -> q i = true ->
  b i = true.
Proof.  intros.
  induction n.
  - inversion H0.
  - inversion H0.
    unfold check_quorum_infer' in H.
    rewrite H3 in H1.
    rewrite H1 in H.
    remember (b n) as bn0.
    destruct bn0.
    auto.
    auto.
    unfold check_quorum_infer' in H.
    destruct (q n).
    destruct (b n).
    fold check_quorum_infer' in H.
    apply IHn ; auto.
    inversion H.
    fold check_quorum_infer' in H.
    apply IHn ; auto.
Qed.

Lemma Core3_6_3 : forall n q b b0, check_quorum_infer n q b = Some b0 ->
  exists i, i < n /\ q i = true /\ b i = Some b0.
Proof.
  intros.
  unfold check_quorum_infer in H.
  remember (fun i : nat => match b i with
                        | Some true => true
                        | Some false => false
                        | None => false
                        end) as bt.
  remember (fun i : nat => match b i with
                         | Some true => false
                         | Some false => true
                         | None => false
                         end) as bf.
  remember (check_quorum_infer' n q bt) as cbt.
  remember (check_quorum_infer' n q bf) as cbf.
  destruct cbt.
  destruct cbf.
  inversion H.
  specialize (Core3_6_1 n q bf (eq_sym Heqcbf)).
  intros.
  destruct H0.
  destruct H0.
  destruct H1.
  specialize (Core3_6_2 n q bt x (eq_sym Heqcbt) H0 H1).
  intros.
  assert (b x = Some true).
  rewrite Heqbt in H3.
  destruct (b x) ; auto.
  destruct b1 ; congruence.
  inversion H3.
  exists x.
  crush.
  destruct cbf.
  specialize (Core3_6_1 n q bt (eq_sym Heqcbt)).
  intros.
  destruct H0.
  destruct H0.
  destruct H1.
  specialize (Core3_6_2 n q bf x (eq_sym Heqcbf) H0 H1).
  intros.
  assert (b x = Some false).
  rewrite Heqbf in H3.
  destruct (b x) ; auto.
  destruct b1 ; congruence.
  inversion H3.
  exists x.
  crush.
  inversion H.
Qed.

Lemma Core3_6_4 : forall n q b k, check_quorum_infer' n q b = true -> k < n -> q k = true ->
  b k = true.
Proof.
  intros.
  induction n.
  - inversion H0.
  - inversion H0.
    unfold check_quorum_infer' in H.
    rewrite H3 in H1.
    rewrite H1 in H.
    destruct (b n).
    auto.
    inversion H.
    unfold check_quorum_infer' in H.
    destruct (q n) ; destruct (b n).
    fold check_quorum_infer' in H.
    apply (IHn H).
    auto.
    inversion H.
    fold check_quorum_infer' in H.
    apply (IHn H).
    auto.
    fold check_quorum_infer' in H.
    apply (IHn H).
    auto.
Qed.

Lemma Core3_6_5 : forall n q b b0 k, check_quorum_infer n q b = Some b0 -> k < n -> q k = true ->
  b k = Some b0.
Proof.
  intros.
  unfold check_quorum_infer in H.
  remember (fun i : nat => match b i with
                        | Some true => true
                        | Some false => false
                        | None => false
                        end) as bt.
  remember (fun i : nat => match b i with
                         | Some true => false
                         | Some false => true
                         | None => false
                         end) as bf.
  remember (check_quorum_infer' n q bt) as cbt.
  remember (check_quorum_infer' n q bf) as cbf.
  destruct cbt.
  destruct cbf.
  inversion H.
  specialize (Core3_6_4 n q bt k (eq_sym Heqcbt) H0 H1).
  intros.
  rewrite Heqbt in H2.
  destruct (b k) ; auto.
  destruct b1 ; congruence.
  inversion H2.
  destruct cbf.
  specialize (Core3_6_4 n q bf k (eq_sym Heqcbf) H0 H1).
  intros.
  rewrite Heqbf in H2.
  destruct (b k) ; auto.
  destruct b1 ; congruence.
  inversion H2.
  inversion H.
Qed.

Lemma Core3_6 : forall n b h sq k, testone n sq h = Some b -> k < n -> sq k = true -> 
  exists m, h k = Some m /\ vote m = Some b.
Proof.
  intros.
  unfold testone in H.
  remember (filter h) as f.
  specialize (Core3_6_5 n sq f b k H H0 H1).
  intros.
  rewrite Heqf in H2.
  unfold filter in H2.
  destruct (h k).
  exists m.
  destruct m ; auto ; destruct vote ; auto.
  inversion H2.
Qed.

(* Trivial *)
Lemma Core4_1_2_1 : forall gs, round_no gs = round_no (step gs) \/ S (round_no gs) = round_no (step gs).
Proof.
  intros.
  unfold step.
  destruct (get_undelivered (n gs) (message_archive gs (round_no gs)) (delivered gs (round_no gs)));
  crush.
Qed.

Lemma Core3_8_1 : forall params gs i r, isValid params gs -> extract_round i gs = Some r -> r = (round_no gs).
Proof.
  intros.
  destruct H.
  remember (initGS params) as gs0.
  generalize dependent r.
  induction H1.
  - intros.
    unfold extract_round in H0.
    unfold initGS in Heqgs0.
    destruct params.
    subst.
    simpl.
    simpl in H0.
    destruct (i <? f_to_n numf).
    crush.
    inversion H0.
  - remember (step s') as s''.
    unfold step in Heqs''.
    destruct (get_undelivered (n s') (message_archive s' (round_no s')) (delivered s' (round_no s'))).
    + intros. 
      rewrite Heqs''.
      simpl.
      apply IHLow_leq.
      assumption.
      rewrite Heqs'' in H0.
      clear Heqs''.
      unfold extract_round.
      unfold extract_round in H0.
      simpl in H0.
      unfold step_deliver in H0.
      remember (i =? receiver_id m) as isreceiver.
      destruct isreceiver.
      assert (i = receiver_id m).
      eapply (beq_nat_true).
      auto.
      rewrite <- H2 in H0.
      destruct (local_states s' i).
      rewrite <- H0.
      unfold step_deliver_loc.
      destruct l.
      destruct ls.
      simpl.
      destruct decision ; crush.
      inversion H0.
      assumption.
    + rewrite Heqs''.
      unfold extract_round.
      unfold extract_round in IHLow_leq.
      simpl.
      unfold step_round.
      unfold step_round_loc.
      destruct (local_states s' i).
      destruct l.
      destruct (estimation ls (hl_round_no ls + 1)) ; simpl.
      intros.
      rewrite <- (IHLow_leq Heqgs0 (hl_round_no ls)).
      congruence.
      congruence.
      intros.
      specialize (IHLow_leq Heqgs0 (hl_round_no ls)).
      rewrite <- IHLow_leq.
      congruence.
      reflexivity.
      intros.
      inversion H0.
Qed.

Lemma Core3_8 : forall params gs gs' i h j m, isValid params gs -> gs <<= gs' -> extract_history i gs = Some h -> h j = Some m -> extract_historyrj i gs' (round_no gs) j = Some m.
Proof.
  intros.
  induction H0.
  - unfold extract_historyrj.
    unfold extract_history in H1.
    specialize (Core3_8_1 params s i).
    intros.
    unfold extract_round in H0.
    destruct (local_states s i).
    destruct l.
    rewrite <- (H0 (hl_round_no ls) H).
    congruence.
    reflexivity.
    inversion H1.
  - specialize (IHLow_leq H H1).
    unfold extract_historyrj.
    unfold extract_historyrj in IHLow_leq.
    remember (local_states s' i) as ls'.
    destruct ls'.
    + specialize (Low_Level_Monotonicity s' (step s') (succ s')).
      intros.
      destruct H3.
      destruct H4.
      destruct H5.
      destruct H6.
      destruct H7.
      assert (local_states s' i = Some l).
      auto.
      specialize (H7 i l H9).
      destruct H7.
      destruct H7.
      rewrite H7.
      unfold LowL_mono in H10.
      destruct l.
      destruct x.
      destruct H10.
      destruct H11.
      destruct H12.
      destruct H13.
      apply (H13 (round_no s) j m IHLow_leq).
    + inversion IHLow_leq.
Qed.

(* Trivial *)
Lemma Core4_1_2_2 : forall gs gs' r i b, gs <<= gs' -> extract_estimationr i gs r = Some b -> extract_estimationr i gs' r = Some b.
Proof.
  intros.
  specialize (Low_Level_Monotonicity gs gs' H).
  intros.
  destruct H1.
  destruct H2.
  destruct H3.
  destruct H4.
  destruct H5.
  unfold extract_estimationr in H0.
  unfold extract_estimationr.
  remember (local_states gs i) as ls.
  destruct ls.
  destruct l.
  specialize (H5 i (Honest ls) (eq_sym Heqls)).
  destruct H5.
  destruct H5.
  rewrite H5.
  destruct x.
  unfold LowL_mono in H7.
  destruct H7.
  destruct H8.
  destruct H9.
  apply (H9 r b H0).
  inversion H0.
Qed.

(* Simple *)
Lemma Core3_10_1_1_1 : forall params gs r, isValid params gs -> (round_no gs) < r -> forall i j, message_archive gs r i j = None.
Proof.
  intros.
  destruct H.
  remember (initGS params) as gs0.
  induction H1.
  - rewrite Heqgs0.
    unfold initGS.
    destruct params.
    simpl.
    unfold update_messages.
    assert (r =? 0 = false).
    eapply (beq_nat_false_iff).
    destruct r.
    inversion H0.
    discriminate.
    rewrite H1.
    reflexivity.
  - remember (step s') as s''.
    unfold step in Heqs''.
    remember (get_undelivered (n s') (message_archive s' (round_no s')) (delivered s' (round_no s'))) as sm.
    destruct sm.
    rewrite Heqs'' in H0.
    simpl in H0.
    rewrite Heqs''.
    simpl.
    apply (IHLow_leq Heqgs0 H0).
    assert (round_no s' < r).
    rewrite Heqs'' in H0.
    simpl in H0.
    crush.
    rewrite Heqs''.
    simpl.
    unfold update_messages.
    rewrite (IHLow_leq Heqgs0 H2).
    assert (r =? round_no s' + 1 = false).
    eapply (beq_nat_false_iff).
    crush.
    rewrite H3.
    reflexivity.
Qed.

(* Simple *)
Lemma Core3_10_1_1_2 : forall gs ls i j eb, step_round (n gs) (CQ gs) (local_states gs) i = Some (Honest ls) -> estimation ls (hl_round_no ls) = Some eb ->
  exists m, step_message (n gs) (step_round (n gs) (CQ gs) (local_states gs)) i j = Some m /\ vote m = Some eb.
Proof.
  intros.
  unfold step_message.
  rewrite H.
  exists (step_message_from_to (Honest ls) i j).
  split.
  reflexivity.
  unfold step_message_from_to.
  simpl.
  auto.
Qed.

Lemma Core3_10_1_1 : forall params gs r i j eb, isValid params gs -> extract_estimationr' i r gs = None -> extract_estimationr' i r (step gs) = Some eb ->
  j < (n (step gs)) -> exists m, message_archive (step gs) r i j = Some m /\ vote m = Some eb.
Proof.
  intros.
  remember (step gs) as gs'.
  unfold step in Heqgs'.
  remember (get_undelivered (n gs) (message_archive gs (round_no gs)) (delivered gs (round_no gs))) as sm.
  destruct sm.
  unfold extract_estimationr' in H0.
  unfold extract_estimationr' in H1.
  rewrite Heqgs' in H1.
  unfold step_deliver in H1.
  simpl in H1.
  remember (i =? receiver_id m) as isreceiver.
  destruct isreceiver.
  assert ((i =? receiver_id m) = true).
  auto.
  specialize (beq_nat_true i (receiver_id m) H3).
  intros.
  rewrite <- H4 in H1.
  destruct (local_states gs i).
  unfold step_deliver_loc in H1.
  destruct l.
  destruct (decision ls) ; crush.
  inversion H1.
  crush.
  assert (r = round_no gs + 1).
  unfold extract_estimationr' in H0.
  unfold extract_estimationr' in H1.
  rewrite Heqgs' in H1.
  unfold step_round in H1.
  simpl in H1.
  remember (local_states gs i) as ls.
  destruct ls.
  unfold step_round_loc in H1.
  destruct l.
  destruct (estimation ls (hl_round_no ls + 1)) ; crush.
  remember (r =? hl_round_no ls + 1) as req.
  destruct req.
  rewrite <- (Core3_8_1 params gs i (hl_round_no ls) H).
  eapply (beq_nat_true).
  auto.
  unfold extract_round.
  rewrite <- Heqls.
  auto.
  congruence.
  inversion H1.
  assert (message_archive gs r i j = None).
  assert (round_no gs < r).
  crush.
  apply (Core3_10_1_1_1 params gs r H H4).
  assert (exists ls, (step_round (n gs) (CQ gs) (local_states gs) i) = Some (Honest ls)).
  rewrite Heqgs' in H1.
  unfold extract_estimationr' in H1.
  simpl in H1.
  remember (step_round (n gs) (CQ gs) (local_states gs) i) as lss.
  destruct lss.
  destruct l.
  exists ls.
  reflexivity.
  inversion H1.
  destruct H5.
  remember x as ls.
  forget x.
  assert (estimation ls r = Some eb).
  unfold extract_estimationr' in H1.
  rewrite Heqgs' in H1.
  simpl in H1.
  rewrite H5 in H1.
  auto.
  assert (exists ls0, local_states gs i = Some (Honest ls0)).
  unfold step_round in H5.
  remember (local_states gs i) as lss.
  destruct lss.
  destruct l.
  exists ls0.
  reflexivity.
  inversion H5.
  destruct H7.
  remember x as ls0.
  forget x.
  assert (hl_round_no ls0 = round_no gs).
  apply (Core3_8_1 params gs i (hl_round_no ls0) H).
  unfold extract_round.
  rewrite H7.
  auto.
  assert (hl_round_no ls = hl_round_no ls0 + 1).
  unfold step_round in H5.
  rewrite H7 in H5.
  unfold step_round_loc in H5.
  destruct (estimation ls0 (hl_round_no ls0 + 1)).
  inversion H5.
  simpl.
  congruence.
  inversion H5.
  simpl.
  congruence.
  assert (r = hl_round_no ls).
  congruence.
  rewrite H10 in H6.
  specialize (Core3_10_1_1_2 gs ls i j eb H5 H6).
  intros.
  destruct H11.
  remember x as m.
  forget x.
  exists m.
  destruct H11.
  split.
  rewrite Heqgs'.
  simpl.
  unfold update_messages.
  assert (r =? round_no gs + 1 = true).
  eapply (beq_nat_true_iff).
  crush.
  rewrite H13.
  rewrite H4.
  assumption.
  assumption.
Qed.

Lemma Core3_10_1_2 : forall params gs r i eb, isValid params gs -> extract_estimationr i gs r = Some eb -> 0 < r ->
  exists gs', isValid params gs' /\ step gs' <<= gs /\ extract_estimationr' i r gs' = None /\ extract_estimationr' i r (step gs') = Some eb.
Proof.
  intros.
  destruct H.
  remember (initGS params) as gs0.
  rewrite (extract_estimationr_eqiv i r gs) in H0.
  assert (extract_estimationr' i r gs0 = None).
  rewrite Heqgs0.
  destruct params.
  unfold initGS.
  unfold extract_estimationr'.
  simpl.
  destruct (i <? f_to_n numf).
  unfold initLS.
  simpl.
  remember (r =? 0).
  destruct b.
  assert ((r =? 0) = true).
  auto.
  rewrite (beq_nat_true r 0 H3) in H1.
  inversion H1.
  auto.
  auto.
  assert (extract_estimationr' i r gs0 <> extract_estimationr' i r gs).
  congruence.
  assert (EqDec (option bool) eq).
  unfold EqDec.
  intros.
  destruct x ; destruct y ; try destruct b ; try destruct b0 ; try (left ; reflexivity) ; try (right ; discriminate).
  specialize (Low_Level_Witness gs0 gs (extract_estimationr' i r) H2 H4).
  intros.
  destruct H5.
  remember x as gs0'.
  forget x.
  destruct H5.
  destruct H6.
  destruct H7.
  rewrite H3 in H7.
  rewrite H3 in H8.
  assert (extract_estimationr' i r (step gs0') = Some eb).
  - remember (extract_estimationr' i r (step gs0')) as eb0.
    destruct eb0.
    rewrite <- (extract_estimationr_eqiv i r gs) in H0.
    rewrite <- (extract_estimationr_eqiv i r (step gs0')) in Heqeb0.
    assert (extract_estimationr i (step gs0') r = Some b).
    auto.
    specialize (Core4_1_2_2 (step gs0') gs r i b H6 H9).
    intros.
    congruence.
    crush.
  - exists gs0'.
    unfold isValid.
    crush.
Qed.

Lemma Core3_10_2_2_4_2 : forall gs gs' i j, gs <<= gs' -> message_archive gs 0 i j = message_archive gs' 0 i j.
Proof.
  intros.
  induction H.
  - reflexivity.
  - rewrite IHLow_leq.
    unfold step.
    destruct (get_undelivered (n s') (message_archive s' (round_no s')) (delivered s' (round_no s'))).
    + reflexivity.
    + simpl.
      unfold update_messages.
      assert (0 =? round_no s' + 1 = false).
      apply (beq_nat_false_iff).
      crush.
      rewrite H0.
      reflexivity.
Qed.

Lemma Core3_10_1_3 : forall gs gs' i, gs <<= gs' -> extract_estimationr i gs 0 = extract_estimationr i gs' 0.
Proof.
  intros.
  induction H.
  - reflexivity.
  - rewrite IHLow_leq.
    unfold step.
    unfold extract_estimationr.
    destruct (get_undelivered (n s') (message_archive s' (round_no s')) (delivered s' (round_no s'))).
    + simpl.
      unfold step_deliver.
      remember (i =? receiver_id m) as isreceiver.
      destruct isreceiver.
      assert (i = receiver_id m).
      eapply (beq_nat_true).
      auto.
      rewrite <- H0.
      destruct (local_states s' i).
      destruct l.
      unfold step_deliver_loc.
      simpl.
      auto.
      auto.
      auto.
    + simpl.
      unfold step_round.
      unfold step_round_loc.
      destruct (local_states s' i).
      destruct l.
      assert (0 =? hl_round_no ls + 1 = false).
      apply (beq_nat_false_iff).
      crush.
      destruct (estimation ls (hl_round_no ls + 1)).
      auto.
      simpl.
      destruct (hl_round_no ls + 1).
      inversion H0.
      auto.
      auto.
Qed.

Lemma Core3_10_1 : forall params gs r i eb, isValid params gs -> extract_estimationr i gs r = Some eb ->
  forall j, j < (n gs) -> exists m, message_archive gs r i j = Some m /\ vote m = Some eb.
Proof.
  intros.
  destruct r.
  - destruct H.
    remember (initGS params) as gs0.
    rewrite <- (Core3_10_2_2_4_2 gs0 gs i j H2).
    rewrite <- (Core3_10_1_3 gs0 gs i H2) in H0.
    unfold extract_estimationr in H0.
    rewrite Heqgs0.
    rewrite Heqgs0 in H0.
    unfold initGS.
    unfold initGS in H0.
    destruct params.
    simpl.
    simpl in H0.
    unfold update_messages.
    unfold step_message.
    destruct (i <? f_to_n numf).
    unfold initLS in H0.
    simpl in H0.
    exists (step_message_from_to (initLS i (inputs i)) i j).
    auto.
    inversion H0.
  - remember (S r) as r'.
    assert (0 < r').
    crush.
    clear Heqr' r.
    remember r' as r.
    forget r'.
    rename H2 into H2'.
    rename H1 into H2.
    rename H2' into H1.
    specialize (Core3_10_1_2 params gs r i eb H H0 H1).
    intros.
    destruct H3.
    remember x as gs0'.
    forget x.
    destruct H3.
    destruct H4.
    destruct H5.
    assert (exists m, message_archive (step gs0') r i j = Some m /\ vote m = Some eb).
    + rewrite <- (Core3_7 (step gs0') gs H4) in H2.
      apply (Core3_10_1_1 params gs0' r i j eb H3 H5 H6 H2).
    + destruct H7.
      exists x.
      specialize (Low_Level_Monotonicity (step gs0') gs H4).
      intros.
      destruct H8.
      destruct H9.
      destruct H10.
      destruct H11.
      destruct H12.
      destruct H13.
      destruct H7.
      specialize (H13 r i j x H7).
      split ; assumption.
Qed.

(* Simple *)
Lemma Core3_10_2_1 : forall gs gs' r i j m, gs <<= gs' -> extract_historyrj i gs r j = Some m -> extract_historyrj i gs' r j = Some m.
Proof.
  intros.
  specialize (Low_Level_Monotonicity gs gs' H).
  intros.
  destruct H1.
  destruct H2.
  destruct H3.
  destruct H4.
  destruct H5.
  unfold extract_historyrj in H0.
  unfold extract_historyrj.
  remember (local_states gs i) as ls.
  destruct ls.
  destruct l.
  specialize (H5 i (Honest ls) (eq_sym Heqls)).
  destruct H5.
  destruct H5.
  rewrite H5.
  destruct x.
  unfold LowL_mono in H7.
  destruct H7.
  destruct H8.
  destruct H9.
  destruct H10.
  apply (H10 r j m H0).
  inversion H0.
Qed.

Lemma Core3_10_2_2_1 :forall gs r i j m, extract_historyrj i gs r j = None -> extract_historyrj i (step gs) r j = Some m ->
  get_undelivered (n gs) (message_archive gs (round_no gs)) (delivered gs (round_no gs)) = Some m.
Proof.
  intros.
  remember (step gs) as gs'.
  unfold step in Heqgs'.
  remember (get_undelivered (n gs) (message_archive gs (round_no gs)) (delivered gs (round_no gs))) as sm.
  destruct sm.
  - rewrite Heqgs' in H0.
    unfold extract_historyrj in H0.
    simpl in H0.
    unfold step_deliver in H0.
    remember (i =? receiver_id m0) as isreceiver.
    destruct isreceiver.
    assert (i = receiver_id m0).
    apply (beq_nat_true_iff i (receiver_id m0) ).
    auto.
    rewrite <- H1 in H0.
    unfold extract_historyrj in H.
    destruct (local_states gs i).
    destruct l.
    unfold step_deliver_loc in H0.
    simpl in H0.
    remember (r =? m_round_no m0) as isround.
    destruct isround.
    assert (r = m_round_no m0).
    eapply (beq_nat_true_iff).
    auto.
    remember (j =? sender_id m0) as issender.
    destruct issender.
    assert (j = sender_id m0).
    eapply (beq_nat_true_iff).
    auto.
    rewrite H2 in H.
    rewrite H3 in H.
    rewrite H in H0.
    rewrite <- Heqissender in H0.
    rewrite <- Heqisround in H0.
    simpl in H0.
    rewrite <- H2 in H.
    rewrite <- H3 in H.
    rewrite H in H0.
    congruence.
    destruct (history ls (m_round_no m0) (sender_id m0)).
    congruence.
    rewrite <- Heqisround in H0.
    rewrite <- Heqissender in H0.
    simpl in H0.
    congruence.
    destruct (history ls (m_round_no m0) (sender_id m0)).
    congruence.
    rewrite <- Heqisround in H0.
    simpl in H0.
    congruence.
    congruence.
    unfold extract_historyrj in H.
    destruct (local_states gs i) ; crush.
  - rewrite Heqgs' in H0.
    unfold extract_historyrj in H0.
    unfold extract_historyrj in H.
    simpl in H0.
    unfold step_round in H0.
    destruct (local_states gs i).
    destruct l.
    unfold step_round_loc in H0.
    destruct (estimation ls (hl_round_no ls + 1)).
    simpl in H0.
    congruence.
    simpl in H0.
    congruence.
    inversion H0.
Qed.

Lemma Core3_10_2_2_2 : forall gs r i j m, extract_historyrj i gs r j = None -> extract_historyrj i (step gs) r j = Some m ->
  (i = receiver_id m) /\ (r = m_round_no m) /\ (j = sender_id m).
Proof.
  intros.
  specialize (Core3_10_2_2_1 gs r i j m H H0).
  intros.
  remember (step gs) as gs'.
  unfold step in Heqgs'.
  rewrite H1 in Heqgs'.
  rewrite Heqgs' in H0.
  unfold extract_historyrj in H0.
  unfold extract_historyrj.
  simpl in H0.
  unfold step_deliver in H0.
  remember (i =? receiver_id m) as isreceiver.
  destruct isreceiver.
  assert (i = receiver_id m).
  apply (beq_nat_true i (receiver_id m) (eq_sym Heqisreceiver)).
  rewrite <- H2 in H0.
  unfold extract_historyrj in H.
  destruct (local_states gs i).
  destruct l.
  unfold step_deliver_loc in H0.
  simpl in H0.
  remember (r =? m_round_no m) as isround.
  destruct isround.
  assert (r = m_round_no m).
  apply (beq_nat_true r (m_round_no m) (eq_sym Heqisround)).
  remember (j =? sender_id m) as issender.
  destruct issender.
  assert (j = sender_id m).
  apply (beq_nat_true j (sender_id m) (eq_sym Heqissender)).
  crush.
  destruct (history ls (m_round_no m) (sender_id m)).
  congruence.
  rewrite <- Heqisround in H0.
  rewrite <- Heqissender in H0.
  simpl in H0.
  congruence.
  destruct (history ls (m_round_no m) (sender_id m)).
  congruence.
  rewrite <- Heqisround in H0.
  simpl in H0.
  congruence.
  congruence.
  unfold extract_historyrj in H.
  destruct (local_states gs i) ; crush.
Qed.

Lemma Core3_10_2_2_3_1 : forall n msg dev m', get_undelivered1d n msg dev = Some m' -> exists i, msg i = Some m' /\ i < n.
Proof.
  intros.
  induction n.
  - inversion H.
  - unfold get_undelivered1d in H.
    remember (msg n) as m0.
    destruct m0.
    + remember (dev n) as d0.
      destruct d0.
      exists n.
      split.
      congruence.
      auto.
      fold get_undelivered1d in H.
      specialize (IHn H).
      destruct IHn.
      exists x.
      crush.
    + fold get_undelivered1d in H.
      specialize (IHn H).
      destruct IHn.
      exists x.
      crush.
Qed.

Lemma Core3_10_2_2_3_2 : forall n m msg dev m', get_undelivered2d n m msg dev = Some m' -> exists i j, msg i j = Some m' /\ i < n /\ j < m.
Proof.
  intro n0.
  induction n0 ; intros.
  - inversion H.
  - unfold get_undelivered2d in H.
    remember (get_undelivered1d m (msg n0) (dev n0)) as m1d.
    destruct m1d.
    exists n0.
    specialize (Core3_10_2_2_3_1 m (msg n0) (dev n0) m0 (eq_sym Heqm1d)).
    intros.
    destruct H0.
    exists x.
    crush.
    fold get_undelivered2d in H.
    specialize (IHn0 m msg dev m' H).
    destruct IHn0.
    destruct H0.
    exists x.
    exists x0.
    crush.
Qed.

Lemma Core3_10_2_2_3 : forall n msg dev m, get_undelivered n msg dev = Some m ->
  exists i j, msg i j = Some m /\ i < n /\ j < n.
Proof.
  intros.
  unfold get_undelivered in H.
  apply (Core3_10_2_2_3_2 n n msg dev m H).
Qed.

Lemma Core3_10_2_2_4_1 : forall params gs r i j m, isValid params gs -> message_archive gs r i j = None -> message_archive (step gs) r i j = Some m ->
  i = sender_id m /\ j = receiver_id m /\ r = m_round_no m /\ r = round_no (step gs).
Proof.
  intros.
  remember (step gs) as gs'.
  unfold step in Heqgs'.
  remember (get_undelivered (n gs) (message_archive gs (round_no gs)) (delivered gs (round_no gs))) as sm.
  destruct sm.
  - rewrite Heqgs' in H1.
    simpl in H1.
    congruence.
  - rewrite Heqgs' in H1.
    simpl in H1.
    unfold update_messages in H1.
    unfold step_message in H1.
    unfold step_message_from_to in H1.
    unfold step_round in H1.
    unfold step_round_loc in H1.
    remember (local_states gs i) as ls.
    destruct ls.
    destruct l.
    assert ((extract_round i gs) = Some (hl_round_no ls)).
    unfold extract_round.
    rewrite <- Heqls.
    reflexivity.
    specialize (Core3_8_1 params gs i (hl_round_no ls) H H2).
    intros.
    rewrite H0 in H1.
    remember (r =? round_no gs + 1) as req.
    destruct req.
    assert (r = round_no gs + 1).
    apply (beq_nat_true r (round_no gs + 1) (eq_sym Heqreq)).
    destruct (estimation ls (hl_round_no ls + 1)) ; crush.
    inversion H1.
    rewrite H0 in H1.
    destruct (r =? round_no gs + 1) ; congruence.
Qed.

Definition EqDecOptionMSG : EqDec (option Message) eq.
  assert (EqDec bool eq).
  crush.
  assert (EqDec nat eq).
  crush.
  assert (EqDec (option bool) eq).
  unfold EqDec.
  intros.
  destruct x ; destruct y ; try destruct b ; try destruct b0 ; try (left ; reflexivity) ; try (right ; discriminate).
  assert (EqDec Message eq).
  unfold EqDec.
  intros.
  destruct x ; destruct y.  
  destruct (X0 sender_id sender_id0).
  destruct (X0 receiver_id receiver_id0).
  destruct (X0 m_round_no m_round_no0).
  destruct (X1 vote vote0).
  left.
  congruence.
  right.
  congruence.
  right.
  congruence.
  right.
  congruence.
  right.
  congruence.
  unfold EqDec.
  intros.
  destruct x ; destruct y.
  destruct (X2 m m0).
  left.
  congruence.
  right.
  congruence.
  right.
  discriminate.
  right.
  discriminate.
  left.
  reflexivity.
Defined.


Lemma Core3_10_2_2_4 : forall params gs r i j m, isValid params gs -> message_archive gs r i j = Some m -> i = sender_id m /\ j = receiver_id m /\ r = m_round_no m /\ r <= round_no gs.
Proof.
  intros.
  remember (fun r i j gs => message_archive gs r i j) as message_archive'.
  assert (forall r i j gs, message_archive' r i j gs = message_archive gs r i j).
  crush.
  inversion H.
  remember (initGS params) as gs0.
  destruct r.
  - rewrite <- (Core3_10_2_2_4_2 gs0 gs i j H3) in H0.
    rewrite Heqgs0 in H0.
    unfold initGS in H0.
    simpl in H0.
    unfold update_messages in H0.
    unfold step_message in H0.
    destruct (0 =? 0).
    destruct (i <? f_to_n (numf params)).
    unfold step_message_from_to in H0.
    unfold initLS in H0.
    simpl in H0.
    inversion H0.
    simpl.
    crush.
    inversion H0.
    inversion H0.
  - assert (message_archive' (S r) i j gs0 = None).
    rewrite H1.
    rewrite Heqgs0.
    unfold initGS.
    auto.
    assert (message_archive' (S r) i j gs0 <> message_archive' (S r) i j gs).
    crush.
    specialize EqDecOptionMSG.
    intros.
    specialize (Low_Level_Witness gs0 gs (message_archive' (S r) i j) H3 H5).
    intros.
    destruct H6.
    remember x as gs1.
    forget x.
    destruct H6.
    destruct H7.
    destruct H8.
    assert (message_archive (step gs1) (S r) i j = Some m /\ (round_no (step gs1) <= round_no gs)).
    rewrite H4 in H9.
    rewrite H1 in H9.
    remember (message_archive (step gs1) (S r) i j).
    destruct o.
    specialize (Low_Level_Monotonicity (step gs1) gs H7).
    intros.
    destruct H10.
    destruct H11.
    destruct H12.
    destruct H13.
    destruct H14.
    destruct H15.
    specialize (H15 (S r) i j m0 (eq_sym Heqo)).
    split.
    congruence.
    assumption.
    congruence.
    rewrite H4 in H8.
    rewrite H1 in H8.
    assert (isValid params gs1).
    unfold isValid.
    unfold isValid in H.
    crush.
    destruct H10.
    specialize (Core3_10_2_2_4_1 params gs1 (S r) i j m H11 (eq_sym H8) H10).
    crush.
Qed.

Lemma Core3_10_2_2 : forall params gs r i j m, isValid params gs -> extract_historyrj i gs r j = None -> extract_historyrj i (step gs) r j = Some m ->
  message_archive gs r j i = Some m /\ r = (round_no (step gs)) /\ i < (n gs) /\ j < (n gs).
Proof.
  intros params gs r i j m H'.
  intros.
  specialize (Core3_10_2_2_2 gs r i j m H H0).
  intros.
  destruct H1.
  destruct H2.
  specialize (Core3_10_2_2_1 gs r i j m H H0).
  intros.
  remember (step gs) as gs'.
  unfold step in Heqgs'.
  rewrite H4 in Heqgs'.
  specialize (Core3_10_2_2_3 (n gs) (message_archive gs (round_no gs)) (delivered gs (round_no gs)) m H4).
  intros.
  destruct H5.
  remember x as j0.
  forget x.
  destruct H5.
  remember x as i0.
  forget x.
  destruct H5.
  specialize (Core3_10_2_2_4 params gs (round_no gs) j0 i0 m H' H5).
  intros.
  destruct H6.
  destruct H7.
  destruct H9.
  destruct H10.
  crush.
Qed.

Lemma Core3_10_4_1 : forall params gs r i j m, isValid params gs -> extract_historyrj i gs r j = Some m ->
  exists gs', isValid params gs' /\ (step gs') <<= gs /\ extract_historyrj i gs' r j = None /\ extract_historyrj i (step gs') r j = Some m.
Proof.
  intros.
  remember (fun i r j gs => extract_historyrj i gs r j) as extract_historyrj'.
  assert (forall i r j gs, extract_historyrj' i r j gs = extract_historyrj i gs r j).
  crush.
  inversion H.
  remember (initGS params) as gs0.
  specialize EqDecOptionMSG.
  intros.
  assert (extract_historyrj' i r j gs0 = None).
  rewrite H1.
  rewrite Heqgs0.
  unfold extract_historyrj.
  unfold initGS.
  simpl.
  destruct (i <? f_to_n (numf params)) ; crush.
  assert (extract_historyrj' i r j gs0 <> extract_historyrj' i r j gs).
  congruence.
  specialize (Low_Level_Witness gs0 gs (extract_historyrj' i r j) H3 H5).
  intros.
  destruct H6.
  remember x as gs1.
  forget x.
  destruct H6.
  destruct H7.
  destruct H8.
  assert (extract_historyrj' i r j (step gs1) = Some m).
  remember (extract_historyrj' i r j (step gs1)) as sh.
  destruct sh.
  specialize (Core3_10_2_1 (step gs1) gs r i j m0 H7).
  intros.
  rewrite <- H0.
  rewrite <- H10.
  reflexivity.
  congruence.
  crush.
  exists gs1.
  split.
  unfold isValid.
  split.
  assumption.
  rewrite Heqgs0 in H6.
  assumption.
  crush.
Qed.

Lemma Core3_10_2 : forall params gs r i j m m', isValid params gs -> extract_historyrj i gs r j = Some m -> message_archive gs r j i = Some m' ->
  m = m'.
Proof.
  intros.
  specialize (Core3_10_4_1 params gs r i j m H H0).
  intros.
  destruct H2.
  remember x as gs1.
  forget x.
  destruct H2.
  destruct H3.
  destruct H4.
  specialize (Core3_10_2_2 params gs1 r i j m H2 H4 H5).
  intros.
  destruct H6.
  specialize (Low_Level_Monotonicity gs1 gs (transit gs1 (step gs1) gs (succ gs1) H3)).
  intros.
  destruct H8.
  destruct H9.
  destruct H10.
  destruct H11.
  destruct H12.
  destruct H13.
  specialize (H13 r j i m H6).
  congruence.
Qed.

Lemma Core3_10_3_1_1 : forall params gs i, isValid params gs -> (n gs) <= i -> local_states gs i = None.
Proof.
  intros.
  destruct H.
  remember (initGS params) as gs0.
  induction H1.
  - unfold extract_historyrj in H0.
    rewrite Heqgs0 in H0.
    unfold initGS in H0.
    simpl in H0.
    rewrite Heqgs0.
    unfold initGS.
    simpl.
    remember (i <? f_to_n (numf params)) as inrange.
    destruct inrange.
    assert (i < f_to_n (numf params)).
    eapply (Nat.ltb_lt).
    auto.
    crush.
    auto.
  - rewrite <- (Core3_7 s' (step s') (succ s')) in H0.
    specialize (IHLow_leq Heqgs0 H0).
    unfold step.
    destruct (get_undelivered (n s') (message_archive s' (round_no s')) (delivered s' (round_no s'))).
    simpl.
    unfold step_deliver.
    remember (i =? receiver_id m) as isreceiver.
    destruct isreceiver.
    assert (i = receiver_id m).
    apply (beq_nat_true i (receiver_id m) (eq_sym Heqisreceiver)).
    rewrite <- H2.
    rewrite IHLow_leq.
    auto.
    auto.
    simpl.
    unfold step_round.
    rewrite IHLow_leq.
    auto.
Qed.

(* Simple *)
Lemma Core3_10_3_1 : forall params gs i r j m, isValid params gs -> extract_historyrj i gs r j = Some m -> i < (n gs).
Proof.
  intros.
  remember (le_lt_dec (n gs) i).
  destruct s.
  - specialize (Core3_10_3_1_1 params gs i H l).
    intros.
    unfold extract_historyrj in H0.
    rewrite H1 in H0.
    inversion H0.
  - auto.
Qed.

Lemma Core3_10_3 : forall params gs r i j m eb, isValid params gs -> extract_estimationr i gs r = Some eb -> extract_historyrj j gs r i = Some m ->
  vote m = Some eb.
Proof.
  intros.
  specialize (Core3_10_3_1 params gs j r i m H H1).
  intros.
  specialize (Core3_10_1 params gs r i eb H H0 j H2).
  intros.
  destruct H3.
  destruct H3.
  specialize (Core3_10_2 params gs r j i m x H H1 H3).
  intros.
  congruence.
Qed.

Lemma Core3_10_4 : forall params gs r i j m, isValid params gs -> extract_historyrj i gs r j = Some m -> r <= (round_no gs) /\ j < n gs.
Proof.
  intros.
  specialize (Core3_10_4_1 params gs r i j m H H0).
  intros.
  destruct H1.
  remember x as gs1.
  forget x.
  destruct H1.
  destruct H2.
  destruct H3.
  specialize (Core3_10_2_2 params gs1 r i j m H1 H3 H4).
  intros.
  destruct H5.
  destruct H6.
  destruct H7.
  specialize (Low_Level_Monotonicity (step gs1) gs H2).
  intros.
  destruct H9.
  destruct H10.
  specialize (Core3_7 gs1 (step gs1) (succ gs1)).
  intros.
  crush.
Qed.

Lemma Core3_10_5_1_1 : forall params gs, isValid params gs -> (forall i, i < n gs -> exists b, extract_estimationr i gs (round_no gs) = Some b) ->
  exists gs', gs' <<= gs /\ isValid params gs' /\
  (forall i j, i < n gs' -> j < n gs' -> 
    (exists m b, message_archive gs' (round_no gs') i j = Some m /\ vote m = Some b) 
    /\ delivered gs' (round_no gs') i j = false /\ extract_historyrj j gs' (round_no gs') j = None).
Proof.
Admitted.

(* Hard *)
Lemma Core3_10_5_1_2 : forall params gs, isValid params gs -> 
  (forall i j, i < n gs -> j < n gs -> 
    (exists m b, message_archive gs (round_no gs) i j = Some m /\ vote m = Some b) 
    /\ delivered gs (round_no gs) i j = false /\ extract_historyrj j gs (round_no gs) j = None) ->
  forall gs', gs <<= gs' -> round_no gs' + 1 = round_no (step gs') -> 
  forall i h, i < n gs -> extract_history i gs' = Some h -> 
  (forall j, j < n gs -> message_archive gs (round_no gs) j i = h j).
Proof.
Admitted.

Lemma Core3_10_5_1_3 : forall params n h, (forall i, i < n -> (exists m b, h i = Some m /\ vote m = Some b)) -> cond params n (filter h).
Proof.
  intros.
  unfold cond.
  intros.
  specialize (H i).
  destruct H.
  auto.
  destruct H.
  destruct H.
  destruct x0.
  left.
  unfold filter.
  rewrite H.
  destruct x.
  simpl in H1.
  rewrite H1.
  auto.
  right.
  unfold filter.
  rewrite H.
  destruct x.
  simpl in H1.
  rewrite H1.
  auto.
Qed.

(* Hard ??? *)
Lemma Core3_10_5_1 : forall params gs, isValid params gs -> (forall i, i < n gs -> exists b, extract_estimationr i gs (round_no gs) = Some b) ->
  (forall gs', gs <<= gs' -> round_no gs' + 1 = round_no (step gs') -> (forall j h, j < n gs -> extract_history j gs' = Some h -> cond params (n gs) (filter h))).
Proof.
  intros params gs H H0.
  specialize (Core3_10_5_1_1 params gs H H0).
  intro.
  destruct H1.
  destruct H1.
  destruct H2.
  intros.
  eapply Core3_10_5_1_3.
  intros.
  specialize (Core3_7 x gs H1).
  intros.
  rewrite <- H9 in H6.
  rewrite <- H9 in H8.
  specialize (Core3_10_5_1_2 params x H2 H3 gs' (transit x gs gs' H1 H4) H5 j h H6 H7 i H8).
  intros.
  specialize (H3 i j H8 H6).
  rewrite H10 in H3.
  destruct H3.
  apply H3.
Qed.

Lemma Core3_10_5_2 : forall n m sqs h b i, i < m -> check_quorum_infer n (sqs i) (filter h) = Some b -> exists b', testall n m sqs h = Some b'.
Proof.
  intros.
  induction m.
  inversion H.
  inversion H.
  unfold testall.
  unfold testone.
  exists b.
  rewrite H2 in H0.
  rewrite H0.
  auto.
  unfold testall.
  destruct (testone n (sqs m) h).
  exists b0.
  auto.
  fold testall.
  apply IHm ; auto.
Qed.

Lemma Core3_10_5 : forall params gs r i, isValid params gs -> r <= round_no gs -> i < n gs -> exists b, extract_estimationr i gs r = Some b.
Proof.
  intros.
  destruct H.
  remember (initGS params) as gs0.
  generalize dependent i.
  generalize dependent r.
  induction H2.
  - intros.
    destruct params.
    unfold initGS in Heqgs0.
    rewrite Heqgs0 in H0.
    simpl in H0.
    inversion H0.
    rewrite Heqgs0.
    simpl.
    unfold extract_estimationr.
    simpl.
    assert ((i <? (f_to_n numf)) = true).
    rewrite Heqgs0 in H1.
    simpl in H1.
    eapply (Nat.ltb_lt).
    auto.
    rewrite H3.
    unfold initLS.
    simpl.
    exists (inputs i).
    auto.
  - remember (succ s') as H'.
    clear HeqH'.
    remember (step s') as s''.
    assert (s'' = step s').
    auto.
    unfold step in Heqs''.
    destruct (get_undelivered (n s') (message_archive s' (round_no s')) (delivered s' (round_no s'))).
    + rewrite Heqs''.
      simpl.
      intros.
      simpl in H1.
      specialize (IHLow_leq Heqgs0 r H1 i H3).
      destruct IHLow_leq.
      exists x.
      rewrite <- H4.
      unfold extract_estimationr.
      simpl.
      unfold step_deliver.
      remember (i =? receiver_id m) as isreceiver.
      destruct isreceiver.
      assert (i = receiver_id m).
      apply (beq_nat_true i (receiver_id m) (eq_sym Heqisreceiver)).
      rewrite <- H5.
      destruct (local_states s' i).
      unfold step_deliver_loc.
      destruct l.
      simpl.
      reflexivity.
      reflexivity.
      reflexivity.
    + intros.
      rewrite Heqs'' in H3.
      simpl in H3.
      rewrite Heqs'' in H1.
      simpl in H1.
      inversion H1.
      * rewrite Heqs''.
        unfold extract_estimationr.
        simpl.
        unfold step_round.
        specialize (Low_Level_Monotonicity s s' H2).
        intros.
        destruct H5.
        destruct H6.
        rewrite <- H6 in H3.
        destruct H7.
        destruct H8.
        destruct H9.
        rewrite Heqgs0 in H9.
        unfold initGS in H9.
        simpl in H9.
        assert (i <? f_to_n (numf params) = true).
        rewrite Heqgs0 in H3.
        unfold initGS in H3.
        simpl in H3.
        eapply (Nat.ltb_lt).
        auto.
        specialize (H9 i).
        rewrite H11 in H9.
        remember (initLS i (inputs params i)) as ls0.
        specialize (H9 ls0 (eq_refl (Some ls0))).
        destruct H9.
        destruct H9.
        rewrite H9.
        unfold step_round_loc.
        destruct x.
        assert (hl_round_no ls = round_no s').
        assert (extract_round i s' = Some (hl_round_no ls)).
        unfold extract_round.
        rewrite H9.
        reflexivity.
        assert (isValid params s').
        unfold isValid.
        crush.
        apply (Core3_8_1 params s' i (hl_round_no ls) H14 H13).
        rewrite H13.
        rewrite <- H4.
        remember (estimation ls r).
        destruct o.
        simpl.
        exists b.
        congruence.
        simpl.
        assert (r =? r = true).
        eapply (beq_nat_true_iff).
        auto.
        rewrite H14.
        remember (history ls (hl_round_no ls)) as h.
        assert (isValid params s').
        unfold isValid.
        crush.
        assert (round_no s' + 1 = round_no (step s')).
        rewrite <- H0.
        rewrite Heqs''.
        simpl.
        reflexivity.
        assert (extract_history i s' = Some h).
        unfold extract_history.
        rewrite H9.
        congruence.
        assert (round_no s' <= round_no s').
        auto.
        specialize (IHLow_leq Heqgs0 (round_no s') H18).
        rewrite H6 in H3.
        specialize (Core3_10_5_1 params s' H15 IHLow_leq s' (reflex s') H16 i h H3 H17).
        intros.
        destruct H.
        assert (f_to_n (numf params) = n s').
        rewrite <- H6.
        rewrite Heqgs0.
        unfold initGS.
        simpl.
        reflexivity.
        rewrite <- H21 in H19.
        specialize (H (filter h) H19).
        destruct H.
        destruct H.
        destruct H.
        destruct H.
        destruct H22.
        unfold estimate.
        rewrite <- H8.
        rewrite Heqgs0.
        unfold initGS.
        simpl.
        rewrite H13 in Heqh.
        rewrite <- Heqh.
        destruct params.
        simpl.
        simpl in H22.
        destruct coq_cq.
        simpl in H22.
        simpl in H.
        simpl in H21.
        rewrite <- H21.
        eapply Core3_10_5_2.
        apply H.
        apply H22.
      * assert (m = round_no s').
        crush.
        rewrite H6 in H5.
        specialize (IHLow_leq Heqgs0 r H5 i H3).
        destruct IHLow_leq.
        exists x.
        rewrite <- H7.
        rewrite Heqs''.
        unfold extract_estimationr.
        simpl.
        unfold step_round.
        remember (local_states s' i) as ls.
        destruct ls.
        unfold step_round_loc.
        destruct l.
        assert (hl_round_no ls = round_no s').
        assert (extract_round i s' = Some (hl_round_no ls)).
        unfold extract_round.
        rewrite <- Heqls.
        reflexivity.
        assert (isValid params s').
        unfold isValid.
        crush.
        apply (Core3_8_1 params s' i (hl_round_no ls) H9 H8).
        destruct (estimation ls (hl_round_no ls + 1)).
        simpl.
        reflexivity.
        simpl.
        rewrite H8.
        assert (r =? round_no s' + 1 = false).
        clear Heqgs0 H2 Heqs'' H0 H1 H6 H3 Heqls H7 H' H8 H4.
        remember (round_no s') as n'.
        clear Heqn'.
        rewrite (beq_nat_false_iff).
        generalize dependent n'.
        generalize dependent r.
        induction n' ; induction r ; crush.
        rewrite H9.
        reflexivity.
        reflexivity.
Qed.

Lemma Core3_10 : forall params gs r i j k mj mk, isValid params gs -> extract_historyrj j gs r i = Some mj -> extract_historyrj k gs r i = Some mk ->
  vote mj = vote mk.
Proof.
  intros.
  specialize (Core3_10_4 params gs r j i mj H H0).
  intros.
  destruct H2.
  specialize (Core3_10_5 params gs r i H H2 H3).
  intros.
  destruct H4.
  specialize (Core3_10_3 params gs r i j mj x H H4 H0).
  specialize (Core3_10_3 params gs r i k mk x H H4 H1).
  intros.
  congruence.
Qed.

(* Trivial *)
Lemma Core4_1_1_1 : forall params gs i b, isValid params gs -> extract_estimationr i gs (round_no gs) = Some b -> 0 < (round_no gs) ->
  exists h, extract_historyr i gs (round_no gs - 1) = Some h.
Proof.
  intros.
  unfold extract_estimationr in H0.
  unfold extract_historyr.
  destruct (local_states gs i).
  destruct l.
  exists (history ls (round_no gs - 1)).
  auto.
  congruence.
Qed.

Lemma Core4_1_1_2_1 : forall params gs gs' i, isValid params gs -> gs <<= gs' -> (round_no gs + 1 = round_no (step gs)) ->
  extract_historyr i gs (round_no gs) = extract_historyr i gs' (round_no gs).
Proof.
  intros.
  induction H0.
  reflexivity.
  specialize (IHLow_leq H H1).
  assert (round_no s < round_no (step s')).
  clear IHLow_leq.
  induction H0.
  crush.
  specialize (IHLow_leq H H1).
  specialize (Core4_1_2_1 (step s')).
  intros.
  destruct H2 ; crush.
  rewrite IHLow_leq.
  clear IHLow_leq.
  unfold step.
  unfold extract_historyr.
  remember (get_undelivered (n s') (message_archive s' (round_no s')) (delivered s' (round_no s'))) as sm.
  destruct sm.
  simpl.
  unfold step_deliver.
  remember (i =? receiver_id m) as isreceiver.
  destruct isreceiver.
  assert (i = receiver_id m).
  apply (beq_nat_true i (receiver_id m) (eq_sym Heqisreceiver)).
  rewrite <- H3.
  remember (local_states s' i) as ls.
  destruct ls.
  destruct l.
  unfold step_deliver_loc.
  simpl.
  match goal with
  | [H : _ |- Some ?f1 = Some ?f2] => assert (f1 = f2)
  end.
  eapply fun_eqiv.
  intros.
  remember (history ls (round_no s) x) as m0.
  remember (history ls (m_round_no m) (sender_id m)) as m1.
  destruct m1.
  auto.
  remember (round_no s =? m_round_no m) as isround.
  remember (x =? sender_id m) as issender.
  destruct isround.
  destruct issender.
  simpl.
  rewrite <- Heqm0.
  destruct m0.
  auto.
  assert (isValid params s').
  unfold isValid.
  unfold isValid in H.
  destruct H.
  split.
  auto.
  eapply transit.
  apply H4.
  assumption.
  assert (extract_historyrj i s' (round_no s) x = None).
  unfold extract_historyrj.
  rewrite <- Heqls.
  congruence.
  assert (extract_historyrj i (step s') (round_no s) x = Some m).
  unfold extract_historyrj.
  unfold step.
  rewrite <- Heqsm.
  simpl.
  unfold step_deliver.
  rewrite <- Heqisreceiver.
  rewrite <- H3.
  rewrite <- Heqls.
  unfold step_deliver_loc.
  simpl.
  rewrite <- Heqm1.
  rewrite <- Heqisround.
  rewrite <- Heqissender.
  simpl.
  rewrite <- Heqm0.
  auto.
  specialize (Core3_10_2_2 params s' (round_no s) i x m H4 H5 H6).
  intros.
  destruct H7.
  destruct H8.
  rewrite H8 in H2.
  crush.
  simpl.
  auto.
  simpl.
  auto.
  destruct (history ls (m_round_no m) (sender_id m)).
  auto.
  congruence.
  auto.
  auto.
  simpl.
  unfold step_round.
  unfold step_round_loc.
  destruct (local_states s' i).
  destruct l.
  destruct (estimation ls (hl_round_no ls + 1)).
  auto.
  auto.
  auto.
Qed.

Lemma Core4_1_1_2_2 : forall n cq h b, estimate n cq h = Some b -> exists qi, qi < coq_k cq /\ testone n (coq_csq cq qi) h = Some b.
Proof.
  intros.
  unfold estimate in H.
  destruct cq.
  simpl.
  induction coq_k.
  inversion H.
  unfold testall in H.
  remember (testone n (coq_csq coq_k) h) as sb.
  destruct sb.
  exists coq_k.
  crush.
  fold testall in H.
  specialize (IHcoq_k H).
  destruct IHcoq_k.
  exists x.
  crush.
Qed.

Lemma Core4_1_1_2 : forall params gs i b h, isValid params gs -> extract_estimationr i gs (round_no gs) = Some b -> 0 < (round_no gs) ->
  extract_historyr i gs (round_no gs - 1) = Some h ->
  exists cqi, cqi < coq_k (CQ gs) /\ testone (n gs) (coq_csq (CQ gs) cqi) h = Some b.
Proof.
  intros.
  specialize (Core3_10_1_2 params gs (round_no gs) i b H H0 H1).
  intros.
  destruct H3.
  remember x as gs0.
  forget x.
  destruct H3.
  destruct H4.
  destruct H5.
  unfold step in H6.
  remember (get_undelivered (n gs0) (message_archive gs0 (round_no gs0)) (delivered gs0 (round_no gs0))) as sm.
  destruct sm.
  unfold extract_estimationr' in H6.
  unfold extract_estimationr' in H5.
  simpl in H6.
  unfold step_deliver in H6.
  remember (i =? receiver_id m) as isreceiver.
  destruct isreceiver.
  assert (i = receiver_id m).
  apply (beq_nat_true i (receiver_id m) (eq_sym Heqisreceiver)).
  rewrite <- H7 in H6.
  destruct (local_states gs0 i).
  unfold step_deliver_loc in H6.
  destruct l.
  simpl in H6.
  congruence.
  inversion H6.
  congruence.
  unfold extract_estimationr' in H6.
  unfold extract_estimationr' in H5.
  simpl in H6.
  unfold step_round in H6.
  remember (local_states gs0 i) as ls.
  destruct ls.
  unfold step_round_loc in H6.
  destruct l.
  destruct (estimation ls (hl_round_no ls + 1)).
  simpl in H6.
  congruence.
  simpl in H6.
  remember (round_no gs =? hl_round_no ls + 1) as isround.
  destruct isround.
  assert (round_no gs = hl_round_no ls + 1).
  eapply beq_nat_true.
  auto.
  assert (hl_round_no ls = round_no gs0).
  apply (Core3_8_1 params gs0 i (hl_round_no ls) H3).
  unfold extract_round.
  rewrite <- Heqls.
  reflexivity.  
  assert (round_no gs0 + 1 = round_no (step gs0)).
  unfold step.
  rewrite <- Heqsm.
  auto.
  assert (extract_historyr i gs0 (hl_round_no ls) = Some h).
  specialize (Core4_1_1_2_1 params gs0 gs i H3 (transit gs0 (step gs0) gs (succ gs0) H4) H9).
  intros.
  rewrite H7 in H2.
  assert (hl_round_no ls + 1 - 1 = hl_round_no ls).
  crush.
  congruence.
  unfold extract_historyr in H10.
  rewrite <- Heqls in H10.
  inversion H10.
  rewrite H12.
  rewrite H12 in H6.
  specialize (Low_Level_Monotonicity gs0 gs (transit gs0 (step gs0) gs (succ gs0) H4)).
  intros.
  destruct H11.
  destruct H13.
  destruct H14.
  destruct H15.
  rewrite <- H13.
  rewrite <- H15.
  eapply (Core4_1_1_2_2).
  assumption.
  congruence.
  congruence.
Qed.

Lemma Core4_1_1_3 : forall gs gs', gs <<= gs' -> step gs <<= step gs'.
Proof.
  intros.
  induction H.
  constructor.
  constructor.
  auto.
Qed.


Lemma Core4_1_1 : forall params gs i b, isValid params gs -> extract_decision i gs = None -> extract_decision i (step gs) = Some b -> 
  (forall gs', gs <<= gs' -> (S (round_no gs) = round_no gs') -> (forall j b0, extract_estimationr j gs' (round_no gs') = Some b0 ->
  b = b0)).
Proof.
  intros.
  specialize (Core3_1 (step gs) i b H1).
  intros.
  destruct H5.
  remember x as h.
  forget x.
  specialize (Core3_2 gs i b h H0 H1 H5).
  intros.
  destruct H6.
  remember x as qi.
  forget x.
  destruct H6.
  assert (isValid params gs').
  unfold isValid.
  inversion H.
  split.
  assumption.
  apply (transit (initGS params) gs gs' H9 H2).
  assert (0 < round_no gs').
  destruct (round_no gs') ; crush.
  (* Temporary solution *)
  rename H9 into H9'.
  specialize (Core4_1_1_1 params gs' j b0 H8 H4 H9').
  intros.
  destruct H9.
  remember x as hj.
  forget x.
  specialize (Core4_1_1_2 params gs' j b0 hj H8 H4 H9' H9).
  intros.
  destruct H10.
  remember x as cqj.
  forget x.
  destruct H10.
  specialize (Core3_3 params (step gs) (Core3_4 params gs H)).
  specialize (Core3_3 params gs' H8).
  specialize (Core3_5 params (step gs) (Core3_4 params gs H)).
  intros.
  rewrite <- H13 in H11.
  rewrite H14 in H11.
  rewrite <- H13 in H10.
  rewrite H14 in H10.
  specialize (Core3_7 gs gs' H2).
  specialize (Core3_7 gs (step gs) (succ gs)).
  intros.
  rewrite H15 in H16.
  rewrite <- H16 in H11.
  destruct H12.
  destruct H17.
  (* Temporary solution *)
  rename H17 into H17'.
  rename H18 into H17.
  remember (H17 qi cqj H6 H10) as H18.
  clear HeqH18 H17.
  destruct H18.
  remember x as k.
  forget x.
  destruct H17.
  destruct H18.
  specialize (Core3_6 (n (step gs)) b h (coq_sq (CQ (step gs)) qi) k H7 H17 H18).
  intros.
  destruct H20.
  remember x as mi.
  forget x.
  specialize (Core3_6 (n (step gs)) b0 hj (coq_csq (CQ (step gs)) cqj) k H11 H17 H19).
  intros.
  destruct H21.
  remember x as mj.
  forget x.
  destruct H20.
  destruct H21.
  assert (step gs <<= gs').
  inversion H2.
  rewrite H25 in H6.
  crush.
  apply (Core4_1_1_3 gs s' H24).
  specialize (Core3_8 params (step gs) gs' i h k mi (Core3_4 params gs H) H24 H5 H20).
  intros.
  assert (extract_historyrj j gs' (round_no gs' - 1) k = Some mj).
  unfold extract_historyrj.
  unfold extract_historyr in H9.
  destruct (local_states gs' j).
  destruct l.
  inversion H9.
  congruence.
  inversion H9.
  specialize (Core3_9 gs i b H0 H1).
  intros.
  rewrite <- H27 in H25.
  rewrite <- H3 in H26.
  simpl in H26.
  assert (round_no gs - 0 = round_no gs).
  crush.
  rewrite H28 in H26.
  specialize (Core3_10 params gs' (round_no gs) k i j mi mj H8 H25 H26).
  intros.
  congruence.
Qed.



(* Simple *)
Lemma Core4_1_2_3 : forall gs gs' r i b, gs <<= gs' -> round_no gs = round_no gs' -> extract_estimationr i gs' r = Some b -> extract_estimationr i gs r = Some b.
Proof.
  intros.
  induction H.
  - auto.
  - assert (round_no s = round_no s').
    specialize (Core4_1_2_1 s').
    intros.
    assert (round_no s <= round_no s').
    specialize (Low_Level_Monotonicity s s' H).
    intros.
    destruct H3.
    auto.
    destruct H2 ; crush.
    rewrite IHLow_leq ; auto.
    remember (step s') as s''.
    unfold step in Heqs''.
    destruct (get_undelivered (n s') (message_archive s' (round_no s')) (delivered s' (round_no s'))).
    rewrite Heqs'' in H1.
    rewrite <- H1.
    unfold extract_estimationr.
    unfold step_deliver.
    simpl.
    remember (i =? receiver_id m) as isreceiver.
    destruct isreceiver.
    assert (i = receiver_id m).
    eapply (beq_nat_true).
    auto.
    rewrite <- H3.
    destruct (local_states s' i).
    destruct l.
    unfold step_deliver_loc.
    simpl.
    auto.
    auto.
    auto.
    rewrite Heqs'' in H0.
    simpl in H0.
    crush.
Qed.

(* Simple *)
Lemma Core4_1_2_4 : forall params gs r i b, isValid params gs -> extract_estimationr i gs r = Some b -> i < (n gs).
Proof.
  intros.
  remember (le_lt_dec (n gs) i).
  destruct s.
  - specialize (Core3_10_3_1_1 params gs i H l).
    intros.
    unfold extract_estimationr in H0.
    rewrite H1 in H0.
    inversion H0.
  - auto.
Qed.

(* Simple *)
Lemma Core4_1_2_5 : forall n sq h b, testone n sq h = Some b -> exists k, k < n /\ sq k = true.
Proof.
  intros.
  unfold testone in H.
  specialize (Core3_6_3 n sq (filter h) b H).
  intros.
  destruct H0.
  exists x.
  tauto.
Qed.

(* Trivial *)
Lemma Core4_1_2_6 : forall gs r i, round_no gs < round_no (step gs) -> extract_historyr i gs r = extract_historyr i (step gs) r.
Proof.
  intros.
  remember (step gs) as gs'.
  unfold step in Heqgs'.
  destruct (get_undelivered (n gs) (message_archive gs (round_no gs)) (delivered gs (round_no gs))).
  rewrite Heqgs' in H.
  crush.
  rewrite Heqgs'.
  unfold extract_historyr.
  simpl.
  unfold step_round.
  destruct (local_states gs i).
  destruct l.
  unfold step_round_loc.
  destruct (estimation ls (hl_round_no ls + 1)).
  auto.
  auto.
  auto.
Qed.

(* Hard *)
Lemma Core4_1_2 : forall params gs b, isValid params gs -> (forall i b0, extract_estimationr i gs (round_no gs) = Some b0 -> b = b0) ->
  (forall gs', gs <<= gs' -> (forall j b', extract_estimationr j gs' (round_no gs') = Some b' -> b = b')).
Proof.
  intros params gs b H H1 gs' H2.
  induction H2.
  auto.
  remember (IHLow_leq H H1) as H3.
  clear HeqH3 IHLow_leq.
  specialize (Core4_1_2_1 s').
  intro.
  destruct H0.
  - intros.
    apply (H3 j).
    rewrite <- H0 in H4.
    apply (Core4_1_2_3 s' (step s') (round_no s') j b' (succ s') H0 H4).
  - intros.
    assert (isValid params s').
    unfold isValid.
    unfold isValid in H.
    destruct H.
    split.
    assumption.
    apply (transit (initGS params) s s' H5 H2).
    assert (0 < round_no (step s')).
    destruct (round_no (step s')) ; crush.
    (* Temporary solution *)
    rename H6 into H6'.
    specialize (Core4_1_1_1 params (step s') j b' (Core3_4 params s' H5) H4 H6').
    intros.
    destruct H6.
    remember x as h.
    forget x.
    assert (round_no (step s') - 1 = round_no s').
    crush.
    specialize (Core4_1_1_2 params (step s') j b' h (Core3_4 params s' H5) H4 H6' H6).
    intros.
    destruct H8.
    remember x as cqj.
    forget x.
    destruct H8.
    specialize (Core4_1_2_5 (n (step s')) (coq_csq (CQ (step s')) cqj) h b' H9).
    intros.
    destruct H10.
    remember x as k.
    forget x.
    destruct H10.
    assert (round_no s' <= round_no s').
    auto.
    specialize (Core3_7 s' (step s') (succ s')).
    intros.
    rewrite <- H13 in H10.
    specialize (Core3_10_5 params s' (round_no s') k H5 H12 H10).
    intros.
    destruct H14.
    remember x as b0.
    forget x.
    remember (H3 k b0 H14) as H15.
    rewrite H15.
    clear HeqH15 H15.
    rewrite H13 in H10.
    specialize (Core3_6 (n (step s')) b' h (coq_csq (CQ (step s')) cqj) k H9 H10 H11).
    intros.
    destruct H15.
    remember x as m.
    forget x.
    destruct H15.
    rewrite H7 in H6.
    assert (round_no s' < round_no (step s')).
    crush.
    specialize (Core4_1_2_6 s' (round_no s') j H17).
    intros.
    rewrite <- H18 in H6.
    assert (extract_historyrj j s' (round_no s') k = Some m).
    unfold extract_historyrj.
    unfold extract_historyr in H6.
    destruct (local_states s' j).
    destruct l.
    congruence.
    inversion H6.
    specialize (Core3_10_3 params s' (round_no s') k j m b0 H5 H14 H19).
    congruence.
Qed.

(* Trivial *)
Lemma Core4_1_3 : forall gs gs', gs <<= gs' -> (round_no gs < round_no gs') -> exists gs'', gs <<= gs'' /\ gs'' <<= gs' /\ (S (round_no gs) = round_no gs'').
Proof.
  intros.
  induction H.
  crush.
  inversion H0.
  - exists (step s').
    split.
    apply (transit s s' (step s') H (succ s')).
    split.
    eapply reflex.
    auto.
  - assert (round_no s < (round_no s')).
    specialize (Core4_1_2_1 s').
    intros.
    destruct H3.
    crush.
    crush.
    specialize (IHLow_leq H3).
    destruct IHLow_leq.
    exists x.
    crush.
    apply (transit x s' (step s') H4 (succ s')).
Qed. 

Lemma Core4_1 : forall params gs i b, isValid params gs -> extract_decision i gs = None -> extract_decision i (step gs) = Some b -> 
  (forall gs', gs <<= gs' -> (round_no gs < round_no gs') -> (forall j b0, extract_estimationr j gs' (round_no gs') = Some b0 ->
  b = b0)).
Proof.
  intros.
  specialize (Core4_1_3 gs gs' H2 H3).
  intros.
  destruct H5.
  remember x as gs''.
  forget x.
  destruct H5.
  destruct H6.
  specialize (Core4_1_1 params gs i b H H0 H1 gs'' H5 H7).
  intros.
  apply (Core4_1_2 params gs'' b (Core3_4_1 params gs gs'' H H5) H8 gs' H6 j b0 H4).
Qed.


(* not validity since it does not necessarily decides *)
Lemma Core4_2 : forall params gs i b b0, isValid params gs -> extract_decision i gs = None -> extract_decision i (step gs) = Some b -> 
  (forall j, j < (n gs) -> extract_estimationr j gs (round_no gs) = Some b0) -> b = b0.
Proof.
  intros.
  specialize (Core3_1 (step gs) i b H1).
  intros.
  destruct H3.
  remember x as h.
  forget x.
  specialize (Core3_2 gs i b h H0 H1 H3).
  intros.
  destruct H4.
  remember x as qi.
  forget x.
  destruct H4.
  specialize (Core4_1_2_5 (n (step gs)) (coq_sq (CQ (step gs)) qi) h b H5).
  intros.
  destruct H6.
  remember x as k.
  forget x.
  destruct H6.
  specialize (Core3_6 (n (step gs)) b h (coq_sq (CQ (step gs)) qi) k H5 H6 H7).
  intros.
  destruct H8.
  remember x as m.
  forget x.
  destruct H8.
  specialize (Core3_7 gs (step gs) (succ gs)).
  intros.
  rewrite <- H10 in H6.
  remember (H2 k H6) as H11.
  specialize (Core3_9 gs i b H0 H1).
  intros.
  clear HeqH11.
  rewrite H12 in H11.
  specialize (Core4_1_2_2 gs (step gs) (round_no (step gs)) k b0 (succ gs) H11).
  intros.
  specialize (Core3_8 params (step gs) (step gs) i h k m (Core3_4 params gs H) (reflex (step gs)) H3 H8).
  intros.
  specialize (Core3_10_3 params (step gs) (round_no (step gs)) k i m b0 (Core3_4 params gs H) H13 H14).
  intros.
  congruence.
Qed.

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
    destruct H19.
    (* Temporary Solution *)
    rename H18 into H18'.
    rename H19 into H18.
    rename H20 into H19.
    unfold n_Quorum_valid in H18.
    simpl in H18.
    specialize (H18 qi qj H0 H13) as H20.
    destruct H20.
    remember x as k.
    forget x.
    destruct H20.
    destruct H21.
    specialize (Core3_6 (n (step gs)) b hi (coq_sq (CQ (step gs)) qi) k H14 H20 H21).
    assert (step gs0 <<= step gs).
    apply (transit (step gs0) gs (step gs)).
    assumption.
    apply (succ gs).
    rewrite (Core3_7 (step gs0) (step gs) H23) in H15.
    specialize (Core3_6 (n (step gs)) b0 hj (coq_sq (CQ (step gs)) qj) k H15 H20 H22).
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
    forget gs'.
    specialize (Core4_1 params gs0 j b0 H4 H6 H7 gs H8 H12).
    intros.
    assert (forall j, j < (n gs) -> extract_estimationr j gs (round_no gs) = Some b0).
    + intros.
      assert (0 < round_no gs).
      destruct (round_no (step gs0)) ; crush.
      assert (round_no gs <= round_no gs).
      crush.
      specialize (Core3_10_5 params gs (round_no gs) j0 H H11 H9).
      intros.
      destruct H13.
      rewrite (H0 j0 x H13).
      auto.
    + clear H0.
      apply (Core4_2 params gs i b b0 H H1 H3 H9).
Qed.


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
      destruct (estimation ls (hl_round_no ls + 1)).
      auto.
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
          assert (fl 0 sender_id receiver_id = fr 0 sender_id receiver_id).
          rewrite H7 ; auto.
          rewrite Heqfl in H.
          rewrite Heqfr in H.
          simpl in H.
          assert ((sender_id =? sender_id) = true).
          eapply Nat.eqb_eq.
          auto.
          assert ((receiver_id =? receiver_id) = true).
          eapply Nat.eqb_eq.
          auto.
          rewrite H0 in H.
          rewrite H1 in H.
          simpl in H.
          inversion H.
        }
        inversion H6.
        destruct round_no ; inversion H0.
      * rewrite <- Heqinits ; auto.
    + remember (IHLow_leq H2 Heqinits) as H'.
      unfold HisValid in H'.
      eapply HMANY.
      apply H'.
      eapply Refinement.
      apply H2.
Qed.
