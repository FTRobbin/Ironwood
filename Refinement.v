(* Refinement Theorem *)

Require Import Program Arith List CpdtTactics.

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

Theorem Refinement : forall params gs, isValid params gs -> HStep (ref_map gs) (ref_map (step gs)).
Proof.
Admitted.

Theorem Refinement' : forall params gs, isValid params gs -> HisValid (ref_mapp params) (ref_map gs).
Proof.
Admitted.

(*
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
*)