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
                admit.
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
Admitted.


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
