(* Theorems about high level protocol *)

Require Import Program Arith CpdtTactics High_def.

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
    remember (i0 <? hg_n0) as inrange_i0.
    remember (j <? hg_n0) as inrange_j.
    destruct (inrange_i0) ; unfold agree'; auto.
    destruct (inrange_j).
    + remember (i0 =? i) as isi_i0.
      remember (j =? i) as isi_j.
      destruct (isi_i0).
      destruct (isi_j). 
      * remember (Hextract_loc match h_localstates0 i with
                   | Some ls => Some (Hstep_decide_loc ls b)
                   | None => None
                   end) as hi.
        destruct hi ; auto.
      * remember (Hextract_loc match h_localstates0 i with
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
    + destruct (Hextract_loc (if i0 =? i then match h_localstates0 i with
                                    | Some ls => Some (Hstep_decide_loc ls b)
                                    | None => None
                                    end else h_localstates0 i0)) ; auto.
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
    remember hg_n as n. 
    remember h_localstates as localstates.
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

Theorem HinitGS_keeps_agreement : forall input n0, agree (HinitGS (HInitP input n0)).
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

