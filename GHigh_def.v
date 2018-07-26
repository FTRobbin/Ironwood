(* Definition of high-level semantics *)
Require Import List Relations CpdtTactics.

(* Model *)
Record HLocalState := HHonest {hhl_input: bool; hhl_decision: option bool}.

Definition HGlobalState := list HLocalState.

Definition wf_init_ls (ls : HLocalState) : Prop :=
  hhl_decision ls = None.

Definition wf_init_gs (gs : HGlobalState) : Prop := Forall wf_init_ls gs.

(* Semantics *)
Inductive HStep : HGlobalState -> HGlobalState -> Prop :=
| NOTHING : forall gs, HStep gs gs
| DECIDE : forall gs1 ls gs2 b,
    (forall ls', In ls' (gs1 ++ ls::gs2) -> hhl_decision ls' = None) ->
    HStep (gs1 ++ ls::gs2) (gs1 ++ (HHonest (hhl_input ls) (Some b))::gs2)
| AGREE : forall gs1 ls gs2 b ls',
    In ls' (gs1 ++ ls::gs2) ->
    hhl_decision ls' = Some b ->
    HStep (gs1 ++ ls::gs2) (gs1 ++ (HHonest (hhl_input ls) (Some b))::gs2).

(* Note, an alternative would be to remove NOTHING from HStep and define HSteps
   to be the reflexive, transitive closure instead of just the transitive closure. *)
Definition HSteps := clos_trans_1n _ HStep.

Record HInitialParams := HInitP {h_inputs : list bool}.

Definition HinitLS (b:bool) := HHonest b None.

Definition HinitGS (params : HInitialParams) :=
  List.map HinitLS (h_inputs params).

Definition HisValid (params : HInitialParams) (gs:HGlobalState) :=
  HSteps (HinitGS params) gs.

Definition hls_agree b (ls : HLocalState) : Prop :=
  match hhl_decision ls with
  | None => True
  | Some b' => b = b'
  end.

Definition hgs_agree b (gs : HGlobalState) : Prop := Forall (hls_agree b) gs.

Definition agree (gs : HGlobalState) : Prop := exists b, hgs_agree b gs.

Lemma hgs_agree_inv : forall b gs1 ls gs2, hgs_agree b (gs1 ++ ls::gs2) -> hls_agree b ls.
Proof.
  induction gs1 ; crush ; inversion H ; crush ; eauto. 
Qed.

Lemma Hextract_agree : forall gs1 ls gs2 b, hhl_decision ls = Some b -> agree (gs1++ls::gs2) ->
                                            hgs_agree b (gs1 ++ ls :: gs2).
Proof.
  intros gs1 ls gs2 b H1 [b' H2]. 
  pose (hgs_agree_inv _ _ _ _ H2). 
  destruct ls ; crush.
Qed.

Lemma in_hgs_agree : forall ls b b' gs, hhl_decision ls = Some b -> In ls gs -> hgs_agree b' gs -> b = b'.
Proof.
  induction gs ; crush ; inversion H1 ; subst.
  + destruct ls ; crush.
  + apply H3 ; crush.
Qed.

Lemma hgs_agree_app : forall b gs1 gs2, hgs_agree b (gs1 ++ gs2) <-> hgs_agree b gs1 /\ hgs_agree b gs2.
Proof.
 induction gs1 ; crush. constructor.
 inversion H ; clear H ; subst.
 apply Forall_cons ; crush.
 specialize (IHgs1 gs2). destruct IHgs1.
 specialize (H H3). destruct H. auto.
 inversion H ; clear H ; subst.
 specialize (IHgs1 gs2). destruct IHgs1.
 specialize (H H3). destruct H ; auto.
 inversion H0 ; clear H0 ; subst.
 apply Forall_cons ; crush.
 specialize (IHgs1 gs2).
 apply IHgs1 ; auto.
Qed.

Lemma hgs_agree_c : forall b gs1 ls gs2, hgs_agree b (gs1 ++ ls::gs2) <->
                                         hgs_agree b gs1 /\ hls_agree b ls /\ hgs_agree b gs2.
Proof.
  intros ; split ; intros.
  rewrite hgs_agree_app in H. destruct H.
  inversion H0 ; subst. crush.
  destruct H as [H1 [H2 H3]].
  rewrite hgs_agree_app. crush.
  apply Forall_cons ; crush.
Qed.
  
Lemma Hstep_keeps_agreement : forall gs gs', HStep gs gs' -> agree gs -> agree gs'.
Proof.
  intros gs gs' H.
  inversion H ; clear H ; crush.
  + clear H. exists b. induction gs1 ; crush.
    * apply Forall_cons. unfold hls_agree ; crush.
      induction gs2 ; crush. 
      apply Forall_cons. unfold hls_agree. rewrite (H0 a) ; crush.
      apply IHgs2. crush.
    * apply Forall_cons.
      - unfold hls_agree. rewrite H0 ; crush.
      - apply IHgs1 ; crush.
 + destruct H as [b' H].
   generalize (in_hgs_agree _ _ _ _ H1 H0 H) ; intro ; subst.
   exists b'.
   rewrite hgs_agree_c in * ; crush.
Qed.

Lemma Hsteps_keeps_agreement : forall gs gs', HSteps gs gs' -> agree gs -> agree gs'.
Proof.
  induction 1 ; intros ; generalize (Hstep_keeps_agreement _ _ H) ; auto.
Qed.

Lemma HinitGS_keeps_agreement : forall input, agree (HinitGS (HInitP input)).
Proof.
  intros. exists true. unfold HinitGS ; simpl.
  induction input ; simpl. econstructor.
  apply Forall_cons ; crush.
  unfold HinitLS. unfold hls_agree. simpl. auto.
Qed.

Lemma HAgreement : forall params gs, HisValid params gs -> agree gs.
Proof.
  intros.
  apply (Hsteps_keeps_agreement (HinitGS params) gs H).
  apply HinitGS_keeps_agreement.
Qed.