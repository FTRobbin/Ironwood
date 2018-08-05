(* Theorems about low level protocol *)

Require Import Program Arith CpdtTactics.

Require Import Refinement Temporal Low_def High_proof Quorum.

Theorem Low_Level_Agreement : forall params, isValidP params -> Always (compose agree ref_map) (initGS params).
Proof.
  unfold Always.
  intros.
  unfold compose.
  eapply (HAgreement (ref_mapp params)).
  eapply Refinement'.
  unfold isValid.
  auto.
Qed.

(* Pretty Proof *)

(* Agreement: For any process i and j, if they both decide, they decide the same value *)
Theorem Readable_Low_Level_Agreement : forall params gs i j b b0, isValid params gs -> 
  extract_decision i gs = Some b -> extract_decision j gs = Some b0
  -> b = b0.
Proof.
  intros.
  (* If a process i decides, it must have decided at some step, same for j *)
  destruct (Lem_VD_cD params gs i b  H H0) as [si].
  destruct (Lem_VD_cD params gs j b0 H H1) as [sj].
  (* The steps happened in some round, say ri and rj *)
  remember (round_no (step si)) as ri.
  remember (round_no (step sj)) as rj.
  (* If i decides, there's a quorum in the votes i received *)
  decompose record H2.
  pose proof (Lem_cD_Q si i b H5 H8).
  destruct H7 as [hi].
  destruct H7.
  destruct H9 as [qi].
  (* ...same for j *)
  decompose record H3.
  pose proof (Lem_cD_Q sj j b0 H11 H14).
  destruct H13 as [hj].
  destruct H13.
  destruct H15 as [qj].
  (* Case on different relationships of ri and rj *)
  remember (lt_eq_lt_dec ri rj) as cmp.
  decompose sum cmp.
  - (* ...in different rounds, ri < rj *)
    rename a0 into n.
    (* If i decides b, then all processes will have estimate b in the future rounds *)
    pose proof (Lem_cD_R si i b H5 H8).
    pose proof (Lem_cD_R sj j b0 H11 H14).
    rewrite Heqri in n.
    rewrite Heqrj in n.
    rewrite <- H16 in n.
    rewrite <- H17 in n.
    assert (si <<= sj).
    eapply (Lem_Rlt_S (initGS params) si sj).
    inversion H4.
    auto.
    inversion H10.
    auto.
    auto.
    pose proof (Lem_VcD_E params si i b H4 H5 H8 sj H18 n).
    (* So everyone holds b as the estimate in round rj, 
       and that will make any decision in that round b *)
    pose proof (Lem_VcDE_DEeq params sj j b0 b H10 H11 H14 H19).
    auto.
  - (* ...in the same round *)
    rename b1 into e.
    (* Processes i, j are using the same quorum system, say quorum sq *)
    pose proof (Lem_V_Qeq params (step si) (Lem_VS'_V params si H4)).
    rewrite <- H16 in H9.
    pose proof (Lem_V_Qeq params (step sj) (Lem_VS'_V params sj H10)).
    rewrite <- H17 in H15.
    pose proof (Lem_S_neq (step si) gs H6).
    rewrite H18 in H9.
    pose proof (Lem_S_neq (step sj) gs H12).
    rewrite H19 in H15.
    remember (coq_sq (coq_cq params)) as sq.
    (* So there's an intersection of the 2 quorums, say node k *)
    pose proof (Lem_V_Qeq params gs H).
    pose proof (Lem_V_Q params gs H).
    rewrite <- H20 in H21.
    destruct H21.
    destruct H22.
    destruct H9.
    destruct H15.
    specialize (H22 qi qj H9 H15).
    destruct H22 as [k].
    simpl in H22.
    (* i and j's decisions are the same as the message sent by k *)
    decompose record H22.
    rewrite <- Heqsq in H28.
    pose proof (Lem_tsok_M (n gs) b hi (sq qi) k H24 H26 H28).
    destruct H27 as [mki].
    rewrite <- Heqsq in H29.
    pose proof (Lem_tsok_M (n gs) b0 hj (sq qj) k H25 H26 H29).
    destruct H30 as [mkj].
    (* an honest k will send the same votes to different nodes *)
    destruct H27.
    pose proof (Lem_VS_Heq params (step si) gs i hi k mki (Lem_VS'_V params si H4) H6 H7 H27).
    rewrite <- Heqri in H32.
    destruct H30.
    pose proof (Lem_VS_Heq params (step sj) gs j hj k mkj (Lem_VS'_V params sj H10) H12 H13 H30).
    rewrite <- Heqrj in H34.
    rewrite <- e in H34.
    pose proof (Lem_VH_Heq params gs ri k i j mki mkj H H32 H34).
    (* so their decisions are equal *)
    congruence.
  - (* The symmetric case *)
    rename b1 into n.
    pose proof (Lem_cD_R si i b H5 H8).
    pose proof (Lem_cD_R sj j b0 H11 H14).
    rewrite Heqri in n.
    rewrite Heqrj in n.
    rewrite <- H16 in n.
    rewrite <- H17 in n.
    assert (sj <<= si).
    eapply (Lem_Rlt_S (initGS params) sj si).
    inversion H10.
    auto.
    inversion H4.
    auto.
    auto.
    pose proof (Lem_VcD_E params sj j b0 H10 H11 H14 si H18 n).
    pose proof (Lem_VcDE_DEeq params si i b b0 H4 H5 H8 H19).
    auto.
Qed.