Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM StepT SemFacts.
Require Import Topology Serial SerialFacts Reduction.

Set Implicit Arguments.

Open Scope list.

(*! Reducibility (commutativity) of internal state transitions *)

(** TODO: need to check whether the disjointness between [ins1] and [ins2] 
 * (or [outs1] and [outs2]) is required. *)
Definition NonConflictingR {ifc: OStateIfc} (rule1 rule2: Rule ifc) :=
  forall post1 porq1 ins1 nost1 norq1 outs1 ins2,
    rule_precond rule1 post1 porq1 ins1 ->
    rule_trs rule1 post1 porq1 ins1 = (nost1, norq1, outs1) ->
    rule_precond rule2 nost1 norq1 ins2 ->
    (* 1) Preconditions of [rule2] hold if the ones of [rule1] hold. *)
    rule_precond rule2 post1 porq1 ins2 /\
    idsOf ins2 = rule_msgs_from rule2 porq1 /\
    let (no2, outs2) := rule_trs rule2 nost1 norq1 ins2 in
    let (nost2, norq2) := no2 in
    let (rno2, routs2) := rule_trs rule2 post1 porq1 ins2 in
    let (rnost2, rnorq2) := rno2 in
    let (rno1, routs1) := rule_trs rule1 rnost2 rnorq2 ins1 in
    let (rnost1, rnorq1) := rno1 in
    (* ?? *)
    routs2 = outs2 /\
    (* 2) Precondition of [rule1] holds after a transition by [rule2]. *)
    rule_precond rule1 rnost2 rnorq2 ins1 /\
    idsOf ins1 = rule_msgs_from rule1 rnorq2 /\
    (* 3) Transitions by [rule1; rule2] and [rule2; rule1] are same. *)
    no2 = rno1 /\ outs1 = routs1.

Definition NonConflictingL (sys: System)
           (oidx1 ridx1 oidx2 ridx2: IdxT) :=
  oidx1 <> oidx2 \/
  (oidx1 = oidx2 /\
   forall obj rule1 rule2,
     In obj (sys_objs sys) -> obj_idx obj = oidx1 ->
     In rule1 (obj_rules obj) -> rule_idx rule1 = ridx1 ->
     In rule2 (obj_rules obj) -> rule_idx rule2 = ridx2 ->
     NonConflictingR rule1 rule2).

Definition NonConflicting (sys: System) (hst1 hst2: MHistory) :=
  forall oidx1 ridx1 ins1 outs1 oidx2 ridx2 ins2 outs2,
    In (RlblInt oidx1 ridx1 ins1 outs1) hst1 ->
    In (RlblInt oidx2 ridx2 ins2 outs2) hst2 ->
    NonConflictingL sys oidx1 ridx1 oidx2 ridx2.

Definition Discontinuous (sys: System) (hst1 hst2: MHistory) :=
  exists inits1 ins1 outs1 eouts1 inits2 ins2 outs2 eouts2,
    Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 /\
    Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 /\
    DisjList (idsOf ins1) (idsOf ins2) /\
    DisjList outs1 ins2 /\
    DisjList (idsOf outs1) (idsOf outs2).

Lemma nonconflicting_head_1:
  forall sys lbl1 hst1 hst2,
    NonConflicting sys (lbl1 :: hst1) hst2 ->
    NonConflicting sys [lbl1] hst2.
Proof.
  unfold NonConflicting; intros.
  Common.dest_in.
  eapply H; eauto.
  left; eauto.
Qed.

Lemma nonconflicting_head_2:
  forall sys hst1 lbl2 hst2,
    NonConflicting sys hst1 (lbl2 :: hst2) ->
    NonConflicting sys hst1 [lbl2].
Proof.
  unfold NonConflicting; intros.
  Common.dest_in.
  eapply H; eauto.
  left; eauto.
Qed.

Lemma nonconflicting_tail_1:
  forall sys lbl1 hst1 hst2,
    NonConflicting sys (lbl1 :: hst1) hst2 ->
    NonConflicting sys hst1 hst2.
Proof.
  unfold NonConflicting; intros.
  eapply H; eauto.
  right; eauto.
Qed.

Lemma nonconflicting_tail_2:
  forall sys hst1 lbl2 hst2,
    NonConflicting sys hst1 (lbl2 :: hst2) ->
    NonConflicting sys hst1 hst2.
Proof.
  unfold NonConflicting; intros.
  eapply H; eauto.
  right; eauto.
Qed.

Lemma internal_commutes:
  forall sys oidx1 ridx1 ins1 outs1 oidx2 ridx2 ins2 outs2,
    NonConflictingL sys oidx1 ridx1 oidx2 ridx2 ->
    DisjList (idsOf ins1) (idsOf ins2) ->
    DisjList outs1 ins2 ->
    DisjList (idsOf outs1) (idsOf outs2) ->
    Reducible sys [RlblInt oidx2 ridx2 ins2 outs2; RlblInt oidx1 ridx1 ins1 outs1]
              [RlblInt oidx1 ridx1 ins1 outs1; RlblInt oidx2 ridx2 ins2 outs2].
Proof.
  unfold Reducible; intros.
  dest_steps; dest_step_m.

  destruct H; dest.
  - econstructor.
    + econstructor.
      * econstructor.
      * econstructor; try reflexivity; try eassumption.
        { mred. }
        { mred. }
        { eapply FirstMPI_Forall_deqMsgs.
          { apply DisjList_comm; eassumption. }
          { eapply FirstMPI_Forall_enqMsgs_inv.
            { apply DisjList_comm; eassumption. }
            { assumption. }
          }
        }
    + econstructor; try reflexivity; try eassumption.
      * mred.
      * mred.
      * apply FirstMPI_Forall_enqMsgs.
        apply FirstMPI_Forall_deqMsgs; auto.
      * f_equal.
        { meq. }
        { meq. }
        { rewrite <-enqMsgs_deqMsgs_FirstMPI_comm.
          { rewrite deqMsgs_deqMsgs_comm by (apply DisjList_comm; assumption).
            rewrite enqMsgs_enqMsgs_comm with (msgs1:= outs2)
              by (apply DisjList_comm; assumption).
            rewrite enqMsgs_deqMsgs_FirstMPI_comm with (msgs2:= outs2).
            { reflexivity. }
            { destruct H15; auto. }
            { apply FirstMPI_Forall_deqMsgs; auto. }
          }
          { destruct H26; auto. }
          { eapply FirstMPI_Forall_enqMsgs_inv.
            { apply DisjList_comm; eassumption. }
            { assumption. }
          }
        }

  - assert (obj = obj0) by (eapply obj_same_id_in_system_same; eauto).
    subst; mred; simpl in *.
    specialize (H3 _ _ _ H7 eq_refl H8 eq_refl H11 eq_refl).

    red in H3.
    pose proof (UIP_refl _ _ Hifc0); subst.
    specialize (H3 _ _ _ _ _ _ _ H18 H19 H29); dest.

    remember (rule_trs rule0 pos porq0 ins2) as trs2.
    destruct trs2 as [[tnost2 tnorq2] touts2]; inv H30.
    remember (rule_trs rule0
                       match Hifc in (_ = o) return (OState o) with
                       | eq_refl => ost_st os
                       end porq ins2) as rtrs2.
    destruct rtrs2 as [[rnost2 rnorq2] routs2]; dest; subst.
    remember (rule_trs rule rnost2 rnorq2 ins1) as rtrs1.
    destruct rtrs1 as [[rnost1 rnorq1] routs1]; dest; subst.
    
    econstructor.
    + econstructor.
      * econstructor.
      * econstructor; try reflexivity; try eassumption.
        { eapply FirstMPI_Forall_deqMsgs.
          { apply DisjList_comm; eassumption. }
          { eapply FirstMPI_Forall_enqMsgs_inv.
            { apply DisjList_comm; eassumption. }
            { eassumption. }
          }
        }
        { apply eq_sym; eassumption. }
    + econstructor.
      * assumption.
      * assumption.
      * reflexivity.
      * instantiate (2:= (oss+[obj_idx obj0 <- {| ost_st := rnost2 |}])%fmap).
        mred.
      * instantiate (2:= (orqs+[obj_idx obj0 <- rnorq2])%fmap).
        mred.
      * instantiate (1:= enqMsgs outs2 (deqMsgs (idsOf ins2) msgs)).
        apply FirstMPI_Forall_enqMsgs.
        apply FirstMPI_Forall_deqMsgs; auto.
      * assumption.
      * assumption.
      * assumption.
      * instantiate (1:= eq_refl); simpl.
        assumption.
      * simpl; apply eq_sym; eassumption.
      * assumption.
      * assumption.
      * reflexivity.
      * inv H20; f_equal.
        { meq. }
        { meq. }
        { rewrite <-enqMsgs_deqMsgs_FirstMPI_comm.
          { rewrite deqMsgs_deqMsgs_comm by (apply DisjList_comm; assumption).
            rewrite enqMsgs_enqMsgs_comm with (msgs1:= outs2)
              by (apply DisjList_comm; assumption).
            rewrite enqMsgs_deqMsgs_FirstMPI_comm with (msgs2:= outs2).
            { reflexivity. }
            { destruct H15; auto. }
            { apply FirstMPI_Forall_deqMsgs; auto. }
          }
          { destruct H26; auto. }
          { eapply FirstMPI_Forall_enqMsgs_inv.
            { apply DisjList_comm; eassumption. }
            { assumption. }
          }
        }
Qed.

Lemma nonconflicting_discontinuous_commutable_atomic_0:
  forall sys oidx1 ridx1 mins1 mouts1 inits2 ins2 hst2 outs2 eouts2,
    Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
    NonConflicting sys [RlblInt oidx1 ridx1 mins1 mouts1] hst2 ->
    DisjList (idsOf mins1) (idsOf ins2) ->
    DisjList mouts1 ins2 ->
    DisjList (idsOf mouts1) (idsOf outs2) ->
    Reducible sys (hst2 ++ [RlblInt oidx1 ridx1 mins1 mouts1])
              (RlblInt oidx1 ridx1 mins1 mouts1 :: hst2).
Proof.
  induction 1; simpl; intros; subst.

  - apply internal_commutes; auto.
    eapply H; try (left; reflexivity; fail).
  - eapply reducible_trans.
    + change (RlblInt oidx ridx rins routs :: hst ++ [RlblInt oidx1 ridx1 mins1 mouts1])
        with ([RlblInt oidx ridx rins routs] ++ hst ++ [RlblInt oidx1 ridx1 mins1 mouts1]).
      eapply reducible_app_1.
      eapply IHAtomic.
      * eapply nonconflicting_tail_2; eassumption.
      * rewrite idsOf_app in H6.
        apply DisjList_comm.
        apply DisjList_comm, DisjList_app_3 in H6; dest; auto.
      * apply DisjList_comm.
        apply DisjList_comm, DisjList_app_3 in H7; dest; auto.
      * rewrite idsOf_app in H8.
        apply DisjList_comm.
        apply DisjList_comm, DisjList_app_3 in H8; dest; auto.
    + simpl.
      change (RlblInt oidx ridx rins routs :: RlblInt oidx1 ridx1 mins1 mouts1 :: hst)
        with ([RlblInt oidx ridx rins routs; RlblInt oidx1 ridx1 mins1 mouts1] ++ hst).
      change (RlblInt oidx1 ridx1 mins1 mouts1 :: RlblInt oidx ridx rins routs :: hst)
        with ([RlblInt oidx1 ridx1 mins1 mouts1; RlblInt oidx ridx rins routs] ++ hst).
      apply reducible_app_2.
      apply internal_commutes.
      * apply nonconflicting_head_2 in H5.
        eapply H5; try (left; reflexivity; fail).
      * rewrite idsOf_app in H6.
        apply DisjList_comm.
        apply DisjList_comm, DisjList_app_3 in H6; dest; auto.
      * apply DisjList_comm.
        apply DisjList_comm, DisjList_app_3 in H7; dest; auto.
      * rewrite idsOf_app in H8.
        apply DisjList_comm.
        apply DisjList_comm, DisjList_app_3 in H8; dest; auto.
Qed.

Lemma nonconflicting_discontinuous_commutable_atomic:
  forall sys hst1 hst2,
    NonConflicting sys hst1 hst2 ->
    Discontinuous sys hst1 hst2 ->
    Reducible sys (hst2 ++ hst1) (hst1 ++ hst2).
Proof.
  unfold Discontinuous; intros.
  destruct H0 as [inits1 [ins1 [outs1 [eouts1 [inits2 [ins2 [outs2 [eouts2 ?]]]]]]]].
  dest.

  induction H0; simpl; intros; subst;
    [eapply nonconflicting_discontinuous_commutable_atomic_0; eauto|].

  replace (hst2 ++ RlblInt oidx ridx rins routs :: hst)
    with ((hst2 ++ [RlblInt oidx ridx rins routs]) ++ hst)
    by (rewrite <-app_assoc; reflexivity).
 
  eapply reducible_trans.
  - apply reducible_app_2.
    eapply nonconflicting_discontinuous_commutable_atomic_0;
      try (eapply H1; eauto).
    + eapply nonconflicting_head_1; eauto.
    + rewrite idsOf_app in H2.
      apply DisjList_app_3 in H2; dest; auto.
    + apply DisjList_app_3 in H3; dest; auto.
    + rewrite idsOf_app in H4.
      apply DisjList_app_3 in H4; dest; auto.
  - simpl; apply reducible_cons.
    apply IHAtomic; auto.
    + eapply nonconflicting_tail_1; eauto.
    + rewrite idsOf_app in H2.
      apply DisjList_app_3 in H2; dest; auto.
    + apply DisjList_app_3 in H3; dest; auto.
    + rewrite idsOf_app in H4.
      apply DisjList_app_3 in H4; dest; auto.
Qed.

Close Scope list.
