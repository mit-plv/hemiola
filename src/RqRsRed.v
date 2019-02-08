Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant.
Require Import Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.
Require Import RqRsInvMsg RqRsInvLock RqRsInvAtomic.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Definition lastOIdxOf (hst: MHistory): option IdxT :=
  match hst with
  | RlblInt oidx _ _ _ :: _ => Some oidx
  | _ => None
  end.

Definition oidxOf (lbl: MLabel) :=
  match lbl with
  | RlblInt oidx _ _ _ => Some oidx
  | _ => None
  end.

Fixpoint oindsOf (hst: MHistory) :=
  match hst with
  | nil => nil
  | lbl :: hst' => (oidxOf lbl) ::> (oindsOf hst')
  end.

Lemma atomic_lastOIdxOf:
  forall inits ins hst outs eouts,
    Atomic msg_dec inits ins hst outs eouts ->
    exists loidx,
      lastOIdxOf hst = Some loidx.
Proof.
  induction 1; simpl; intros; eauto.
Qed.

Section InsideTree.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrd: RqRsDTree dtr sys).

  Lemma atomic_inside_tree_ins_disj_outs:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall st1 st2,
        steps step_m sys st1 hst st2 ->
        forall toidx,
          SubList (oindsOf hst) (subtreeIndsOf dtr toidx) ->
          forall ups,
            Forall (fun up =>
                      rqEdgeUpFrom dtr toidx = Some (idOf up) \/
                      rsEdgeUpFrom dtr toidx = Some (idOf up)) ups ->
            DisjList ups ins.
  Proof.
    pose proof Hrrd.
  Admitted.

  Corollary atomic_inside_tree_inits_disj_rqUps:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall st1 st2,
        steps step_m sys st1 hst st2 ->
        forall toidx,
          SubList (oindsOf hst) (subtreeIndsOf dtr toidx) ->
          forall rqUps,
            Forall (fun up => rqEdgeUpFrom dtr toidx = Some (idOf up)) rqUps ->
            DisjList rqUps inits.
  Proof.
    intros.
    eapply DisjList_comm, DisjList_SubList;
      [eapply atomic_inits_in; eassumption|].
    apply DisjList_comm.
    eapply atomic_inside_tree_ins_disj_outs; try eassumption.
    eapply Forall_impl; [|eassumption].
    simpl; intros; auto.
  Qed.

End InsideTree.

Section RqRsRed.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: RqRsSys dtr sys).

  Lemma rqrs_lbl_ins_disj:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall oidx1 ridx1 rins1 routs1 oidx2 ridx2 rins2 routs2 st2,
        oidx1 <> oidx2 ->
        steps step_m sys st1
              [RlblInt oidx2 ridx2 rins2 routs2;
                 RlblInt oidx1 ridx1 rins1 routs1] st2 ->
        DisjList (idsOf rins1) (idsOf rins2).
  Proof.
  Admitted.

  Lemma rqrs_lbl_outs_disj:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall oidx1 ridx1 rins1 routs1 oidx2 ridx2 rins2 routs2 st2,
        oidx1 <> oidx2 ->
        steps step_m sys st1
              [RlblInt oidx2 ridx2 rins2 routs2;
                 RlblInt oidx1 ridx1 rins1 routs1] st2 ->
        DisjList (idsOf routs1) (idsOf routs2).
  Proof.
  Admitted.

  Lemma rqrs_atomic_ins_disj:
    forall inits1 ins1 hst1 outs1 eouts1 inits2 ins2 hst2 outs2 eouts2,
      Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
      Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
      DisjList (oindsOf hst1) (oindsOf hst2) ->
      DisjList eouts1 inits2 ->
      DisjList eouts1 ins2.
  Proof.
  Admitted.

  Lemma rqrs_atomic_outs_disj:
    forall inits1 ins1 hst1 outs1 eouts1 inits2 ins2 hst2 outs2 eouts2,
      Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
      Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
      DisjList (oindsOf hst1) (oindsOf hst2) ->
      DisjList eouts1 inits2 ->
      DisjList outs1 inits2.
  Proof.
  Admitted.

  Lemma rqrs_lbl_reducible':
    forall inits1 ins1 hst1 outs1 eouts1 lbl2 oidx2 ridx2 rins2 routs2,
      Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
      lbl2 = RlblInt oidx2 ridx2 rins2 routs2 ->
      ~ In oidx2 (oindsOf hst1) ->
      DisjList outs1 rins2 ->
      Reducible sys (lbl2 :: hst1) (hst1 ++ [lbl2]).
  Proof.
    unfold Reducible; induction 1; simpl; intros; subst.
    - apply internal_commutes; auto.
      + red; intuition.
      + eapply rqrs_lbl_ins_disj; try eassumption; intuition.
      + eapply rqrs_lbl_outs_disj; try eassumption; intuition.
    - eapply reducible_trans; try eassumption.
      + apply reducible_cons_2.
        * change (RlblInt oidx2 ridx2 rins2 routs2 :: RlblInt oidx ridx rins routs :: hst)
            with ([RlblInt oidx2 ridx2 rins2 routs2; RlblInt oidx ridx rins routs] ++ hst)
            in H8.
          eapply steps_split in H8; [|reflexivity].
          destruct H8 as [sti [? ?]].
          apply internal_commutes; auto.
          { red; intuition. }
          { eapply rqrs_lbl_ins_disj;
              [eapply reachable_steps; eassumption| |eassumption].
            intuition.
          }
          { eapply DisjList_app_3 in H7; dest; assumption. }
          { eapply rqrs_lbl_outs_disj;
              [eapply reachable_steps; eassumption| |eassumption].
            intuition.
          }
      + apply reducible_cons.
        red; intros.
        eapply IHAtomic; eauto.
        eapply DisjList_app_3 in H7; dest; assumption.
  Qed.
  
  Lemma rqrs_lbl_reducible:
    forall inits1 ins1 hst1 outs1 eouts1 lbl2 oidx2 ridx2 rins2 routs2,
      Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
      lbl2 = RlblInt oidx2 ridx2 rins2 routs2 ->
      ~ In oidx2 (oindsOf hst1) ->
      DisjList eouts1 rins2 ->
      Reducible sys (lbl2 :: hst1) (hst1 ++ [lbl2]).
  Proof.
    intros.
    eapply rqrs_atomic_outs_disj with (outs1:= outs1) (hst2:= [lbl2]) in H2.
    { eapply rqrs_lbl_reducible'; try eassumption. }
    { eassumption. }
    { subst; econstructor. }
    { subst; simpl.
      apply (DisjList_singleton_2 eq_nat_dec); eassumption.
    }
  Qed.

  Lemma rqrs_reducible':
    forall inits1 ins1 hst1 outs1 eouts1 inits2 ins2 hst2 outs2 eouts2,
      Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
      Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
      DisjList (oindsOf hst1) (oindsOf hst2) ->
      DisjList eouts1 ins2 ->
      Reducible sys (hst2 ++ hst1) (hst1 ++ hst2).
  Proof.
    induction 2; simpl; intros; subst.
    - eapply rqrs_lbl_reducible; eauto.
      specialize (H0 oidx); destruct H0; intuition.
    - apply DisjList_comm, DisjList_cons in H6; dest.
      apply DisjList_comm in H4.
      apply DisjList_comm, DisjList_app_3 in H7; dest.
      apply DisjList_comm in H5; apply DisjList_comm in H6.
      eapply reducible_trans.
      + apply reducible_cons.
        apply IHAtomic; auto.
      + change (RlblInt oidx ridx rins routs :: hst1 ++ hst)
          with ((RlblInt oidx ridx rins routs :: hst1) ++ hst).
        replace (hst1 ++ RlblInt oidx ridx rins routs :: hst)
          with ((hst1 ++ [RlblInt oidx ridx rins routs]) ++ hst)
          by (rewrite <-app_assoc; reflexivity).
        apply reducible_app_2.
        eapply rqrs_lbl_reducible; eauto.
  Qed.

  Theorem rqrs_reducible:
    forall inits1 ins1 hst1 outs1 eouts1 inits2 ins2 hst2 outs2 eouts2,
      Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
      Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
      DisjList (oindsOf hst1) (oindsOf hst2) ->
      DisjList eouts1 inits2 ->
      Reducible sys (hst2 ++ hst1) (hst1 ++ hst2).
  Proof.
    intros.
    eapply rqrs_atomic_ins_disj in H2; eauto; dest.
    eapply rqrs_reducible'; eauto.
  Qed.

End RqRsRed.

Close Scope list.
Close Scope fmap.

