Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant.
Require Import Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.
Require Import RqRsInvMsg RqRsInvLock RqRsInvAtomic.
Require Import RqUpRed RsUpRed RqRsRed.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

(** Proof sketch for the reducibility of downward-response labels:
 * 1) [exists preh posth, 
 *       phst = posth ++ preh /\
 *       ("preh" just consists of RqUp labels) /\
 *       oinds(posth) ⊆ tr(nlbl)^{-1}]
 * 2) Let [olast(hst)] be the last object index of an [Atomic] history [hst].
 * 2-1) [olast(hst) ∈ tr(nlbl) -> oinds(hst) ⊆ tr(nlbl)]
 * 2-2) [olast(hst) ∈ tr(nlbl)^{-1} -> oinds(hst) ⊆ tr(nlbl)^{-1}]
 *      This part differs from the one for downward-requests since both upward
 *      requests and upward responses cannot happen when a downward-response label is
 *      in the message pool.
 * 3) Define [LPush] and [RPush] as follows:
 *    [LPush hst ≜ olast(hst) ∈ tr(nlbl)]
 *    [RPush hst ≜ olast(hst) ∈ tr(nlbl)^{-1}]
 * 4) Conditions of [PushableHst] are easier to prove, mostly by a).
 *)

Section RsDownReduction.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: RqRsSys dtr sys).

  Section OnRsDown.
    Variables (oidxTo: IdxT)
              (rsDowns: list (Id Msg)).
    Hypothesis (Hrsd: RsDownMsgs dtr oidxTo rsDowns).

    Lemma rsDown_oinds:
      forall inits ins hst outs eouts,
        SubList rsDowns eouts ->
        Atomic msg_dec inits ins hst outs eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          steps step_m sys st1 hst st2 ->
          exists phst ruIdx rqUps ninits nins nhst nouts,
            hst = nhst ++ phst /\
            (phst = nil \/
             (RqUpMsgs dtr ruIdx rqUps /\ RqUpHistory dtr phst rqUps)) /\
            SubList (oindsOf phst) (subtreeIndsOf dtr oidxTo) /\
            SubList ninits ins /\
            Atomic msg_dec ninits nins nhst nouts eouts /\
            DisjList (oindsOf nhst) (subtreeIndsOf dtr oidxTo).
    Proof.
    Admitted.

    Lemma rsDown_olast_inside_tree:
      forall inits ins hst outs eouts,
        DisjList rsDowns inits ->
        Atomic msg_dec inits ins hst outs eouts ->
        forall st1 st2 loidx,
          Reachable (steps step_m) sys st1 ->
          Forall (InMPI st1.(bst_msgs)) rsDowns ->
          steps step_m sys st1 hst st2 ->
          lastOIdxOf hst = Some loidx ->
          In loidx (subtreeIndsOf dtr oidxTo) ->
          SubList (oindsOf hst) (subtreeIndsOf dtr oidxTo).
    Proof.
    Admitted.

    Lemma rsDown_olast_outside_tree:
      forall inits ins hst outs eouts,
        DisjList rsDowns inits ->
        Atomic msg_dec inits ins hst outs eouts ->
        forall st1 st2 loidx,
          Reachable (steps step_m) sys st1 ->
          Forall (InMPI st1.(bst_msgs)) rsDowns ->
          steps step_m sys st1 hst st2 ->
          lastOIdxOf hst = Some loidx ->
          ~ In loidx (subtreeIndsOf dtr oidxTo) ->
          DisjList (oindsOf hst) (subtreeIndsOf dtr oidxTo).
    Proof.
    Admitted.

    Definition RsDownP (st: MState oifc) :=
      Forall (InMPI st.(bst_msgs)) rsDowns.

    Lemma rsDown_lpush_rpush_unit_reducible:
      forall rinits rins rhst routs reouts
             linits lins lhst louts leouts,
        Atomic msg_dec rinits rins rhst routs reouts ->
        DisjList (oindsOf rhst) (subtreeIndsOf dtr oidxTo) ->
        Atomic msg_dec linits lins lhst louts leouts ->
        SubList (oindsOf lhst) (subtreeIndsOf dtr oidxTo) ->
        DisjList reouts linits ->
        Reducible sys (lhst ++ rhst) (rhst ++ lhst).
    Proof.
      intros.
      eapply rqrs_reducible; try eassumption.
      eapply DisjList_comm, DisjList_SubList; [eassumption|].
      apply DisjList_comm; assumption.
    Qed.
    
    Lemma rsDown_lpush_unit_reducible:
      forall pinits pins phst pouts peouts
             inits ins hst outs eouts loidx,
        PInitializing sys RsDownP phst ->
        Atomic msg_dec pinits pins phst pouts peouts ->
        SubList rsDowns peouts ->
        Atomic msg_dec inits ins hst outs eouts ->
        lastOIdxOf hst = Some loidx ->
        In loidx (subtreeIndsOf dtr oidxTo) ->
        DisjList peouts inits ->
        Reducible sys (hst ++ phst) (phst ++ hst).
    Proof.
      intros; red; intros.
      eapply steps_split in H6; [|reflexivity].
      destruct H6 as [sti [? ?]].

      pose proof (rsDown_oinds H1 H0 Hr H6).
      destruct H8 as [pphst [ruIdx [rqUps [ninits [nins [nphst [nouts ?]]]]]]].
      dest; subst.
      eapply steps_split in H6; [|reflexivity].
      destruct H6 as [psti [? ?]].

      rewrite <-app_assoc.
      eapply reducible_app_1; try assumption.
      - instantiate (1:= hst ++ pphst).
        destruct H9; dest; subst; simpl in *.
        + rewrite app_nil_r; apply reducible_refl.
        + eapply rqUpHistory_lpush_unit_reducible; eauto.
          admit.
      - rewrite app_assoc.
        eapply reducible_app_2; try assumption.
        + instantiate (1:= hst ++ nphst).
          eapply rsDown_lpush_rpush_unit_reducible; try eassumption.
          eapply rsDown_olast_inside_tree.
          * eapply DisjList_SubList; eassumption.
          * eassumption.
          * eapply reachable_steps; [eassumption|].
            eapply steps_append; eassumption.
          * eapply H.
            eapply steps_append; eassumption.
          * eassumption.
          * eassumption.
          * eassumption.
        + rewrite <-app_assoc.
          eapply steps_append; [|eassumption].
          eapply steps_append; eassumption.
    Admitted.

    Lemma rsDown_rpush_unit_reducible:
      forall inits ins hst outs eouts loidx ridx routs,
        Atomic msg_dec inits ins hst outs eouts ->
        lastOIdxOf hst = Some loidx ->
        ~ In loidx (subtreeIndsOf dtr oidxTo) ->
        DisjList rsDowns inits ->
        ReducibleP sys RsDownP (RlblInt oidxTo ridx rsDowns routs :: hst)
                   (hst ++ [RlblInt oidxTo ridx rsDowns routs]).
    Proof.
      intros; red; intros.
      inv_steps.
      eapply rsDown_lpush_rpush_unit_reducible; try eassumption.
      - eapply rsDown_olast_outside_tree; eassumption.
      - constructor.
      - simpl; red; intros; Common.dest_in.
        apply parentChnsOf_subtreeIndsOf_self_in.
        + apply Hrrs.
        + destruct Hrsd as [rsDown ?]; dest.
          unfold edgeDownTo, downEdgesTo in H5.
          destruct (parentChnsOf dtr e); simpl in H5; discriminate.
      - (* For an [Atomic] history,
         * if [DisjList rqDowns inits] then [DisjList eouts rqDowns] *)
        admit.
      - simpl; econstructor; eassumption.
    Admitted.

    Lemma rsDown_LRPushable_unit_reducible:
      forall rinits rins rhst routs reouts rloidx
             linits lins lhst louts leouts lloidx,
        Atomic msg_dec rinits rins rhst routs reouts ->
        DisjList rsDowns rinits ->
        lastOIdxOf rhst = Some rloidx ->
        ~ In rloidx (subtreeIndsOf dtr oidxTo) ->
        Atomic msg_dec linits lins lhst louts leouts ->
        DisjList rsDowns linits ->
        lastOIdxOf lhst = Some lloidx ->
        In lloidx (subtreeIndsOf dtr oidxTo) ->
        ReducibleP sys RsDownP (lhst ++ rhst) (rhst ++ lhst).
    Proof.
      intros; red; intros.
      eapply steps_split in H7; [|reflexivity].
      destruct H7 as [sti [? ?]].

      eapply rsDown_olast_inside_tree in H6;
        [|exact H4
         |eassumption
         |eapply reachable_steps; eassumption
         |eapply (atomic_messages_ins_ins msg_dec);
          try eapply H; try eassumption;
          apply DisjList_comm; assumption
         |eassumption
         |eassumption].
      clear H5.

      eapply rsDown_olast_outside_tree in H2;
        try exact H0; try eassumption.
      clear H1.

      eapply rsDown_lpush_rpush_unit_reducible; try eassumption.
      - admit.
      - eapply steps_append; eassumption.
    Admitted.
    
  End OnRsDown.

End RsDownReduction.

