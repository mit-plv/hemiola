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

Section RqDownReduction.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: RqRsSys dtr sys).

  Section OnRqDown.
    Variables (oidxTo: IdxT)
              (rqDowns: list (Id Msg)).
    Hypothesis (Hrqd: RqDownMsgs dtr oidxTo rqDowns).

    Lemma rqDown_oinds:
      forall inits ins hst outs eouts,
        SubList rqDowns eouts ->
        Atomic msg_dec inits ins hst outs eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          steps step_m sys st1 hst st2 ->
          DisjList (oindsOf hst) (subtreeIndsOf dtr oidxTo).
    Proof.
    Admitted.

    Lemma rqDown_olast_inside_tree:
      forall inits ins hst outs eouts,
        DisjList rqDowns inits ->
        Atomic msg_dec inits ins hst outs eouts ->
        forall st1 st2 loidx,
          Reachable (steps step_m) sys st1 ->
          Forall (InMPI st1.(bst_msgs)) rqDowns ->
          steps step_m sys st1 hst st2 ->
          lastOIdxOf hst = Some loidx ->
          In loidx (subtreeIndsOf dtr oidxTo) ->
          SubList (oindsOf hst) (subtreeIndsOf dtr oidxTo).
    Proof.
    Admitted.

    Lemma rqDown_olast_outside_tree:
      forall inits ins hst outs eouts,
        DisjList rqDowns inits ->
        Atomic msg_dec inits ins hst outs eouts ->
        forall st1 st2 loidx,
          Reachable (steps step_m) sys st1 ->
          Forall (InMPI st1.(bst_msgs)) rqDowns ->
          steps step_m sys st1 hst st2 ->
          lastOIdxOf hst = Some loidx ->
          ~ In loidx (subtreeIndsOf dtr oidxTo) ->
          exists phst rqUps ninits nins nhst nouts,
            hst = nhst ++ phst /\
            (phst = nil \/ RqUpHistory dtr phst rqUps) /\
            SubList (oindsOf phst) (subtreeIndsOf dtr oidxTo) /\
            SubList ninits ins /\
            Atomic msg_dec ninits nins nhst nouts eouts /\
            DisjList (oindsOf nhst) (subtreeIndsOf dtr oidxTo).
    Proof.
    Admitted.

    Definition RqDownP (st: MState oifc) :=
      Forall (InMPI st.(bst_msgs)) rqDowns.

    Lemma rqDown_lpush_rpush_unit_reducible:
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
    
    Lemma rqDown_lpush_unit_reducible:
      forall pinits pins phst pouts peouts
             inits ins hst outs eouts loidx,
        PInitializing sys RqDownP phst ->
        Atomic msg_dec pinits pins phst pouts peouts ->
        SubList rqDowns peouts ->
        Atomic msg_dec inits ins hst outs eouts ->
        lastOIdxOf hst = Some loidx ->
        In loidx (subtreeIndsOf dtr oidxTo) ->
        DisjList peouts inits ->
        Reducible sys (hst ++ phst) (phst ++ hst).
    Proof.
      intros; red; intros.
      eapply steps_split in H6; [|reflexivity].
      destruct H6 as [sti [? ?]].
      eapply rqDown_lpush_rpush_unit_reducible; try eassumption.
      - eapply rqDown_oinds; try eassumption.
      - eapply rqDown_olast_inside_tree.
        + eapply DisjList_SubList; [|eassumption].
          eassumption.
        + eassumption.
        + eapply reachable_steps; [eassumption|].
          eassumption.
        + eapply H; eassumption.
        + eassumption.
        + eassumption.
        + eassumption.
      - eapply steps_append; eauto.
    Qed.

    Lemma rqDown_rpush_unit_reducible:
      forall inits ins hst outs eouts loidx ridx routs,
        Atomic msg_dec inits ins hst outs eouts ->
        lastOIdxOf hst = Some loidx ->
        ~ In loidx (subtreeIndsOf dtr oidxTo) ->
        DisjList rqDowns inits ->
        ReducibleP sys RqDownP (RlblInt oidxTo ridx rqDowns routs :: hst)
                   (hst ++ [RlblInt oidxTo ridx rqDowns routs]).
    Proof.
      intros; red; intros.
      inv_steps.
      pose proof (rqDown_olast_outside_tree H2 H Hr Hp H7 H0 H1).
      destruct H3 as [rhst [rqUps ?]].
      destruct H3 as [ninits [nins [nhst [nouts ?]]]]; dest; subst.
      eapply steps_split in H7; [|reflexivity].
      destruct H7 as [sti [? ?]].

      rewrite <-app_assoc.
      eapply reducible_app_1; try assumption.
      - instantiate (1:= RlblInt oidxTo ridx rqDowns routs :: rhst).
        red; intros.
        destruct H4; dest; subst; simpl in *.
        + inv_steps.
          apply steps_singleton; assumption.
        + eapply rqUpHistory_lpush_lbl; try eassumption.
          (* [RqUp]s and [RqDown]s are certainly disjoint. *)
          admit.
      - change (nhst ++ RlblInt oidxTo ridx rqDowns routs :: rhst)
          with (nhst ++ [RlblInt oidxTo ridx rqDowns routs] ++ rhst).
        rewrite app_assoc.
        eapply reducible_app_2; try assumption.
        + instantiate (1:= RlblInt oidxTo ridx rqDowns routs :: nhst).
          change (RlblInt oidxTo ridx rqDowns routs :: nhst)
            with ([RlblInt oidxTo ridx rqDowns routs] ++ nhst).
          eapply rqDown_lpush_rpush_unit_reducible; try eassumption.
          * constructor.
          * simpl.
            (* [In oidxTo (subtreeIndsOf dtr oidxTo)] when [oidxTo] is valid. *)
            admit.
          * (* For an [Atomic] history, 
             * if [DisjList rqDowns inits] then [DisjList eouts rqDowns] *)
            admit.
        + simpl; econstructor; [|eassumption].
          eapply steps_append; eassumption.
    Admitted.      

    Lemma rqDown_LRPushable_unit_reducible:
      forall rinits rins rhst routs reouts rloidx
             linits lins lhst louts leouts lloidx,
        Atomic msg_dec rinits rins rhst routs reouts ->
        DisjList rqDowns rinits ->
        lastOIdxOf rhst = Some rloidx ->
        ~ In rloidx (subtreeIndsOf dtr oidxTo) ->
        Atomic msg_dec linits lins lhst louts leouts ->
        DisjList rqDowns linits ->
        lastOIdxOf lhst = Some lloidx ->
        In lloidx (subtreeIndsOf dtr oidxTo) ->
        ReducibleP sys RqDownP (lhst ++ rhst) (rhst ++ lhst).
    Proof.
      intros; red; intros.
      eapply steps_split in H7; [|reflexivity].
      destruct H7 as [sti [? ?]].
      (* pose proof (rqDown_olast_outside_tree H2 H Hr Hp H7 H0 H1). *)
    Admitted.
    
  End OnRqDown.

End RqDownReduction.

