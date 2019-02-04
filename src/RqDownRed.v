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
        DisjList inits rqDowns ->
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
        DisjList inits rqDowns ->
        Atomic msg_dec inits ins hst outs eouts ->
        forall st1 st2 loidx,
          Reachable (steps step_m) sys st1 ->
          Forall (InMPI st1.(bst_msgs)) rqDowns ->
          steps step_m sys st1 hst st2 ->
          lastOIdxOf hst = Some loidx ->
          ~ In loidx (subtreeIndsOf dtr oidxTo) ->
          exists rqUps phst nhst,
            hst = nhst ++ phst /\
            RqUpHistory dtr phst rqUps /\
            SubList (oindsOf phst) (subtreeIndsOf dtr oidxTo) /\
            DisjList (oindsOf nhst) (subtreeIndsOf dtr oidxTo).
    Proof.
    Admitted.

  End OnRqDown.

End RqDownReduction.

