Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Mesi.ImplOStateIfc.

Section Footprints.
  Variable topo: DTree.

  Definition DownLockFromChild (oidx: IdxT) (rqid: RqInfo Msg) :=
    exists cidx,
      rqid.(rqi_midx_rsb) = Some (downTo cidx) /\
      parentIdxOf topo cidx = Some oidx.

  Definition DownLockFromParent (oidx: IdxT) (rqid: RqInfo Msg) :=
    rqid.(rqi_midx_rsb) = Some (rqUpFrom oidx).

  Definition MesiFootprintsInv (st: MState): Prop :=
    forall oidx,
      orq <+- (bst_orqs st)@[oidx];
        rqid <+- orq@[downRq];
        rmsg <+- rqid.(rqi_msg);
        match case rmsg.(msg_id) on idx_dec default True with
        | mesiRqS: DownLockFromChild oidx rqid
        | mesiRqM: DownLockFromChild oidx rqid
        | mesiDownRqS: DownLockFromParent oidx rqid
        | mesiDownRqI: DownLockFromParent oidx rqid
        end.

End Footprints.

