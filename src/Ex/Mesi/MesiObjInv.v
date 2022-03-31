Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

#[global] Existing Instance Mesi.ImplOStateIfc.

Section ObjInv.
  Variable topo: DTree.

  Definition MesiUpLockObjInv (oidx: IdxT): ObjInv :=
    fun ost orq =>
      (rqiu <+- orq@[upRq];
      rmsg <+- rqiu.(rqi_msg);
      match case rmsg.(msg_id) on idx_dec default True with
      | mesiRqS:
          ost#[owned] = false /\ ost#[status] <= mesiI /\
          ost#[dir].(dir_st) <= mesiS
      | mesiRqM:
          ost#[owned] = false /\ ost#[status] <= mesiS /\
          ost#[dir].(dir_st) <= mesiS
      end).

  Definition DownLockFromChild (oidx: IdxT) (rqid: RqInfo Msg) :=
    exists cidx,
      rqid.(rqi_midx_rsb) = Some (downTo cidx) /\
      parentIdxOf topo cidx = Some oidx.

  Definition DownLockFromParent (oidx: IdxT) (rqid: RqInfo Msg) :=
    rqid.(rqi_midx_rsb) = Some (rsUpFrom oidx).

  Definition MesiDownLockObjInv (oidx: IdxT): ObjInv :=
    fun ost orq =>
      (rqid <+- orq@[downRq];
      rmsg <+- rqid.(rqi_msg);
      match case rmsg.(msg_id) on idx_dec default True with
      | mesiRqS: DownLockFromChild oidx rqid /\
                 ost#[status] <= mesiI /\ mesiE <= ost#[dir].(dir_st) <= mesiM /\
                 In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
                 map fst rqid.(rqi_rss) = [rsUpFrom ost#[dir].(dir_excl)]
      | mesiRqM: DownLockFromChild oidx rqid /\
                 ost#[status] <= mesiS /\
                 ((ost#[owned] = true /\ ost#[dir].(dir_st) = mesiS /\
                   SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
                   (rsb <+- rqid.(rqi_midx_rsb);
                   map fst rqid.(rqi_rss) =
                   map rsUpFrom (remove idx_dec (objIdxOf rsb) ost#[dir].(dir_sharers)))) \/
                  (mesiE <= ost#[dir].(dir_st) <= mesiM /\
                   In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
                   map fst rqid.(rqi_rss) = [rsUpFrom ost#[dir].(dir_excl)]))
      | mesiDownRqS: DownLockFromParent oidx rqid /\
                     ost#[status] <= mesiI /\ mesiE <= ost#[dir].(dir_st) <= mesiM /\
                     In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
                     map fst rqid.(rqi_rss) = [rsUpFrom ost#[dir].(dir_excl)]
      | mesiDownRqIS: DownLockFromParent oidx rqid /\
                      ost#[dir].(dir_st) = mesiS /\
                      SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
                      map fst rqid.(rqi_rss) = map rsUpFrom ost#[dir].(dir_sharers)
      | mesiDownRqIM: DownLockFromParent oidx rqid /\
                      ((ost#[dir].(dir_st) = mesiS /\
                        SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
                        map fst rqid.(rqi_rss) = map rsUpFrom ost#[dir].(dir_sharers)) \/
                       (mesiE <= ost#[dir].(dir_st) <= mesiM /\
                        In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
                        map fst rqid.(rqi_rss) = [rsUpFrom ost#[dir].(dir_excl)]))
      end).

  Definition MesiObjInvs (oidx: IdxT): ObjInv :=
    fun ost orq =>
      MesiUpLockObjInv oidx ost orq /\
      MesiDownLockObjInv oidx ost orq.

End ObjInv.

Ltac disc_mesi_obj_invs :=
  repeat
    match goal with
    | [H: MesiObjInvs _ _ _ _ |- _] => destruct H
    | [H: MesiUpLockObjInv _ _ _ |- _] =>
      red in H; mred; simpl in H; disc_rule_conds_const
    | [H: MesiDownLockObjInv _ _ _ _ |- _] =>
      red in H; mred; simpl in H; disc_rule_conds_const
    | [Hmsg: msg_id ?rmsg = _, H: context [msg_id ?rmsg] |- _] =>
      rewrite Hmsg in H; simpl in H
    end.

