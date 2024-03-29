Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Msi Ex.MsiInc.Msi.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

#[global] Existing Instance Msi.ImplOStateIfc.

Section ObjInv.
  Variable topo: DTree.

  Definition MsiUpLockObjInv (oidx: IdxT): ObjInv :=
    fun ost orq =>
      (rqiu <+- orq@[upRq];
      rmsg <+- rqiu.(rqi_msg);
      match case rmsg.(msg_id) on idx_dec default True with
      | msiRqS:
          ost#[owned] = false /\ ost#[status] <= msiI /\
          ost#[dir].(dir_st) <= msiS
      | msiRqM:
          ost#[owned] = false /\ ost#[status] <= msiS /\
          ost#[dir].(dir_st) <= msiS
      end).

  Definition DownLockFromChild (oidx: IdxT) (rqid: RqInfo Msg) :=
    exists cidx,
      rqid.(rqi_midx_rsb) = Some (downTo cidx) /\
      parentIdxOf topo cidx = Some oidx.

  Definition DownLockFromParent (oidx: IdxT) (rqid: RqInfo Msg) :=
    rqid.(rqi_midx_rsb) = Some (rsUpFrom oidx).

  Definition MsiDownLockObjInv (oidx: IdxT): ObjInv :=
    fun ost orq =>
      (rqid <+- orq@[downRq];
      match rqid.(rqi_msg) with
      | None =>
        (* NOTE: it is a bit too hacky, but back invalidation is the only case
         * that [rqi_msg = None] holds. *)
        ((ost#[dir].(dir_st) = msiS /\
          SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
          map fst rqid.(rqi_rss) = map rsUpFrom (ost#[dir].(dir_sharers))) \/
         (ost#[dir].(dir_st) = msiM /\
          In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
          map fst rqid.(rqi_rss) = [rsUpFrom ost#[dir].(dir_excl)]))
      | Some rmsg =>
        (match case rmsg.(msg_id) on idx_dec default True with
         | msiRqS: DownLockFromChild oidx rqid /\
                   ost#[status] <= msiI /\ ost#[dir].(dir_st) = msiM /\
                   In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
                   map fst rqid.(rqi_rss) = [rsUpFrom ost#[dir].(dir_excl)]
         | msiRqM: DownLockFromChild oidx rqid /\
                   ost#[status] <= msiS /\
                   ((ost#[owned] = true /\ ost#[dir].(dir_st) = msiS /\
                     SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
                     (rsb <+- rqid.(rqi_midx_rsb);
                     map fst rqid.(rqi_rss) =
                     map rsUpFrom (remove idx_dec (objIdxOf rsb) ost#[dir].(dir_sharers)))) \/
                    (ost#[dir].(dir_st) = msiM /\
                     In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
                     map fst rqid.(rqi_rss) = [rsUpFrom ost#[dir].(dir_excl)]))
         | msiDownRqS: DownLockFromParent oidx rqid /\
                       ost#[status] <= msiI /\ ost#[dir].(dir_st) = msiM /\
                       In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
                       map fst rqid.(rqi_rss) = [rsUpFrom ost#[dir].(dir_excl)]
         | msiDownRqIS: DownLockFromParent oidx rqid /\
                        ost#[dir].(dir_st) = msiS /\
                        SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
                        map fst rqid.(rqi_rss) = map rsUpFrom ost#[dir].(dir_sharers)
         | msiDownRqIM: DownLockFromParent oidx rqid /\
                        ((ost#[dir].(dir_st) = msiS /\
                          SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
                          map fst rqid.(rqi_rss) = map rsUpFrom ost#[dir].(dir_sharers)) \/
                         (ost#[dir].(dir_st) = msiM /\
                          In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
                          map fst rqid.(rqi_rss) = [rsUpFrom ost#[dir].(dir_excl)]))
         end)
      end).

  Definition MsiObjInvs (oidx: IdxT): ObjInv :=
    fun ost orq =>
      MsiUpLockObjInv oidx ost orq /\
      MsiDownLockObjInv oidx ost orq.

End ObjInv.

Ltac disc_msi_obj_invs :=
  repeat
    match goal with
    | [H: MsiObjInvs _ _ _ _ |- _] => destruct H
    | [H: MsiUpLockObjInv _ _ _ |- _] =>
      red in H; mred; simpl in H; disc_rule_conds_const
    | [H: MsiDownLockObjInv _ _ _ _ |- _] =>
      red in H; mred; simpl in H; disc_rule_conds_const
    | [Hmsg: msg_id ?rmsg = _, H: context [msg_id ?rmsg] |- _] =>
      rewrite Hmsg in H; simpl in H
    end.
