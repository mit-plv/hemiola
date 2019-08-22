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

(* NOTE: these ltacs only work for constants (channels, objects, etc.),
 * thus will be used only in this file.
 *)
(* Ltac get_lock_minds oidx := *)
(*   progress (good_footprint_get oidx); *)
(*   repeat (repeat disc_rule_conds_unit_simpl; try disc_footprints_ok); *)
(*   disc_minds_const. *)
 
(* Ltac get_lock_inv obj sys := *)
(*   let H := fresh "H" in *)
(*   assert (In obj (sys_objs sys)) as H by (simpl; tauto); *)
(*   progress (good_locking_get obj); *)
(*   clear H. *)

Existing Instance Mesi.ImplOStateIfc.

Definition MsgExistsSig (sig: MSig) (msgs: MessagePool Msg) :=
  exists idm, InMPI msgs idm /\ sigOf idm = sig.

Section Inv.

  Section ObjUnit.
    Variables (oidx: IdxT)
              (orq: ORq Msg)
              (ost: OState)
              (msgs: MessagePool Msg).

    Definition MsgNotRsI (idm: Id Msg) :=
      match case (sigOf idm) on sig_dec default True with
        |! (downTo oidx, (MRs, mesiRsI)): False
      end.

    Definition NoRsI :=
      forall idm, InMPI msgs idm -> MsgNotRsI idm.

    Definition ImplOStateMESI (cv: nat): Prop :=
      mesiS <= ost#[implStatusIdx] -> NoRsI ->
      ost#[implValueIdx] = cv.

    Definition NotCohMsg (idm: Id Msg) :=
      match case (sigOf idm) on sig_dec default True with
      | (downTo oidx, (MRs, mesiRsS)): False
      | (downTo oidx, (MRs, mesiRsE)): False
      | (rsUpFrom oidx, (MRs, mesiDownRsS)): False
      end.

    Definition NoCohMsgs :=
      forall idm, InMPI msgs idm -> NotCohMsg idm.

    Definition CohRqI :=
      forall idm,
        InMPI msgs idm ->
        sigOf idm = (rqUpFrom oidx, (MRq, mesiRqI)) ->
        msg_value (valOf idm) = ost#[implValueIdx].

    Definition ObjExcl0 :=
      mesiE <= ost#[implStatusIdx] /\ NoRsI /\ NoCohMsgs /\ CohRqI.

    Definition ObjExcl :=
      ObjExcl0 \/
      MsgExistsSig (downTo oidx, (MRs, mesiRsE)) msgs \/
      MsgExistsSig (downTo oidx, (MRs, mesiRsM)) msgs.

    Definition ObjInvalid0 :=
      ost#[implStatusIdx] = mesiI /\ NoCohMsgs.

    Definition ObjInvalid :=
      ObjInvalid0 \/
      MsgExistsSig (downTo oidx, (MRs, mesiRsI)) msgs.

    Section Facts.

      Lemma NoRsI_MsgExistsSig_false:
        MsgExistsSig (downTo oidx, (MRs, mesiRsI)) msgs ->
        NoRsI -> False.
      Proof.
        intros.
        destruct H as [idm [? ?]].
        specialize (H0 _ H).
        red in H0; rewrite H1 in H0.
        unfold caseDec in H0.
        find_if_inside; auto.
      Qed.

    End Facts.
    
  End ObjUnit.

  Definition InvExcl (st: MState): Prop :=
    forall eidx,
      eost <+- (bst_oss st)@[eidx];
        (ObjExcl eidx eost (bst_msgs st) ->
         forall oidx,
           oidx <> eidx ->
           ost <+- (bst_oss st)@[oidx];
             ObjInvalid oidx ost (bst_msgs st)).

End Inv.

Hint Unfold NoRsI ImplOStateMESI ObjExcl0 ObjExcl
     NoCohMsgs CohRqI ObjInvalid0 ObjInvalid: RuleConds.

