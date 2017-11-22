Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics SemFacts.
Require Import StepDet StepSeq Serial SerialFacts Simulation Predicate.

Set Implicit Arguments.

Section SimP.

  (** User inputs *)
  Variables
    (impl0 spec: System)
    (R: TState -> TState -> Prop)
    (p: Label -> Label).

  Definition SynthOk (s: System) :=
    SerializableSys s step_det /\
    R (getStateInit s) (getStateInit spec) /\
    Simulates step_seq step_det R p s spec.

  Hypothesis (Hinit_ok: SynthOk impl0).

  Section SynthesisStep.

    Definition SynT := System -> System -> Prop.
    Variable syn: SynT.

    (** The synthesizer [syn] should "preserve" three conditions:
     * 1) initial state
     * 2) serializability
     * 3) simulation on sequential semantics
     *)
    Hypotheses (Hsyn_init: forall s s', syn s s' -> getStateInit s' = getStateInit s)
               (Hsyn_serial:
                  forall s, SerializableSys s step_det ->
                            forall s', syn s s' -> SerializableSys s' step_det)
               (Hsyn_sim:
                  forall s, Simulates step_seq step_det R p s spec ->
                            forall s', syn s s' ->
                                       Simulates step_seq step_det R p s' spec).

    Lemma synthOk_refinement:
      forall s, SynthOk s -> step_det # step_det |-- s ⊑[p] spec.
    Proof.
      unfold SynthOk; intros; dest.
      eapply refines_trans.
      - apply sequential_step_seq.
        eauto using Hsyn_serial.
      - apply simulation_implies_refinement with (sim:= R); assumption.
    Qed.

    Lemma synthOk_preserved:
      forall s s', SynthOk s -> syn s s' -> SynthOk s'.
    Proof.
      unfold SynthOk; intros; dest.
      repeat split; eauto.
      erewrite Hsyn_init; eauto.
    Qed.

  End SynthesisStep.

End SimP.

Section SimTrs.

  Definition SimEquivO (ost1 ost2: OState) :=
    ost_tst ost1 = ost_tst ost2 /\
    (ost_tst ost1 = [] -> ost_st ost1 = ost_st ost2).

  Definition SimEquiv (os1 os2: ObjectStates) :=
    forall oidx,
      match os1@[oidx], os2@[oidx] with
      | Some ost1, Some ost2 => SimEquivO ost1 ost2
      | None, None => True
      | _, _ => False
      end.

  Inductive SimTrsO (R: ObjectStates -> ObjectStates -> Prop):
    ObjectStates -> ObjectStates -> Prop :=
  | SimTrsOIntro:
      forall ioss rioss,
        SimEquiv ioss rioss ->
        forall soss,
          R rioss soss ->
          SimTrsO R ioss soss.

  Definition SimTrs (R: ObjectStates -> ObjectStates -> Prop)
             (ioss soss: TState): Prop :=
    SimTrsO R (tst_oss ioss) (tst_oss soss).

End SimTrs.

Section SynTrs.
  Variables (trsIdx: IdxT)
            (this: IdxT).

  Definition rqChn: IdxT := 0.
  Definition rsChn: IdxT := 1.

  Definition TPMsg mid outs postcond :=
    {| pmsg_mid := mid;
       pmsg_precond := fun _ => True;
       pmsg_outs := outs;
       pmsg_postcond := postcond |}.

  Section Immediate.

    Definition synRqOuts (tochns: list (IdxT * IdxT)) (val: Value) :=
      map (fun tochn => {| msg_id := {| mid_type := trsIdx;
                                        mid_from := this;
                                        mid_to := fst tochn;
                                        mid_chn := snd tochn
                                     |};
                           msg_value := val
                        |}) tochns.

    Definition synImm (rqfrom: IdxT) (postcond: PostCond)
               (valOut: StateT -> Value -> Value) :=
      TPMsg {| mid_type := trsIdx;
               mid_from := rqfrom;
               mid_to := this;
               mid_chn := rqChn |}
            (fun st val => synRqOuts ((rqfrom, rsChn) :: nil) (valOut (ost_st st) val))
            postcond.

  End Immediate.

  Section RequestFwd.
    Variables (rqfrom: IdxT) (fwds: list IdxT).

    Definition synRqPostcond (pre: OState) (val: Value) (post: OState) :=
      post = {| ost_st := ost_st pre;
                ost_tst := (ost_tst pre)
                           +[ trsIdx <- {| tst_rqfrom := rqfrom;
                                           tst_rqfwds := map (fun idx => (idx, None)) fwds |}]
             |}.

    Definition synRq (prec: PreCond) :=
      {| pmsg_mid := {| mid_type := trsIdx;
                        mid_from := rqfrom;
                        mid_to := this;
                        mid_chn := rqChn |};
         pmsg_precond :=
           fun ost =>
             prec ost /\
             (** FIXME: need a more fine-grained lock condition *)
             ost_tst ost = [];
         pmsg_outs := fun _ val => synRqOuts (map (fun to => (to, rqChn)) fwds) val;
         pmsg_postcond := synRqPostcond
      |}.

  End RequestFwd.

  Section ResponseBack.
    Variable rsFrom: IdxT.

    Fixpoint checkResponded (rss: list (IdxT * option Value)) (rsVal: Value) :=
      match rss with
      | nil => nil
      | (idx, ov) :: rss' =>
        if idx ==n rsFrom
        then (idx, Some rsVal) :: rss'
        else (idx, ov) :: (checkResponded rss' rsVal)
      end.

    Definition Responded (pre: OState) (rsVal: Value) (post: OState) :=
      (ost_tst pre)@[trsIdx] >>=[False]
      (fun preth =>
         (ost_tst post)@[trsIdx] >>=[False]
         (fun postth =>
            postth = {| tst_rqfrom := tst_rqfrom preth;
                        tst_rqfwds := checkResponded (tst_rqfwds preth) rsVal |})).

    Definition allResponded (fwds: list (IdxT * option Value)) :=
      forallb (fun ib => match snd ib with
                         | Some _ => true
                         | _ => false
                         end) fwds.

    Definition WhenAllResponded (postcond: PostCond)
               (pre: OState) (val: Value) (post: OState) :=
      (ost_tst pre)@[trsIdx] >>=[False]
      (fun trsh =>
         if allResponded (tst_rqfwds trsh)
         then postcond pre val post /\
              ost_tst post = M.remove trsIdx (ost_tst pre)
         else True).

    Fixpoint getFwdValue (vals: list (IdxT * option Value)) :=
      match vals with
      | nil => VUnit
      | (_, Some v) :: vals' =>
        match v with
        | VUnit => getFwdValue vals'
        | _ => v
        end
      | (_, None) :: vals' => getFwdValue vals'
      end.

    Definition rsFwdValue (post: OState) :=
      (ost_tst post)@[trsIdx] >>=[VUnit]
      (fun trsh =>
         getFwdValue (tst_rqfwds trsh)).
         
    Definition synRsPostcond (postcond: PostCond)
               (pre: OState) (val: Value) (post: OState) :=
      Responded pre val post /\
      (exists post',
          Responded pre val post' /\
          WhenAllResponded postcond post' (rsFwdValue post') post).

    Definition synRsOuts (rsOut: StateT -> list (IdxT * option Value) -> Value) :=
      fun st val =>
        (ost_tst st)@[trsIdx] >>=[nil]
        (fun trsh =>
           let rss := checkResponded (tst_rqfwds trsh) val in
           if allResponded rss
           then {| msg_id := {| mid_type := trsIdx;
                                mid_from := this;
                                mid_to := tst_rqfrom trsh;
                                mid_chn := rsChn |};
                   msg_value := rsOut (ost_st st) rss |} :: nil
           else nil).

    (* NOTE: [postcond] is a desired postcondition when assuming 
     * the transaction is atomic.
     *)
    Definition synRs (postcond: PostCond)
               (rsOut: StateT -> list (IdxT * option Value) -> Value) :=
      TPMsg {| mid_type := trsIdx;
               mid_from := rsFrom;
               mid_to := this;
               mid_chn := rsChn |}
            (synRsOuts rsOut)
            (synRsPostcond postcond).

  End ResponseBack.

  Section AddPMsgs.

    Definition buildRawObjs (oobs: list Object): list Object :=
      map (fun obj => {| obj_idx := obj_idx obj;
                         obj_state_init := obj_state_init obj;
                         obj_trs := nil |}) oobs.

    Definition buildRawSys (osys: System) :=
      {| sys_objs := buildRawObjs (sys_objs osys);
         sys_chns := sys_chns osys |}.

    Definition addPMsgsO (pmsgs: list PMsg) (obj: Object) :=
      {| obj_idx := obj_idx obj;
         obj_state_init := obj_state_init obj;
         obj_trs :=
           (filter (fun pmsg =>
                      if mid_to (pmsg_mid pmsg) ==n obj_idx obj
                      then true else false) pmsgs)
             ++ obj_trs obj |}.

    Fixpoint addPMsgs (pmsgs: list PMsg) (objs: list Object) :=
      match objs with
      | nil => nil
      | obj :: obs' =>
        (addPMsgsO pmsgs obj) :: (addPMsgs pmsgs obs')
      end.

    Definition addPMsgsSys (pmsgs: list PMsg) (sys: System) :=
      {| sys_objs := addPMsgs pmsgs (sys_objs sys);
         sys_chns := sys_chns sys |}.
    
  End AddPMsgs.

  Definition idxInter (li1 li2: list IdxT) :=
    filter (fun idx => if idx ?<n li2 then true else false) li1.
  Definition idxSubtract (li1 li2: list IdxT) :=
    filter (fun idx => if idx ?<n li2 then false else true) li1.
  
End SynTrs.

Section VChange.
  
  Inductive VLoc :=
  | VLocState: forall (oidx kidx: IdxT), VLoc
  | VLocMsg: VLoc.

  Inductive VConst: IdxT -> Set :=
  | VConstIntro: forall (oidx kidx: IdxT) (const: Value), VConst oidx.

  Inductive VMoved: IdxT -> Set :=
  | VMovedIntro: forall (source: VLoc) (oidx kidx: IdxT), VMoved oidx.

  Record VChanges :=
    { vchg_consts: list { targetIdx: IdxT & VConst targetIdx };
      vchg_moved: option { targetIdx: IdxT & VMoved targetIdx}
    }.

  Fixpoint getTargetConsts (chgs: list { targetIdx: IdxT & VConst targetIdx })
           (tidx: IdxT): list (VConst tidx) :=
    match chgs with
    | nil => nil
    | (existT _ idx const) :: chgs' =>
      (match idx ==n tidx with
       | left Heq => match Heq with
                     | eq_refl => Some const
                     end
       | _ => None
       end) ::> (getTargetConsts chgs' tidx)
    end.

  Definition getTargetMoved (omv: option { targetIdx: IdxT & VMoved targetIdx })
             (tidx: IdxT): option (VMoved tidx) :=
    omv >>= (fun moved =>
               match moved with
               | existT _ idx mv =>
                 match idx ==n tidx with
                 | left Heq => match Heq with
                               | eq_refl => Some mv
                               end
                 | _ => None
                 end
               end).

  Definition getChangeTargets (chgs: VChanges): list IdxT :=
    ((vchg_moved chgs) >>= (fun mv => Some (projT1 mv)))
      ::> (map (projT1 (P:= VConst)) (vchg_consts chgs)).

End VChange.

Section SynByVChanges.
  Variables trsIdx: IdxT.

  Section PerTarget.
    Context {targetIdx: IdxT}.

    Section Immediate.

      (** TODO: define *)

    End Immediate.

    Section RequestFwd.
      Variable topo: list Channel.

      Definition synRqVChanges (rqFrom: IdxT) (remChgs: VChanges) (prec: PreCond) :=
        synRq trsIdx targetIdx rqFrom
              (idxInter (getChangeTargets remChgs) (getForwards topo targetIdx))
              prec.

    End RequestFwd.

    Section ResponseBack.
      
      Fixpoint constUpdatesOf (consts: list (VConst targetIdx))
               (pre: StateT) :=
        match consts with
        | nil => pre
        | (VConstIntro _ kidx val) :: chgs' =>
          constUpdatesOf chgs' (pre +[kidx <- val])
        end.

      Definition movedUpdatedOf (mv: option (VMoved targetIdx)) (val: Value)
                 (pre: StateT) :=
        match mv with
        | Some (VMovedIntro _ _ kidx) => pre +[kidx <- val]
        | _ => pre
        end.

      Definition updatesOf (consts: list (VConst targetIdx)) (mv: option (VMoved targetIdx)) :=
        fun pre val post =>
          ost_st post = movedUpdatedOf
                          mv val
                          (constUpdatesOf consts (ost_st pre)).

      Definition rsPostcondVChanges (chgs: VChanges) :=
        updatesOf (getTargetConsts (vchg_consts chgs) targetIdx)
                  (getTargetMoved (vchg_moved chgs) targetIdx).

      Definition rsOutsVChanges (vmoved: option (VMoved targetIdx))
                 (pre: StateT) (rss: list (IdxT * option Value)) :=
        match vmoved with
        | Some _ => VUnit (* nothing to forward, since the target is the destination. *)
        | None => getFwdValue rss
        end.

      Definition synRsVChanges (rsFrom: IdxT) (chgs: VChanges) :=
        synRs trsIdx targetIdx rsFrom 
              (rsPostcondVChanges chgs)
              (rsOutsVChanges (getTargetMoved (vchg_moved chgs) targetIdx)).

    End ResponseBack.

  End PerTarget.

  (** TODO: define *)
  (* Inductive SynVChanges: list PMsg -> VChanges -> Prop := *)
  (* | SynVChangeInit: *)

End SynByVChanges.

(** Some tactics about [VLoc] and [VChange] *)

Ltac no_vloc_st oss oidx kidx :=
  lazymatch goal with
  | [vloc := (oss, VLocState oidx kidx, _) |- _] => fail
  | _ => idtac
  end.

(* NOTE: there's only one [VLocMsg] information per a transaction. *)
Ltac no_vloc_msg :=
  lazymatch goal with
  | [vloc := (VLocMsg, _) |- _] => fail
  | _ => idtac
  end.

Ltac collect_vloc :=
  repeat
    match goal with
    | [H1: M.find ?oidx ?oss = Some ?ost, H2: M.find ?kidx (ost_st ?ost) = Some ?v |- _] =>
      no_vloc_st oss oidx kidx;
      let vloc := fresh "vloc" in
      set (oss, VLocState oidx kidx, v) as vloc
    | [H: pmsg_postcond _ _ ?v _ |- _] =>
      no_vloc_msg;
      let vloc := fresh "vloc" in
      set (VLocMsg, v) as vloc
    end.

Ltac no_diff sdf :=
  lazymatch goal with
  | [df := sdf |- _] => fail
  | _ => idtac
  end.

Ltac collect_diff oss1 oss2 :=
  repeat
    match goal with
    | [vloc := (oss2, VLocState ?oidx ?kidx, ?v) |- _] =>
      is_pure_const v;
      no_diff (VConstIntro oidx kidx v);
      let df := fresh "df" in
      pose (VConstIntro oidx kidx v) as df
    | [vloc1 := (oss1, ?wh1, ?v),
       vloc2 := (oss2, VLocState ?oidx2 ?kidx2, ?v) |- _] =>
      not_pure_const v;
      first [is_equal wh1 (VLocState oidx2 kidx2) |
             no_diff (VMovedIntro wh1 oidx2 kidx2);
             let df := fresh "df" in
             pose (VMovedIntro wh1 oidx2 kidx2) as df]
    end.

