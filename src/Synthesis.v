Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics SemFacts.
Require Import StepDet StepSeq Serial SerialFacts Simulation Predicate.

Section SimP.

  (** User inputs *)
  Variables
    (impl0 spec: System)
    (R: TState -> TState -> Prop)
    (p: Label -> Label).

  Definition SynthOk (s: System) :=
    Serial s step_det /\
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
                  forall s, Serial s step_det ->
                            forall s', syn s s' -> Serial s' step_det)
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

  Definition NoTrs (ioss: ObjectStates) :=
    forall oidx,
      match ioss@[oidx] with
      | Some os => ost_tst os = M.empty _
      | None => True
      end.

  Inductive SimTrsO (R: ObjectStates -> ObjectStates -> Prop):
    ObjectStates -> ObjectStates -> Prop :=
  | SimTrsStable:
      forall ioss soss,
        R ioss soss ->
        NoTrs ioss ->
        SimTrsO R ioss soss
  | SimTrsTrs:
      forall ioss soss,
        ~ NoTrs ioss ->
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

    Definition synRq :=
      TPMsg {| mid_type := trsIdx;
               mid_from := rqfrom;
               mid_to := this;
               mid_chn := rqChn |}
            (fun _ val => synRqOuts (map (fun to => (to, rqChn)) fwds) val)
            synRqPostcond.

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

    Definition synRsPostcond (postcond: PostCond)
               (pre: OState) (val: Value) (post: OState) :=
      Responded pre val post /\
      (exists post',
          Responded pre val post' /\
          WhenAllResponded postcond post' val post).

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
    
