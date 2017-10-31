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

Section SynPerObj.
  Variables (trsIdx: IdxT)
            (this: IdxT).

  Definition synPMsgOuts (tos: list IdxT) (val: Value) :=
    map (fun to => {| msg_id := {| mid_type := trsIdx;
                                   mid_from := this;
                                   mid_to := to;
                                   mid_chn := 0; (* TODO: how to decide a channel to use *)
                                |};
                      msg_value := val
                   |}) tos.

  Section Request.
    Variables (rqfrom: IdxT) (fwds: list IdxT).

    (* TODO: correct preconditions for safe interleavings *)
    Definition synPMsgRqPrecond (st: OState) := True.

    Definition synPMsgRqPostcond (pre: OState) (val: Value) (post: OState) :=
      post = {| ost_st := ost_st pre;
                ost_tst := (ost_tst pre)
                           +[ trsIdx <- {| tst_rqfrom := rqfrom;
                                           tst_rqfwds := map (fun idx => (idx, false)) fwds |}]
             |}.

    Definition synPMsgRq (chn: IdxT): PMsg :=
      {| pmsg_mid := {| mid_type := trsIdx;
                        mid_from := rqfrom;
                        mid_to := this;
                        mid_chn := chn |};
         pmsg_precond := synPMsgRqPrecond;
         pmsg_outs := fun _ val => synPMsgOuts fwds val;
         pmsg_postcond := synPMsgRqPostcond |}.

  End Request.

  Section Response.
    Variable rsFrom: IdxT.

    (* TODO: pre/postconditions for safe interleavings *)
    Definition synPMsgRsPrecond (st: OState) :=
      True.

    Fixpoint addResponse (fwds: list (IdxT * bool)) :=
      match fwds with
      | nil => nil
      | (idx, b) :: fwds' =>
        if idx ==n rsFrom
        then (idx, true) :: fwds'
        else (idx, b) :: (addResponse fwds')
      end.

    Definition Responded (pre: OState) (post: OState) :=
      (ost_tst pre)@[trsIdx] >>=[False]
      (fun preth =>
         (ost_tst post)@[trsIdx] >>=[False]
         (fun postth =>
            postth = {| tst_rqfrom := tst_rqfrom preth;
                        tst_rqfwds := addResponse (tst_rqfwds preth) |})).

    Definition allResponded (fwds: list (IdxT * bool)) :=
      forallb (fun ib => snd ib) fwds.

    Definition WhenAllResponded (oinv: OInv) (val: Value)
               (pre post: OState) :=
      (ost_tst post)@[trsIdx] >>=[False]
      (fun trsh =>
         if allResponded (tst_rqfwds trsh)
         then pre = post
         else oinv post val).

    Definition synPMsgRsPostcond (oinv: OInv) (pre: OState) (val: Value) (post: OState) :=
      Responded pre post /\
      WhenAllResponded oinv val pre post.

    (* TODO: how to decide a channel [chn] to use *)
    Definition synPMsgRs (chn: IdxT) (oinv: OInv): PMsg :=
      {| pmsg_mid := {| mid_type := trsIdx;
                        mid_from := rsFrom;
                        mid_to := this;
                        mid_chn := chn |};
         pmsg_precond := synPMsgRsPrecond;
         pmsg_outs :=
           fun st val =>
             (ost_tst st)@[trsIdx] >>=[nil]
             (fun trsh =>
                if allResponded (tst_rqfwds trsh)
                then synPMsgOuts (tst_rqfrom trsh :: nil) val
                else nil);
         pmsg_postcond := synPMsgRsPostcond oinv |}.

    Definition synPMsgImm (chn: IdxT) (oinv: OInv): PMsg :=
      {| pmsg_mid := {| mid_type := trsIdx;
                        mid_from := rsFrom;
                        mid_to := this;
                        mid_chn := chn |};
         pmsg_precond := fun _ => True;
         pmsg_outs := fun _ val => synPMsgOuts (rsFrom :: nil) val;
         pmsg_postcond := synPMsgRsPostcond oinv |}.

  End Response.
  
End SynPerObj.

Section SynPerTrs.

  Variables
    (* A transaction index uniquely assigned for this transaction *)
    (trsIdx: IdxT)
    (trsVal: Value)
    (* A transaction predicate *)
    (trspred: Pred).

  Local Definition targetObjs := map fst (M.elements trspred).

  Fixpoint getTos (me: IdxT) (topo: list Channel) :=
    match topo with
    | nil => nil
    | chn :: t =>
      if me ==n chn_from chn
      then chn_to chn :: getTos me t
      else getTos me t
    end.

  Fixpoint idxInter (li1 li2: list IdxT) :=
    filter (fun idx => if idx ?<n li2 then true else false) li1.

  Inductive SynTrs (efrom hdl: IdxT) (topo: list Channel):
    list MsgId (* currently synthesizable messages *) ->
    Pred (* current transaction predicate *) ->
    list Object (* synthesized objects *) -> Prop :=
  | SynTrsStart:
      forall objs chn mid,
        mid = {| mid_type := trsIdx; mid_from := efrom; mid_to := hdl; mid_chn := chn |} ->
        SynTrs efrom hdl topo (mid :: nil) trspred objs
  | SynTrsStep:
      forall oidx mids1 mid mids2 preds objs1 obj objs2 oinv fwds synrq synrss mouts nobj,
        SynTrs efrom hdl topo (mids1 ++ mid :: mids2) preds (objs1 ++ obj :: objs2) ->
        oidx = mid_to mid ->
        oidx = obj_idx obj ->
        preds@[oidx] = Some oinv ->
        fwds = idxInter (getTos oidx topo) targetObjs ->
        synrq = synPMsgRq trsIdx oidx (mid_from mid) fwds (mid_chn mid) ->
        synrss = map (fun ridx =>
                        synPMsgRs trsIdx oidx ridx O (* TODO: channel... *)
                                  oinv
                     )
                     fwds ->
        mouts = synPMsgOuts oidx trsIdx
                            (idxInter (getTos oidx topo) targetObjs)
                            trsVal ->
        nobj = {| obj_idx := obj_idx obj;
                  obj_state_init := obj_state_init obj;
                  obj_trs := synrq :: synrss ++ obj_trs obj |} ->
        forall nmids npreds nobjs,
          nmids = mids1 ++ mids2 ++ map msg_id mouts ->
          npreds = M.remove oidx preds ->
          nobjs = objs1 ++ nobj :: objs2 ->
          SynTrs efrom hdl topo nmids npreds nobjs
  | SynTrsEnd:
      forall oidx mids1 mid mids2 preds objs1 obj objs2 oinv synimm nobj,
        SynTrs efrom hdl topo (mids1 ++ mid :: mids2) preds (objs1 ++ obj :: objs2) ->
        oidx = mid_to mid ->
        oidx = obj_idx obj ->
        preds@[oidx] = Some oinv ->
        idxInter (getTos oidx topo) targetObjs = nil ->
        synimm = synPMsgImm trsIdx oidx (mid_from mid) (mid_chn mid) oinv ->
        nobj = {| obj_idx := obj_idx obj;
                  obj_state_init := obj_state_init obj;
                  obj_trs := synimm :: obj_trs obj |} ->
        forall nmids npreds nobjs,
          nmids = mids1 ++ mids2 ->
          npreds = M.remove oidx preds ->
          nobjs = objs1 ++ nobj :: objs2 ->
          SynTrs efrom hdl topo nmids npreds nobjs.

  Definition SynTrsFinished (efrom hdl: IdxT) (topo: list Channel) (objs: list Object) :=
    SynTrs efrom hdl topo nil (M.empty _) objs.

End SynPerTrs.

Section Synthesizer.

  (* A target system *)
  Variable sys: System.

  Local Definition objs := sys_objs sys.
  Local Definition topo := sys_chns sys.

End Synthesizer.

