Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepDet Serial.
Require Import Synthesis TrsInv TrsSim.

Section AtomicRules.
  
  Variable (tid: IdxT).

  (* Inductive AtomicRules: Msg -> list Rule -> Prop := *)
  (* | ARImm: *)
  (*     forall from to v prec postc valOut, *)
  (*       AtomicRules *)
  (*         (buildMsg (buildMsgId tid from to rqChn) v) *)
  (*         (synImm tid to prec from postc valOut :: nil) *)
  (* | ARRqRs: *)
  (*     forall (rrs: list (Msg * list Rule)), *)
  (*       Forall (fun rr => AtomicRules (fst rr) (snd rr)) rrs -> *)
  (*       forall from to rqv rqprec fwds rspostc rsOut, *)
  (*         fwds = map (fun rr => mid_to (msg_id (fst rr))) rrs -> *)
  (*         AtomicRules *)
  (*           (buildMsg (buildMsgId tid from to rqChn) rqv) *)
  (*           ((synRq tid to alwaysLock from fwds rqprec) *)
  (*              :: (concat (map snd rrs)) *)
  (*              ++ (map (fun rsbFrom => synRs tid to rsbFrom rspostc rsOut) fwds)). *)

End AtomicRules.

Section Compositionality.

  Variables
    (rqin: MsgId)
    (rqfwds: list MsgId)
    (rsbacks: list MsgId)
    (rsout: MsgId)

    (rqfwdR: Rule)
    (rssbRs: list Rule)
    (subRs: list Rule)
    
    (sim: TState -> TState -> Prop)
    (p: Label -> Label)

    (spec: System).

  (* FIXME: remove [sys] and [ssys], and replace all uses with appropriate systems. *)
  Variables (sys ssys: System).

  Local Infix "≈" := sim (at level 30).

  Local Definition rqfwdTMsgs (v: Value) (ti: TInfo) :=
    map (fun mid => toTMsg ti {| msg_id := mid; msg_value := v |}) rqfwds.

  Definition SimRqF :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ist2 v ti,
        step_det sys ist1 (IlblOuts (Some (toTMsgU (buildMsg rqin v)))
                                    (rqfwdTMsgs v ti)) ist2 ->
        ist2 ≈ sst1.

  Definition SimRs :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ti rsb rsv ist2,
        In rsb rsbacks ->
        step_det sys ist1 (IlblOuts (Some (toTMsg ti (buildMsg rsb rsv))) nil) ist2 ->
        ist2 ≈ ist1.

  Definition SimRsB :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ti rsb rsv ist2,
        In rsb rsbacks ->
        step_det sys ist1 (IlblOuts (Some (toTMsg ti (buildMsg rsb rsv)))
                                    (toTMsg ti (buildMsg rsb rsv) :: nil)) ist2 ->
        exists slbl sst2,
          step_det spec sst1 slbl sst2 /\
          extLabel spec (getLabel slbl) =
          Some (p (LblOuts (buildMsg rsb rsv :: nil))) /\
          ist2 ≈ sst2.

  Definition SubAtomicSim :=
    forall ti hst mouts orsout,
      Atomic ssys ti hst mouts orsout ->
      forall ist1 sst1,
        ist1 ≈ sst1 ->
        forall ist2,
          steps_det ssys ist1 hst ist2 ->
          exists (sst2 : TState) (shst : list TLabel),
            steps_det spec sst1 shst sst2 /\
            map p (behaviorOf ssys hst) = behaviorOf spec shst /\
            ist2 ≈ sst2.

  Hypotheses (Hrqf: SimRqF) (Hrs: SimRs) (Hrsb: SimRsB)
             (Hsub: SubAtomicSim).

  Theorem atomic_sim_compositional:
    forall ti hst mouts orsout,
      Atomic sys ti hst mouts orsout ->
      forall ist1 sst1,
        ist1 ≈ sst1 ->
        forall ist2,
          steps_det ssys ist1 hst ist2 ->
          exists (sst2 : TState) (shst : list TLabel),
            steps_det spec sst1 shst sst2 /\
            map p (behaviorOf ssys hst) = behaviorOf spec shst /\
            ist2 ≈ sst2.
  Proof.
  Admitted.

End Compositionality.

