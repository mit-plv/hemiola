Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM StepT SemFacts.
Require Import Topology Serial SerialFacts.
Require Import QuasiSeq Reduction Transaction.
Require Import Topology.

Require Import Omega.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section RqRs.
  Variable (RqRsT: Type).

  Definition RqRsDec := MLabel -> RqRsT.
  Definition RqRsComm := RqRsT -> RqRsT -> Prop.

  Variables (rrdec: RqRsDec) (rrc: RqRsComm).

  Definition RqRsCommHistories (hst1 hst2: MHistory) :=
    forall lbl1 lbl2,
      In lbl1 hst1 -> In lbl2 hst2 ->
      rrc (rrdec lbl1) (rrdec lbl2).

  Definition RqRsLPush (hst1 hst: MHistory) :=
    RqRsCommHistories hst1 hst.

  Definition RqRsRPush (hst2 hst: MHistory) :=
    RqRsCommHistories hst hst2.

  Definition RqRsContComm {oifc} (sys: System oifc) :=
    forall hst1 hst2,
      ValidContinuous sys hst1 hst2 ->
      RqRsCommHistories hst1 hst2.

  Definition RqRsLRPushable {oifc} (sys: System oifc) :=
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall st2 hst1 hst2 hsts,
        steps step_m sys st1 (List.concat (hst2 :: hsts ++ [hst1])) st2 ->
        Continuous hst1 hst2 ->
        Forall (AtomicEx msg_dec) hsts ->
        LRPushable sys (RqRsLPush hst1) (RqRsRPush hst2) (hsts ++ [hst1]) /\
        LRPushable sys (RqRsLPush hst1) (RqRsRPush hst2) (hst2 :: hsts).

  Definition RqRsLOrR {oifc} (sys: System oifc) :=
    forall st1 st2 hst1 hst2 hsts,
      steps step_m sys st1 (List.concat (hst2 :: hsts ++ [hst1])) st2 ->
      Continuous hst1 hst2 ->
      Forall (AtomicEx msg_dec) hsts ->
      Forall (fun hst => RqRsLPush hst1 hst \/ RqRsRPush hst2 hst) hsts.
  
  Definition RqRsSys {oifc} (sys: System oifc) :=
    RqRsContComm sys /\
    RqRsLRPushable sys /\
    RqRsLOrR sys.

End RqRs.

Section RqRsSerial.
  Context {oifc: OStateIfc}.
  Variables (gtr: DTree)
            (RqRsT: Type)
            (rrdec: RqRsDec RqRsT)
            (rrc: RqRsComm RqRsT)
            (sys: System oifc).

  Hypotheses (* (Htr: TreeTopoSys gtr sys) *)
             (* (Hpb: HalfLockSys (* gtr *) sys) *)
             (Hrr: RqRsSys rrdec rrc sys).

  Lemma rqrs_well_interleaved_push:
    WellInterleavedPush sys.
  Proof.
    red; intros.
    exists (RqRsLPush rrdec rrc hst1).
    exists (RqRsRPush rrdec rrc hst2).
    pose proof H; destruct H0.
    split; [|split; [|split; [|split]]];
      try (eapply Hrr; eauto; fail).
  Qed.

  Theorem immrqrs_pb_serializable:
    SerializableSys sys.
  Proof.
    apply well_interleaved_serializable.
    apply well_interleaved_push_ok.
    apply rqrs_well_interleaved_push.
  Qed.

End RqRsSerial.

Close Scope list.
Close Scope fmap.

