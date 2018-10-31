Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM StepT SemFacts.
Require Import Topology Serial SerialFacts.
Require Import QuasiSeq Reduction.
Require Import Topology TopologyFacts.

Require Import Omega.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section TreeTopo.
  Variable (gtr: GTree).
  Local Notation topo := (topoOfT gtr).

  Definition TreeTopoRule (oidx: IdxT) {ifc} (rule: Rule ifc) :=
    forall post porq ins nost norq outs,
      rule_trs rule post porq ins = (nost, norq, outs) ->
      (forall min,
          In min ins ->
          exists mfrom, In (createEdge mfrom (idOf min) oidx) (dg_es topo)) /\
      (forall mout,
          In mout outs ->
          exists mto, In (createEdge oidx (idOf mout) mto) (dg_es topo)).

  Definition TreeTopoObj (obj: Object) :=
    Forall (TreeTopoRule (obj_idx obj)) (obj_rules obj).
    
  Definition TreeTopoSys (sys: System) :=
    Forall TreeTopoObj (sys_objs sys).

End TreeTopo.

Section HalfLock.
  Variable (gtr: GTree).

  Definition upRq := 0.
  Definition downRq := 1.

  (** Preconditions to check the lock state *)

  Definition LockFree (orq: ORq Msg) (addr: AddrT) :=
    orq@[addr] >>=[True] (fun aorq => aorq = []).

  Definition HalfLockFree (orq: ORq Msg) (addr: AddrT) :=
    orq@[addr] >>=[True] (fun aorq => aorq@[downRq] = None).


  Definition getDownRq (addr: AddrT) (orq: ORq Msg) :=
    orq@[addr] >>=[None]
       (fun aorq => aorq@[downRq] >>=[None] (fun ri => Some ri)).

  Fixpoint getUpRq (addr: AddrT) (orq: ORq Msg) :=
    orq@[addr] >>=[None]
       (fun aorq => aorq@[upRq] >>=[None] (fun ri => Some ri)).

  (* TODO: define it. *)
  Definition HalfLockPrec (oidx: IdxT) {ifc}: OPrec ifc :=
    fun (ost: OState ifc) (orq: ORq Msg) (ins: list (Id Msg)) =>
      True.

  Definition HalfLockRule (oidx: IdxT) {ifc} (rule: Rule ifc) :=
    (rule_precond rule) ->oprec (HalfLockPrec oidx).

  Definition HalfLockObj (obj: Object) :=
    Forall (HalfLockRule (obj_idx obj)) (obj_rules obj).
  
  Definition HalfLockSys (sys: System) :=
    Forall HalfLockObj (sys_objs sys).

End HalfLock.

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

  Definition RqRsContComm (sys: System) :=
    forall hst1 hst2,
      ValidContinuous sys hst1 hst2 ->
      RqRsCommHistories hst1 hst2.

  Definition RqRsLRPushable (sys: System) :=
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall st2 hst1 hst2 hsts,
        steps step_m sys st1 (List.concat (hst2 :: hsts ++ [hst1])) st2 ->
        Continuous hst1 hst2 ->
        Forall (STransactional msg_dec) hsts ->
        LRPushable sys (RqRsLPush hst1) (RqRsRPush hst2) (hsts ++ [hst1]) /\
        LRPushable sys (RqRsLPush hst1) (RqRsRPush hst2) (hst2 :: hsts).

  Definition RqRsLOrR (sys: System) :=
    forall st1 st2 hst1 hst2 hsts,
      steps step_m sys st1 (List.concat (hst2 :: hsts ++ [hst1])) st2 ->
      Continuous hst1 hst2 ->
      Forall (STransactional msg_dec) hsts ->
      Forall (fun hst => RqRsLPush hst1 hst \/ RqRsRPush hst2 hst) hsts.
  
  Definition RqRsSys (sys: System) :=
    RqRsContComm sys /\
    RqRsLRPushable sys /\
    RqRsLOrR sys.

End RqRs.

Section RqRsSerial.
  Variables (gtr: GTree)
            (RqRsT: Type)
            (rrdec: RqRsDec RqRsT)
            (rrc: RqRsComm RqRsT)
            (sys: System).

  Hypotheses (Htr: TreeTopoSys gtr sys)
             (Hpb: HalfLockSys (* gtr *) sys)
             (Hrr: RqRsSys rrdec rrc sys).

  Lemma rqrs_well_interleaved_push:
    WellInterleavedPush sys.
  Proof.
    red; intros.
    exists (RqRsLPush rrdec rrc hst1).
    exists (RqRsRPush rrdec rrc hst2).
    pose proof H; destruct H0; clear H1.
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

