Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepDet Serial.
Require Import Synthesis TrsInv TrsSim.

(* Want:
 * 1) [AtomicRules] -> [Atomic] -> [steps_det] -> [CompAtomic].
 * 2) [CompAtomic] is compositional.
 *)

Section HoareTriple.

  Inductive HoareTriple (obj: Object): Precond -> Rule -> Postcond -> Prop :=
  | HTRule:
      forall rule postc,
        In rule (obj_rules obj) ->
        (rule_postcond rule) ~~> postc ->
        HoareTriple obj (rule_precond rule) rule postc
  | HTWeaken:
      forall prec rule postc,
        HoareTriple obj prec rule postc ->
        forall wprec wpostc,
          wprec --> prec ->
          postc ==> wpostc ->
          HoareTriple obj wprec rule wpostc.

  Corollary HTPreWeaken:
    forall obj prec rule postc,
      HoareTriple obj prec rule postc ->
      forall wprec,
        wprec --> prec ->
        HoareTriple obj wprec rule postc.
  Proof.
    intros.
    eapply HTWeaken; eauto.
  Qed.

  Corollary HTPostWeaken:
    forall obj prec rule postc,
      HoareTriple obj prec rule postc ->
      forall wpostc,
        postc ==> wpostc ->
        HoareTriple obj prec rule wpostc.
  Proof.
    intros.
    eapply HTWeaken; eauto.
  Qed.

  Definition GPrecond := TState -> Value -> Prop.
  Definition GPostcond := TState -> list Msg -> Prop.

  Definition liftPre (oidx: IdxT) (pre: Precond): GPrecond :=
    fun prest val =>
      (tst_oss prest)@[oidx] >>=[True] (* [True] or [False]? *)
      (fun preost => pre preost val).

  Definition liftPost (oidx: IdxT) (post: Postcond): GPostcond :=
    fun postst outs =>
      (tst_oss postst)@[oidx] >>=[True]
      (fun postost => post postost outs).

  
  
End HoareTriple.

Section AtomicRules.
  
  Variable (tid: IdxT).

  (* Inductive AtomicRules: MsgId -> System -> Prop := *)
  (* | ARImm: *)
  (*     forall oidx oinit immr, *)
  (*       ImmRule oidx immr -> *)
  (*       AtomicRules (rule_mid immr) *)
  (*                   [{| obj_idx := oidx; *)
  (*                       obj_state_init := oinit; *)
  (*                       obj_rules := immr :: nil |}] *)
  (* | ARRqRs: *)
  (*     forall oidx oinit fwds rqr rsb syss, *)
  (*       RqRsRules tid oidx fwds rqr rsb -> *)
  (*       Forall (fun systo => AtomicRules (buildMsgId tid oidx (snd systo) rqChn) *)
  (*                                        (fst systo)) *)
  (*              (combine syss fwds) -> *)
  (*       AtomicRules (rule_mid rqr) *)
  (*                   ({| obj_idx := oidx; *)
  (*                       obj_state_init := oinit; *)
  (*                       obj_rules := rqr :: rsb |} *)
  (*                      :: concat syss). *)

End AtomicRules.

Section CompAtomic.
  
  (* Here are necessary requirements of [CompAtomic], moved from [Serial]:
   * 1) No external output messages are generated until the transaction ends.
   * 2) When the transaction ends, it outputs a single external message, which
   *    is the response of the original request.
   * 3) When the transaction ends, no internal messages about the transaction 
   *    are left. We ensure it by just tracking the internal messages about
   *)

  (* Inductive CompAtomic: *)
  (*   System -> *)
  (*   Inv (* precondition *) -> *)
  (*   TInfo -> *)
  (*   History -> *)
  (*   MessagePool TMsg -> *)
  (*   Inv (* postcondition *) -> *)
  (*   option TMsg -> Prop := *)
  (* | CAtomicImm: *)
  (*     forall sys tid rqin rsout prec postc, *)
  (*       Atomic sys (buildTInfo tid rqin) *)
  (*              (IlblOuts (Some (toTMsgU rqin)) (rsout :: nil) :: nil) *)
  (*              (rsout :: nil) -> *)
  (*       isExternal sys (mid_from (msg_id (tmsg_msg rsout))) = true -> *)
  (*       CompAtomic sys prec (buildTInfo tid rqin) *)
  (*                  (IlblOuts (Some (toTMsgU rqin)) (rsout :: nil) :: nil) *)
  (*                  nil postc (Some rsout) *)

End CompAtomic.

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
    forall ti hst mouts,
      Atomic ssys ti hst mouts ->
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
    forall ti hst mouts,
      Atomic sys ti hst mouts ->
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

