Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepDet Serial.
Require Import TrsSim.

Definition StateTCond := StateT -> Prop.
Definition TrsHelperCond := TrsHelper -> Prop.

Definition OstCond := (StateTCond * TrsHelperCond)%type.
Definition OssCond := M.t OstCond.
Definition MsgValCond := Value -> ObjectStates -> Prop.
Definition StepCond := (OssCond * MsgValCond)%type.

Definition stepCondTop: StepCond := (M.empty _, fun _ _ => True).

Definition updateOstCond (oidx: IdxT) (ostc: OstCond) (stc: StepCond): StepCond :=
  ((fst stc)+[oidx <- ostc], snd stc).

Definition OstCondHolds (ostc: OstCond) (ost: OState) :=
  (fst ostc) (ost_st ost) /\ (snd ostc) (ost_tst ost).
  
Definition OssCondHolds (ossc: OssCond) (oss: ObjectStates) :=
  (forall oidx,
      match ossc@[oidx] with
      | Some ostc => oss@[oidx] >>=[False] (fun ost => OstCondHolds ostc ost)
      | None => True
      end).

Definition MsgValCondHolds (mvc: MsgValCond) (mval: Value) (oss: ObjectStates) :=
  mvc mval oss.

Definition StepCondHolds (stc: StepCond) (mval: Value) (oss: ObjectStates) :=
  OssCondHolds (fst stc) oss /\ MsgValCondHolds (snd stc) mval oss.

Section AtomicSteps.

  Variables (trsIdx: IdxT)
            (rqImpl rqSpec: Msg).

  Variable (spec: System) (sobj: Object) (spmsg: PMsg)
           (Hsobj: sys_objs spec = sobj :: nil)
           (HspmsgIn: In spmsg (obj_trs sobj))
           (Hspmsg: pmsg_mid spmsg = msg_id rqSpec).

  Variables (impl: System)
            (R: ObjectStates -> ObjectStates -> Prop)
            (p: Label -> Label)
            (HrqP: p (LblIn rqImpl) = LblIn rqSpec).
  
  Local Infix "≈" := R (at level 30).

  Inductive AtomicSteps:
    StepCond (* impl precondition *) ->
    ObjectStates (* impl state *) ->
    ObjectStates (* spec state *) ->
    list Msg (* output messages *) -> Prop :=
  | AstNil: forall stc ioss soss, AtomicSteps stc ioss soss nil
  | AstSpecSilent:
      forall pre pioss soss msg curs1 curs2 curs,
        R pioss soss ->
        curs = curs1 ++ msg :: curs2 ->

        (forall pmsg obj ostc stc piost niost nioss,
            msg_id msg = pmsg_mid pmsg ->
            In pmsg (obj_trs obj) ->
            In obj (sys_objs impl) ->
            StepCondHolds stc (msg_value msg) pioss ->
            pioss@[obj_idx obj] = Some piost ->
            (OstCondHolds ostc niost ->
             pmsg_postcond pmsg niost (msg_value msg) niost) ->
            nioss = pioss +[obj_idx obj <- niost] ->
            R nioss soss /\
            AtomicSteps (updateOstCond (obj_idx obj) ostc stc)
                        nioss soss
                        (curs ++ pmsg_outs pmsg piost (msg_value msg))) ->

        AtomicSteps pre pioss soss curs.
  (* TODO: | AstSpecStep: ... *)

  Definition CompleteAtomicSteps (ioss soss: ObjectStates) (rqin: Msg) :=
    AtomicSteps stepCondTop ioss soss (rqin :: nil).

  Theorem atomicSteps_trsSimStepAtomic:
    forall ioss soss,
      AtomicSteps stepCondTop ioss soss (rqImpl :: nil) ->
      ioss ≈ soss ->
      forall ist1 sst1,
        tst_oss ist1 = ioss ->
        tst_oss sst1 = soss ->
        forall ihst ist2 mouts,
          steps_det impl ist1 ihst ist2 ->
          Atomic impl trsIdx (toTMsgU rqImpl) ihst mouts ->
          exists sst2 shst,
            steps_det spec sst1 shst sst2 /\
            map p (behaviorOf impl ihst) = behaviorOf spec shst /\
            tst_oss ist2 ≈ tst_oss sst2.
  Proof.
  Admitted.

End AtomicSteps.

