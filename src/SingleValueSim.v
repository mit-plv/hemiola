Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepDet.
Require Import Simulation Synthesis.

Require Import SingleValue.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section Inv.

  Definition SvmInv (ist: TState) :=
    (exists post pstt pv,
        (tst_oss ist)@[parentIdx] = Some post /\
        post@[statusIdx] = Some (VNat pstt) /\
        (pstt = stI \/ pstt = stS \/ pstt = stM) /\
        post@[valueIdx] = Some pv) /\
    (exists c1ost c1stt c1v,
        (tst_oss ist)@[child1Idx] = Some c1ost /\
        c1ost@[statusIdx] = Some (VNat c1stt) /\
        (c1stt = stI \/ c1stt = stS \/ c1stt = stM) /\
        c1ost@[valueIdx] = Some c1v) /\
    (exists c2ost c2stt c2v,
        (tst_oss ist)@[child2Idx] = Some c2ost /\
        c2ost@[statusIdx] = Some (VNat c2stt) /\
        (c2stt = stI \/ c2stt = stS \/ c2stt = stM) /\
        c2ost@[valueIdx] = Some c2v).

End Inv.

Section Sim.
  Variables extIdx1 extIdx2: nat.
  Hypotheses (Hiext1: isExternal impl0 extIdx1 = true)
             (Hiext2: isExternal impl0 extIdx2 = true)
             (Hsext1: isExternal (spec extIdx1 extIdx2) extIdx1 = true)
             (Hsext2: isExternal (spec extIdx1 extIdx2) extIdx2 = true).

  Local Notation spec := (spec extIdx1 extIdx2).

  (** Label mapping *)
  
  Definition svmIdxF (idx: IdxT): IdxT :=
    if idx ?<n (indicesOf impl0) then specIdx else idx.

  Definition svmMsgIdF (imid: MsgId): MsgId :=
    {| mid_addr := {| ma_from := svmIdxF (mid_from imid);
                      ma_to := svmIdxF (mid_to imid);
                      ma_chn := mid_to imid |};
       mid_tid := mid_tid imid |}.

  Definition svmMsgF (imsg: Msg): Msg :=
    {| msg_id := svmMsgIdF (msg_id imsg);
       msg_value := msg_value imsg |}.

  Definition svmP := LabelMap svmMsgF.

  (** Simulation between [TState]s *)

  Definition ImplStatusMI (ioss: ObjectStates OrdOState) (v: Value) :=
    exists midx most v,
      ioss@[midx] = Some most /\
      most@[statusIdx] = Some (VNat stM) /\
      most@[valueIdx] = Some v /\
      (forall oidx ost stt,
          oidx <> midx ->
          ioss@[oidx] = Some ost ->
          ost@[statusIdx] = Some (VNat stt) ->
          stt = stI).

  Definition ImplStatusSI (ioss: ObjectStates OrdOState) (v: Value) :=
    forall oidx ost stt,
      ioss@[oidx] = Some ost ->
      ost@[statusIdx] = Some (VNat stt) ->
      match stt with
      | 0 (* stI *) => True
      | 1 (* stS *) => ost@[valueIdx] = Some v
      | 2 (* stM *) => False
      | _ => False
      end.

  Definition SpecState (soss: ObjectStates OrdOState) (v: Value) :=
    exists sost,
      soss@[specIdx] = Some sost /\
      sost@[valueIdx] = Some v.

  Inductive SvmR: ObjectStates OrdOState -> ObjectStates OrdOState -> Prop :=
  | SvmMI:
      forall ioss soss v,
        ImplStatusMI ioss v ->
        SpecState soss v ->
        SvmR ioss soss
  | SvmSI:
      forall ioss soss v,
        ImplStatusSI ioss v ->
        SpecState soss v ->
        SvmR ioss soss.

  Definition SvmSim (ist sst: TState) :=
    SvmR (tst_oss ist) (tst_oss sst) /\
    SimMP svmMsgF (tst_msgs ist) (tst_msgs sst).

End Sim.

