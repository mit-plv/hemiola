Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics.
Require Import StepDet StepSeq Predicate Simulation.

Require Import SingleValue.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section Sim.
  Variables extIdx1 extIdx2: nat.
  Hypotheses (Hiext1: isExternal (impl0 extIdx1 extIdx2) extIdx1 = true)
             (Hiext2: isExternal (impl0 extIdx1 extIdx2) extIdx2 = true)
             (Hsext1: isExternal (spec extIdx1 extIdx2) extIdx1 = true)
             (Hsext2: isExternal (spec extIdx1 extIdx2) extIdx2 = true).

  Local Notation impl0 := (impl0 extIdx1 extIdx2).
  Local Notation spec := (spec extIdx1 extIdx2).

  Definition svmImplChild1Inv: list (OState -> Prop) :=
    (fun iost1 => (ost_st iost1)@[statusIdx] = Some (VNat stI))
      :: (fun iost1 => (ost_st iost1)@[statusIdx] = Some (VNat stS)) 
      :: (fun iost1 => (ost_st iost1)@[statusIdx] = Some (VNat stM))
      :: nil.

  Definition svmImplChild2Inv: list (OState -> Prop) :=
    (fun iost1 => (ost_st iost1)@[statusIdx] = Some (VNat stI))
      :: (fun iost1 => (ost_st iost1)@[statusIdx] = Some (VNat stS)) 
      :: (fun iost1 => (ost_st iost1)@[statusIdx] = Some (VNat stM))
      :: nil.

  Definition svmImplInv: list (ObjectStates -> Prop) :=
    (fun ioss =>
       exists iost1 iost2,
         ioss@[child1Idx] = Some iost1 /\
         (ost_st iost1)@[statusIdx] = Some (VNat stS) /\
         ioss@[child2Idx] = Some iost2 /\
         (ost_st iost2)@[statusIdx] = Some (VNat stS))
      :: (fun ioss =>
            exists iost1 iost2,
              ioss@[child1Idx] = Some iost1 /\
              (ost_st iost1)@[statusIdx] = Some (VNat stM) /\
              ioss@[child2Idx] = Some iost2 /\
              (ost_st iost2)@[statusIdx] = Some (VNat stI))
      :: (fun ioss =>
            exists iost1 iost2,
              ioss@[child1Idx] = Some iost1 /\
              (ost_st iost1)@[statusIdx] = Some (VNat stI) /\
              ioss@[child2Idx] = Some iost2 /\
              (ost_st iost2)@[statusIdx] = Some (VNat stM))
      :: nil.

  Definition svmR: list (ObjectStates -> ObjectStates -> Prop) :=
    (fun ioss soss =>
       exists iost1 iost2 sost v,
         ioss@[child1Idx] = Some iost1 /\
         (ost_st iost1)@[statusIdx] = Some (VNat stS) /\
         (ost_st iost1)@[valueIdx] = Some v /\
         ioss@[child2Idx] = Some iost2 /\
         (ost_st iost2)@[statusIdx] = Some (VNat stS) /\
         (ost_st iost2)@[valueIdx] = Some v /\
         soss@[specIdx] = Some sost /\
         (ost_st sost)@[valueIdx] = Some v)
      :: (fun ioss soss =>
            exists iost1 iost2 sost v,
              ioss@[child1Idx] = Some iost1 /\
              (ost_st iost1)@[statusIdx] = Some (VNat stM) /\
              (ost_st iost1)@[valueIdx] = Some v /\
              ioss@[child2Idx] = Some iost2 /\
              (ost_st iost2)@[statusIdx] = Some (VNat stI) /\
              soss@[specIdx] = Some sost /\
              (ost_st sost)@[valueIdx] = Some v)
      :: (fun ioss soss =>
            exists iost1 iost2 sost v,
              ioss@[child1Idx] = Some iost1 /\
              (ost_st iost1)@[statusIdx] = Some (VNat stI) /\
              ioss@[child2Idx] = Some iost2 /\
              (ost_st iost2)@[statusIdx] = Some (VNat stM) /\
              (ost_st iost2)@[valueIdx] = Some v /\
              soss@[specIdx] = Some sost /\
              (ost_st sost)@[valueIdx] = Some v)
      :: nil.

  Inductive SvmR: ObjectStates -> ObjectStates -> Prop :=
  | SvmSS: forall ioss soss iost1 iost2 sost v,
      ioss@[child1Idx] = Some iost1 ->
      (ost_st iost1)@[statusIdx] = Some (VNat stS) ->
      (ost_st iost1)@[valueIdx] = Some v ->
      ioss@[child2Idx] = Some iost2 ->
      (ost_st iost2)@[statusIdx] = Some (VNat stS) ->
      (ost_st iost2)@[valueIdx] = Some v ->
      soss@[specIdx] = Some sost ->
      (ost_st sost)@[valueIdx] = Some v ->
      SvmR ioss soss
  | SvmIM1: forall ioss soss iost1 iost2 sost v,
      ioss@[child1Idx] = Some iost1 ->
      (ost_st iost1)@[statusIdx] = Some (VNat stM) ->
      (ost_st iost1)@[valueIdx] = Some v ->
      ioss@[child2Idx] = Some iost2 ->
      (ost_st iost2)@[statusIdx] = Some (VNat stI) ->
      soss@[specIdx] = Some sost ->
      (ost_st sost)@[valueIdx] = Some v ->
      SvmR ioss soss
  | SvmIM2: forall ioss soss iost1 iost2 sost v,
      ioss@[child1Idx] = Some iost1 ->
      (ost_st iost1)@[statusIdx] = Some (VNat stI) ->
      ioss@[child2Idx] = Some iost2 ->
      (ost_st iost2)@[statusIdx] = Some (VNat stM) ->
      (ost_st iost2)@[valueIdx] = Some v ->
      soss@[specIdx] = Some sost ->
      (ost_st sost)@[valueIdx] = Some v ->
      SvmR ioss soss.

  Lemma svmR_svmR:
    forall ioss soss,
      SvmR ioss soss ->
      exists n, nth n svmR (fun _ _ => False) ioss soss.
  Proof.
    intros; inv H.
    - exists 0; cbn.
      repeat eexists; eauto.
    - exists 1; cbn.
      repeat eexists; eauto.
    - exists 2; cbn.
      repeat eexists; eauto.
  Qed.      

  Definition SvmSim (ist sst: TState) := SvmR (tst_oss ist) (tst_oss sst).

  Definition svmIdxF (idx: IdxT): IdxT :=
    if idx ?<n (indicesOf impl0) then specIdx else idx.

  Definition svmMsgIdF (imid: MsgId): MsgId :=
    {| mid_type := mid_type imid;
       mid_from := svmIdxF (mid_from imid);
       mid_to := svmIdxF (mid_to imid);
       mid_chn := mid_to imid |}.

  Definition svmMsgF (imsg: Msg): Msg :=
    {| msg_id := svmMsgIdF (msg_id imsg);
       msg_value := msg_value imsg |}.

  Definition svmMsgsF (imsgs: list Msg): list Msg :=
    map svmMsgF imsgs.

  Definition svmP (l: Label) :=
    match l with
    | Lbl min mouts => Lbl min (svmMsgsF mouts)
    end.
  
End Sim.

