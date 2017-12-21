Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepDet.
Require Import Predicate Simulation.

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

  Definition svmImplOstRepr (iost: OState) :=
    match (ost_st iost)@[statusIdx] with
    | Some (VNat st) => st
    | _ => 0
    end.

  Definition SvmImplCoord := (nat * nat * nat)%type.

  Definition dist (n1 n2: nat) :=
    if Nat.leb n1 n2 then (n2 - n1) * (n2 - n1) else (n1 - n2) * (n1 - n2).

  Definition svmImplRepDist (c1 c2: SvmImplCoord) :=
    dist (fst (fst c1)) (fst (fst c2)) +
    dist (snd (fst c1)) (snd (fst c2)) +
    dist (snd c1) (snd c2).

  Definition svmImplRepr (ioss: ObjectStates): SvmImplCoord :=
    match ioss@[parentIdx], ioss@[child1Idx], ioss@[child2Idx] with
    | Some ostp, Some ost1, Some ost2 =>
      (svmImplOstRepr ostp, svmImplOstRepr ost1, svmImplOstRepr ost2)
    | _, _, _ => (0, 0, 0) (* never happens *)
    end.

  Definition svmImplDist (ioss1 ioss2: ObjectStates): nat :=
    svmImplRepDist (svmImplRepr ioss1) (svmImplRepr ioss2).

  Inductive SvmR: ObjectStates -> ObjectStates -> Prop :=
  | SvmSSI: forall ioss soss iostp iost1 iost2 sost v,
      ioss@[parentIdx] = Some iostp ->
      (ost_st iostp)@[statusIdx] = Some (VNat stS) ->
      (ost_st iostp)@[valueIdx] = Some v ->

      ioss@[child1Idx] = Some iost1 ->
      (ost_st iost1)@[statusIdx] = Some (VNat stS) ->
      (ost_st iost1)@[valueIdx] = Some v ->

      ioss@[child2Idx] = Some iost2 ->
      (ost_st iost2)@[statusIdx] = Some (VNat stI) ->

      soss@[specIdx] = Some sost ->
      (ost_st sost)@[valueIdx] = Some v ->
      SvmR ioss soss

  | SvmSIS: forall ioss soss iostp iost1 iost2 sost v,
      ioss@[parentIdx] = Some iostp ->
      (ost_st iostp)@[statusIdx] = Some (VNat stS) ->
      (ost_st iostp)@[valueIdx] = Some v ->

      ioss@[child1Idx] = Some iost1 ->
      (ost_st iost1)@[statusIdx] = Some (VNat stI) ->

      ioss@[child2Idx] = Some iost2 ->
      (ost_st iost2)@[statusIdx] = Some (VNat stS) ->
      (ost_st iost2)@[valueIdx] = Some v ->

      soss@[specIdx] = Some sost ->
      (ost_st sost)@[valueIdx] = Some v ->
      SvmR ioss soss

  | SvmSSS: forall ioss soss iostp iost1 iost2 sost v,
      ioss@[parentIdx] = Some iostp ->
      (ost_st iostp)@[statusIdx] = Some (VNat stS) ->
      (ost_st iostp)@[valueIdx] = Some v ->

      ioss@[child1Idx] = Some iost1 ->
      (ost_st iost1)@[statusIdx] = Some (VNat stS) ->
      (ost_st iost1)@[valueIdx] = Some v ->

      ioss@[child2Idx] = Some iost2 ->
      (ost_st iost2)@[statusIdx] = Some (VNat stS) ->
      (ost_st iost2)@[valueIdx] = Some v ->

      soss@[specIdx] = Some sost ->
      (ost_st sost)@[valueIdx] = Some v ->
      SvmR ioss soss

  | SvmMII: forall ioss soss iostp iost1 iost2 sost v,
      ioss@[parentIdx] = Some iostp ->
      (ost_st iostp)@[statusIdx] = Some (VNat stM) ->
      (ost_st iostp)@[valueIdx] = Some v ->
      
      ioss@[child1Idx] = Some iost1 ->
      (ost_st iost1)@[statusIdx] = Some (VNat stI) ->

      ioss@[child2Idx] = Some iost2 ->
      (ost_st iost2)@[statusIdx] = Some (VNat stI) ->

      soss@[specIdx] = Some sost ->
      (ost_st sost)@[valueIdx] = Some v ->
      SvmR ioss soss

  | SvmIMI: forall ioss soss iostp iost1 iost2 sost v,
      ioss@[parentIdx] = Some iostp ->
      (ost_st iostp)@[statusIdx] = Some (VNat stI) ->

      ioss@[child1Idx] = Some iost1 ->
      (ost_st iost1)@[statusIdx] = Some (VNat stM) ->
      (ost_st iost1)@[valueIdx] = Some v ->

      ioss@[child2Idx] = Some iost2 ->
      (ost_st iost2)@[statusIdx] = Some (VNat stI) ->

      soss@[specIdx] = Some sost ->
      (ost_st sost)@[valueIdx] = Some v ->
      SvmR ioss soss

  | SvmIIM: forall ioss soss iostp iost1 iost2 sost v,
      ioss@[parentIdx] = Some iostp ->
      (ost_st iostp)@[statusIdx] = Some (VNat stI) ->

      ioss@[child1Idx] = Some iost1 ->
      (ost_st iost1)@[statusIdx] = Some (VNat stI) ->

      ioss@[child2Idx] = Some iost2 ->
      (ost_st iost2)@[statusIdx] = Some (VNat stM) ->
      (ost_st iost2)@[valueIdx] = Some v ->

      soss@[specIdx] = Some sost ->
      (ost_st sost)@[valueIdx] = Some v ->
      SvmR ioss soss.

  Definition SvmSim (ist sst: TState) := SvmR (tst_oss ist) (tst_oss sst).

  Definition svmIdxF (idx: IdxT): IdxT :=
    if idx ?<n (indicesOf impl0) then specIdx else idx.

  Definition svmMsgIdF (imid: MsgId): MsgId :=
    {| mid_tid := mid_tid imid;
       mid_from := svmIdxF (mid_from imid);
       mid_to := svmIdxF (mid_to imid);
       mid_chn := mid_to imid |}.

  Definition svmMsgF (imsg: Msg): Msg :=
    {| msg_id := svmMsgIdF (msg_id imsg);
       msg_value := msg_value imsg |}.

  Definition svmP := LabelMap svmMsgF.

End Sim.

Lemma SvmR_EquivPreservingR:
  EquivPreservingR SvmR.
Proof.
Admitted.

