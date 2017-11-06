Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics.
Require Import StepDet StepSeq Simulation Predicate Synthesis.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Inductive SVM : Set :=
| GetReq
| GetResp (v: nat)
| SetReq (v: nat)
| SetResp
| InvReq
| InvResp (v: nat).

Definition svm_dec: forall m1 m2: SVM, {m1 = m2} + {m1 <> m2}.
Proof.
  repeat decide equality.
Defined.

Section System.
  Variables extIdx1 extIdx2: nat.

  Definition SvmGetE: IdxT := 0.
  Definition SvmSetE: IdxT := 1.

  Section Spec.

    Definition specIdx := 0.
    Definition specChn1 := 1.
    Definition specChn2 := 2.
    Definition valueIdx := 0.

    Definition getSpecExtIdx (idx: nat) :=
      if eq_nat_dec idx specChn1 then extIdx1 else extIdx2.
    
    Section PerChn.
      Variable chnIdx: nat.

      Definition getReqM := buildMsgId SvmGetE (getSpecExtIdx chnIdx) specIdx chnIdx.
      Definition getRespM := buildMsgId SvmGetE specIdx (getSpecExtIdx chnIdx) chnIdx.
      Definition setReqM := buildMsgId SvmSetE (getSpecExtIdx chnIdx) specIdx chnIdx.
      Definition setRespM := buildMsgId SvmSetE specIdx (getSpecExtIdx chnIdx) chnIdx.

      Definition specGetReq: PMsg :=
        {| pmsg_mid := getReqM;
           pmsg_precond := T;
           pmsg_outs :=
             fun st _ =>
               (ost_st st)@[valueIdx] >>=[nil]
               (fun v => {| msg_id := getRespM; msg_value := v |} :: nil);
           pmsg_postcond :=
             fun pre _ post => pre = post
        |}.

      Definition specSetReq: PMsg :=
        {| pmsg_mid := setReqM;
           pmsg_precond := T;
           pmsg_outs :=
             fun st _ => {| msg_id := setRespM; msg_value := VUnit |} :: nil;
           pmsg_postcond :=
             fun pre v post => (ost_st post)@[valueIdx] = Some v
        |}.

    End PerChn.

    Definition specObj: Object :=
      {| obj_idx := specIdx;
         obj_state_init := [valueIdx <- VNat 0];
         obj_trs :=
           (specGetReq specChn1)
             :: (specSetReq specChn1)
             :: (specGetReq specChn2)
             :: (specSetReq specChn2) :: nil
      |}.
    
    Definition spec : System := singleton specObj.

  End Spec.

  Section Impl0.

    Definition parentIdx := 0.
    Definition child1Idx := 1.
    Definition child2Idx := 2.
    Definition chnImpl := 0.
    Definition chnC2PRq := 1.
    Definition chnC2PRs := 2.
    
    Definition theOtherChild (idx: nat) :=
      if eq_nat_dec idx child1Idx then child2Idx else child1Idx.
    Definition getImplExtIdx (idx: nat) :=
      if eq_nat_dec idx child1Idx then extIdx1 else extIdx2.

    (* Definition valueIdx := 0. *)
    Definition statusIdx := 1.
    
    Definition stM := 2.
    Definition stS := 1.
    Definition stI := 0.

    Section Child0.
      Variable childIdx: nat.

      Definition ecGetReqM := buildMsgId SvmGetE (getImplExtIdx childIdx) childIdx chnImpl.
      Definition ecGetRespM := buildMsgId SvmGetE childIdx (getImplExtIdx childIdx) chnImpl.
      Definition ecSetReqM := buildMsgId SvmSetE (getImplExtIdx childIdx) childIdx chnImpl.
      Definition ecSetRespM := buildMsgId SvmSetE childIdx (getImplExtIdx childIdx) chnImpl.

      Definition ecGetReqOk: PMsg :=
        {| pmsg_mid := ecGetReqM;
           pmsg_precond :=
             fun st => (ost_st st)@[statusIdx] >>=[False] 
                       (fun stt => match stt with
                                   | VNat n => n >= stS
                                   | _ => False
                                   end);
           pmsg_outs :=
             fun st _ =>
               (ost_st st)@[valueIdx] >>=[nil]
               (fun v => {| msg_id := ecGetRespM; msg_value := v |} :: nil);
           pmsg_postcond :=
             fun pre _ post => pre = post
        |}.

      Definition ecSetReqOk: PMsg :=
        {| pmsg_mid := ecSetReqM;
           pmsg_precond :=
             fun st => (ost_st st)@[statusIdx] >>=[False] 
                       (fun stt => match stt with
                                   | VNat n => n = stM
                                   | _ => False
                                   end);
           pmsg_outs :=
             fun st _ => {| msg_id := ecSetRespM; msg_value := VUnit |} :: nil;
           pmsg_postcond :=
             fun pre v post =>
               exists n, v = VNat n /\
                         ost_st post = (ost_st pre) +[ valueIdx <- VNat n] |}.

      Definition child0: Object :=
        {| obj_idx := childIdx;
           obj_state_init := [valueIdx <- VNat 0] +[statusIdx <- VNat stS];
           obj_trs := ecGetReqOk :: ecSetReqOk :: nil
        |}.

    End Child0.

    Section Parent0.

      Definition parent0 : Object :=
        {| obj_idx := parentIdx;
           obj_state_init := [valueIdx <- VNat 0] +[statusIdx <- VNat stS];
           obj_trs := nil
        |}.

    End Parent0.

    Definition impl0 : System :=
      {| sys_objs := parent0 :: (child0 child1Idx) :: (child0 child2Idx) :: nil;
         sys_chns :=
           (buildChannel extIdx1 child1Idx chnImpl)
             :: (buildChannel extIdx2 child2Idx chnImpl)
             :: (buildChannel child1Idx parentIdx chnC2PRq)
             :: (buildChannel child1Idx parentIdx chnC2PRs)
             :: (buildChannel child2Idx parentIdx chnC2PRq)
             :: (buildChannel child2Idx parentIdx chnC2PRs)
             :: (buildChannel parentIdx child1Idx chnImpl)
             :: (buildChannel parentIdx child2Idx chnImpl)
             :: nil
      |}.

  End Impl0.

End System.


Section Sim.
  Variables extIdx1 extIdx2: nat.
  Hypotheses (Hiext1: isExternal (impl0 extIdx1 extIdx2) extIdx1 = true)
             (Hiext2: isExternal (impl0 extIdx1 extIdx2) extIdx2 = true)
             (Hsext1: isExternal (spec extIdx1 extIdx2) extIdx1 = true)
             (Hsext2: isExternal (spec extIdx1 extIdx2) extIdx2 = true).

  Local Notation impl0 := (impl0 extIdx1 extIdx2).
  Local Notation spec := (spec extIdx1 extIdx2).

  Inductive ValidValueImpl: ObjectStates -> Value -> Prop :=
  | VVIS: forall s ost1 ost2 vv,
      s@[child1Idx] = Some ost1 ->
      s@[child2Idx] = Some ost2 ->
      (ost_st ost1)@[statusIdx] = Some (VNat stS) ->
      (ost_st ost2)@[statusIdx] = Some (VNat stS) ->
      (ost_st ost1)@[valueIdx] = Some vv ->
      (ost_st ost2)@[valueIdx] = Some vv ->
      ValidValueImpl s vv
  | VVIM1: forall s ost1 ost2 vv,
      s@[child1Idx] = Some ost1 ->
      s@[child2Idx] = Some ost2 ->
      (ost_st ost1)@[statusIdx] = Some (VNat stM) ->
      (ost_st ost1)@[valueIdx] = Some vv ->
      (ost_st ost2)@[statusIdx] = Some (VNat stI) ->
      ValidValueImpl s vv
  | VVIM2: forall s ost1 ost2 vv,
      s@[child1Idx] = Some ost1 ->
      s@[child2Idx] = Some ost2 ->
      (ost_st ost1)@[statusIdx] = Some (VNat stI) ->
      (ost_st ost2)@[statusIdx] = Some (VNat stM) ->
      (ost_st ost2)@[valueIdx] = Some vv ->
      ValidValueImpl s vv.

  Inductive ValidValueSpec: ObjectStates -> Value -> Prop :=
  | VVS: forall sst sost v,
      sst@[specIdx] = Some sost ->
      (ost_st sost)@[valueIdx] = Some v ->
      ValidValueSpec sst v.

  Inductive SvmStR: ObjectStates -> ObjectStates -> Prop :=
  | SvmStRIntro:
      forall ist sst v,
        (Invertible ValidValueImpl) ist v ->
        (Invertible ValidValueSpec) sst v ->
        SvmStR ist sst.

  Definition SvmR (ist sst: TState) := SvmStR (tst_oss ist) (tst_oss sst).

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

  Theorem impl0_ok: SynthOk spec SvmR svmP impl0.
  Proof.
    repeat split.
    - admit.
    - repeat econstructor.
    - admit.
  Admitted.


  (* Goal (forall (soss1 soss2: ObjectStates) (sost1 sost2: OState) (setV: Value), *)
  (*          soss1@[specIdx] = Some sost1 -> *)
  (*          soss2@[specIdx] = Some sost2 -> *)
  (*          pmsg_postcond (specSetReq extIdx1 extIdx2 child1Idx) sost1 setV sost2 -> *)

  (*          StateSimCond *)
  (*            SvmStR soss1 child1Idx *)
  (*            (fun ost => *)
  (*               (ost_st ost)@[statusIdx] = Some (VNat stS)) -> *)

  (*          StateSimCond *)
  (*            SvmStR soss2 child1Idx *)
  (*            (fun ost => *)
  (*               (ost_st ost)@[statusIdx] = Some (VNat stM)) -> *)

  (*          list PMsg). *)
  (* Proof. *)
  (*   ssp. *)

  (*   collect_vloc. *)
  (*   simpl_postcond. *)
  (*   collect_diff ioss0 ioss. *)
  (* Abort. *)
  
End Sim.

