Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepDet.
Require Import Synthesis.

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

      Definition specGetReq: Rule :=
        {| rule_mids := getReqM :: nil;
           rule_precond := ⊤;
           rule_postcond :=
             rpostOf ⊤⊤= (fun pre _ =>
                            pre@[valueIdx] >>=[nil]
                            (fun v => {| msg_id := getRespM; msg_value := v |} :: nil));
        |}.

      Definition specSetReq: Rule :=
        {| rule_mids := setReqM :: nil;
           rule_precond := ⊤;
           rule_postcond :=
             rpostOf (SingleRqPostcondSt
                        (fun pre v post => post@[valueIdx] = Some v))
                     (fun _ _ => {| msg_id := setRespM; msg_value := VUnit |} :: nil)
        |}.

    End PerChn.

    Definition spec: System :=
      {| sys_inds := specIdx :: nil;
         sys_inits := [specIdx <- [valueIdx <- VNat 0]];
         sys_rules :=
           (specGetReq specChn1)
             :: (specSetReq specChn1)
             :: (specGetReq specChn2)
             :: (specSetReq specChn2) :: nil
      |}.

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

    Definition impl0: System :=
      {| sys_inds := parentIdx :: child1Idx :: child2Idx :: nil;
         sys_inits := [parentIdx <- [valueIdx <- VNat 0] +[statusIdx <- VNat stS]]
                      +[child1Idx <- [valueIdx <- VNat 0] +[statusIdx <- VNat stS]]
                      +[child2Idx <- [valueIdx <- VNat 0] +[statusIdx <- VNat stS]];
         sys_rules := nil |}.

  End Impl0.

End System.

