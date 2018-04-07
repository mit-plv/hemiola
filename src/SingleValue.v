Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepT.
Require Import Synthesis.
Require Import Topology.

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

    Definition specRqChn (chnIdx: nat) := rqChn + numChns * chnIdx.
    Definition specRsChn (chnIdx: nat) := rsChn + numChns * chnIdx.
    Definition chnIdx0 := 0.
    Definition chnIdx1 := 1.
    
    Definition valueIdx := 0.

    Definition getChnIdx (eidx: nat) :=
      if eq_nat_dec eidx extIdx1 then chnIdx0 else chnIdx1.
    
    Section PerChn.
      Variable eidx: nat.

      Definition getReqM := buildMsgId SvmGetE eidx specIdx (specRqChn (getChnIdx eidx)).
      Definition getRespM := buildMsgId SvmGetE specIdx eidx (specRsChn (getChnIdx eidx)).
      Definition setReqM := buildMsgId SvmSetE eidx specIdx (specRqChn (getChnIdx eidx)).
      Definition setRespM := buildMsgId SvmSetE specIdx eidx (specRsChn (getChnIdx eidx)).

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
           (specGetReq extIdx1)
             :: (specSetReq extIdx1)
             :: (specGetReq extIdx2)
             :: (specSetReq extIdx2) :: nil
      |}.

  End Spec.

  Section Impl0.

    Definition parentIdx := 0.
    Definition child1Idx := 1.
    Definition child2Idx := 2.

    Definition valid_child1Idx: child1Idx = chnIdx0 + 1 := eq_refl.
    Definition valid_child2Idx: child2Idx = chnIdx1 + 1 := eq_refl.
    
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

    Definition implTopo: Tree unit :=
      Node parentIdx tt
           [Node child1Idx tt nil; Node child2Idx tt nil].

    Definition implIndices: list IdxT :=
      ltac:(evalIndicesOf impl0).
    
  End Impl0.

End System.

