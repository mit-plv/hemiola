Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Semantics StepT.
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

Definition svmGetIdx: IdxT := 0.
Definition svmSetIdx: IdxT := 1.

Section System.
  Variables erq1 erq2 ers1 ers2: nat.

  Definition c1pRq := 0.
  Definition c1pRs := 1.
  Definition pc1 := 2.
  Definition c2pRq := 3.
  Definition c2pRs := 4.
  Definition pc2 := 5.
  
  Hypothesis (Hmvalid: NoDup ([c1pRq; c1pRs; pc1; c2pRq; c2pRs; pc2]
                                ++ [erq1; erq2; ers1; ers2])).

  Section Spec.

    Definition specIdx := 0.
    Definition valueIdx := 0.
    
    Section PerChn.
      Variables erq ers: nat.

      Definition specGetRq: Rule :=
        {| rule_oidx := specIdx;
           rule_msg_ids := svmGetIdx :: nil;
           rule_minds := erq :: nil;
           rule_precond := ⊤oprec;
           rule_trs :=
             fun ost orq mins =>
               (ost, orq,
                ost@[valueIdx] >>=[nil]
                   (fun v => (ers, {| msg_id := svmGetIdx;
                                      msg_rr := Rq;
                                      msg_value := v |})
                               :: nil))
        |}.

      Definition specSetRq: Rule :=
        {| rule_oidx := specIdx;
           rule_msg_ids := svmSetIdx :: nil;
           rule_minds := erq :: nil;
           rule_precond := ⊤oprec;
           rule_trs :=
             fun ost orq mins =>
               ((hd_error mins) >>=[ost]
                (fun idm => ost+[valueIdx <- msg_value (valOf idm)]),
                orq,
                ((ers, {| msg_id := svmSetIdx;
                          msg_rr := Rq;
                          msg_value := VUnit |})
                   :: nil))
        |}.

    End PerChn.

    Definition specInit: OStates := [specIdx <- [valueIdx <- VNat 0]].

    Definition spec: System :=
      {| sys_oinds := specIdx :: nil;
         sys_minds := nil;
         sys_merqs := erq1 :: erq2 :: nil;
         sys_merss := ers1 :: ers2 :: nil;
         sys_msg_inds_valid := NoDup_app_weakening_2 _ _ Hmvalid;
         sys_inits := specInit;
         sys_rules :=
           (specGetRq erq1 ers1)
             :: (specSetRq erq1 ers1)
             :: (specGetRq erq2 ers2)
             :: (specSetRq erq2 ers2) :: nil
      |}.

  End Spec.

  Section Impl0.

    Definition parentIdx := 0.
    Definition child1Idx := 1.
    Definition child2Idx := 2.

    (* Already defined above: Definition valueIdx := 0. *)
    Definition statusIdx := 1.
    
    Definition stM := 2.
    Definition stS := 1.
    Definition stI := 0.

    Definition implInit: OStates :=
      [parentIdx <- [valueIdx <- VNat 0] +[statusIdx <- VNat stS]]
      +[child1Idx <- [valueIdx <- VNat 0] +[statusIdx <- VNat stS]]
      +[child2Idx <- [valueIdx <- VNat 0] +[statusIdx <- VNat stS]].

    Definition impl0: System :=
      {| sys_oinds := parentIdx :: child1Idx :: child2Idx :: nil;
         sys_minds := c1pRq :: c1pRs :: pc1 :: c2pRq :: c2pRs :: pc2 :: nil;
         sys_merqs := erq1 :: erq2 :: nil;
         sys_merss := ers1 :: ers2 :: nil;
         sys_msg_inds_valid := Hmvalid;
         sys_inits := implInit;
         sys_rules := nil |}.

    Definition implTopo: CTree :=
      {| ctr_tr := Node parentIdx [Node child1Idx nil; Node child2Idx nil];
         ctr_chns :=
           [ {| chn_midx := c1pRq; chn_from := child1Idx; chn_to := parentIdx |};
               {| chn_midx := c1pRs; chn_from := child1Idx; chn_to := parentIdx |};
               {| chn_midx := c2pRq; chn_from := child2Idx; chn_to := parentIdx |};
               {| chn_midx := c2pRs; chn_from := child2Idx; chn_to := parentIdx |};
               {| chn_midx := pc1; chn_from := parentIdx; chn_to := child1Idx |};
               {| chn_midx := pc2; chn_from := parentIdx; chn_to := child2Idx |} ]
      |}.
                                            
    Definition implIndices: list IdxT :=
      ltac:(evalOIndsOf impl0).
    
  End Impl0.

End System.

