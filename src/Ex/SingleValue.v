Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport Syntax Semantics StepT.
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

  Definition erq1 := 0.
  Definition ers1 := 1.
  Definition erq2 := 2.
  Definition ers2 := 3.

  Section Spec.

    Definition specIdx := 0.

    Definition SpecOStateIfc: OStateIfc :=
      {| ost_sz := 1;
         ost_ty := [nat:Type]%vector |}.
    Definition specValueIdx: Fin.t 1 := Fin.F1.
    
    Section PerChn.
      Variables erq ers: nat.

      Definition specGetRq: Rule SpecOStateIfc :=
        {| rule_idx := erq + 0;
           rule_msg_ids := [svmGetIdx];
           rule_minds := [erq];
           rule_precond := ⊤oprec;
           rule_trs :=
             fun (ost: OState SpecOStateIfc) orq mins =>
               (ost, orq,
                (ers, {| msg_id := svmGetIdx;
                         msg_rr := Rq;
                         msg_value := VNat (hvec_ith ost specValueIdx) |}) :: nil)
        |}.

      Definition specSetRq: Rule SpecOStateIfc :=
        {| rule_idx := erq + 1;
           rule_msg_ids := [svmSetIdx];
           rule_minds := [erq];
           rule_precond := ⊤oprec;
           rule_trs :=
             fun (ost: OState SpecOStateIfc) orq mins =>
               ((hd_error mins) >>=[ost]
                  (fun idm =>
                     match msg_value (valOf idm) with
                     | VNat n => hvec_upd ost specValueIdx n
                     | _ => ost
                     end),
                orq,
                ((ers, {| msg_id := svmSetIdx;
                          msg_rr := Rq;
                          msg_value := VUnit |})
                   :: nil))
        |}.

    End PerChn.

    Definition specInit: OStates :=
      [specIdx <- {| ost_ifc := SpecOStateIfc;
                     ost_st := hvcons 0 hvnil (* (0, tt) *) |}].

    Definition specObj: Object :=
      {| obj_idx := specIdx;
         obj_ifc := SpecOStateIfc;
         obj_rules := 
           (specGetRq erq1 ers1)
             :: (specSetRq erq1 ers1)
             :: (specGetRq erq2 ers2)
             :: (specSetRq erq2 ers2) :: nil;
         obj_rules_valid := ltac:(inds_valid_tac)
      |}.
    
    Definition spec: System :=
      {| sys_objs := [specObj];
         sys_oinds_valid := ltac:(inds_valid_tac);
         sys_minds := nil;
         sys_merqs := [erq1; erq2];
         sys_merss := [ers1; ers2];
         sys_msg_inds_valid := ltac:(inds_valid_tac);
         sys_oss_inits := specInit;
         sys_orqs_inits := []
      |}.

  End Spec.

  Section Impl.

    Definition c1pRq := 4.
    Definition c1pRs := 5.
    Definition pc1 := 6.
    Definition c2pRq := 7.
    Definition c2pRs := 8.
    Definition pc2 := 9.

    Definition parentIdx := 0.
    Definition child1Idx := 1.
    Definition child2Idx := 2.

    Definition implValueIdx: Fin.t 2 := Fin.F1.
    Definition implStatusIdx: Fin.t 2 := Fin.FS Fin.F1.
    
    Definition stM := 2.
    Definition stS := 1.
    Definition stI := 0.

    Definition ImplOStateIfc: OStateIfc :=
      {| ost_sz := 2;
         ost_ty := [nat:Type; nat:Type]%vector |}.
    Definition implInit: OStates :=
      [parentIdx <- {| ost_ifc := ImplOStateIfc;
                       ost_st := (0, (stS, tt)) |}]
      +[child1Idx <- {| ost_ifc := ImplOStateIfc;
                        ost_st := (0, (stS, tt)) |}]
      +[child2Idx <- {| ost_ifc := ImplOStateIfc;
                        ost_st := (0, (stS, tt)) |}].

    Section PerChild.
      Variables (erq ers: nat) (oidx: IdxT).

      (* Definition implGetImm: Rule := *)
      (*   {| rule_oidx := oidx; *)
      (*      rule_msg_ids := svmGetIdx :: nil; *)
      (*      rule_minds := erq :: nil; *)
      (*      rule_precond := *)
      (*        fun ost orq mins => *)
      (*          ost@[statusIdx] >=[False] (fun st => st >= stS); *)
      (*      rule_trs := *)
      (*        fun ost orq mins => *)
      (*          (ost, orq, *)
    
      (* Definition implGetRqUp: Rule := *)
      (*   {| rule_oidx := oidx; *)
      (*      rule_msg_ids := svmGetIdx :: nil; *)
      (*      rule_minds := erq :: nil; *)
      (*      rule_precond := *)
      (*        fun ost orq mins => True; *)
      (*      rule_trs := *)
      (*        fun ost orq mins => *)
      (*          (ost, orq, *)
      (*           ost@[valueIdx] >>=[nil] *)
      (*              (fun v => (ers, {| msg_id := svmGetIdx; *)
      (*                                 msg_rr := Rq; *)
      (*                                 msg_value := v |}) *)
      (*                          :: nil)) *)
      (*   |}. *)

    End PerChild.
    
    (* Definition impl0: System := *)
    (*   {| sys_oinds := parentIdx :: child1Idx :: child2Idx :: nil; *)
    (*      sys_minds := c1pRq :: c1pRs :: pc1 :: c2pRq :: c2pRs :: pc2 :: nil; *)
    (*      sys_merqs := erq1 :: erq2 :: nil; *)
    (*      sys_merss := ers1 :: ers2 :: nil; *)
    (*      sys_msg_inds_valid := Hmvalid; *)
    (*      sys_inits := implInit; *)
    (*      sys_rules := nil |}. *)

    (* Definition implTopo: GTree := *)
    (*   Node parentIdx *)
    (*        [([createEdge child1Idx c1pRq parentIdx; *)
    (*             createEdge child1Idx c1pRs parentIdx; *)
    (*             createEdge parentIdx pc1 child1Idx], *)
    (*          Node child1Idx nil); *)
    (*           ([createEdge child2Idx parentIdx c2pRq; *)
    (*               createEdge child2Idx parentIdx c2pRs; *)
    (*               createEdge parentIdx child2Idx pc2], *)
    (*            Node child2Idx nil)]. *)
                                            
    (* Definition implIndices: list IdxT := *)
    (*   ltac:(evalOIndsOf impl0). *)
    
  End Impl.

End System.

Close Scope list.
Close Scope fmap.

