Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Semantics StepT.
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
  Definition c1pRq := 2.
  Definition c1pRs := 3.
  Definition pc1 := 4.

  Definition erq2 := 5.
  Definition ers2 := 6.
  Definition c2pRq := 7.
  Definition c2pRs := 8.
  Definition pc2 := 9.

  Definition svm_msg_inds_valid:
    NoDup ([c1pRq; c1pRs; pc1; c2pRq; c2pRs; pc2]
             ++ [erq1; erq2; ers1; ers2]).
  Proof.
    compute; repeat (constructor; firstorder).
  Qed.

  Section Spec.

    Definition specIdx := 0.
    Definition valueIdx := 0.

    Definition SpecOStateIfc: OStateIfc :=
      {| ost_sz := 1;
         ost_ty :=
           fun n =>
             match n with
             | O => nat
             | _ => unit
             end
      |}.
    
    Section PerChn.
      Variables erq ers: nat.

      Definition specGetRq: Rule SpecOStateIfc :=
        {| rule_idx := 0; (* TODO: fix it, it's wrong. *)
           rule_msg_ids := svmGetIdx :: nil;
           rule_minds := erq :: nil;
           rule_precond := ⊤oprec;
           rule_trs :=
             fun (ost: OState SpecOStateIfc) orq mins =>
               (ost, orq,
                (ers, {| msg_id := svmGetIdx;
                         msg_rr := Rq;
                         msg_value := VNat (IList.ith ost Fin.F1) |}) :: nil)
        |}.

      (* Definition specSetRq: Rule := *)
      (*   {| rule_oidx := specIdx; *)
      (*      rule_msg_ids := svmSetIdx :: nil; *)
      (*      rule_minds := erq :: nil; *)
      (*      rule_precond := ⊤oprec; *)
      (*      rule_trs := *)
      (*        fun ost orq mins => *)
      (*          ((hd_error mins) >>=[ost] *)
      (*           (fun idm => ost+[valueIdx <- msg_value (valOf idm)]), *)
      (*           orq, *)
      (*           ((ers, {| msg_id := svmSetIdx; *)
      (*                     msg_rr := Rq; *)
      (*                     msg_value := VUnit |}) *)
      (*              :: nil)) *)
      (*   |}. *)

    End PerChn.

    (* Definition specInit: OStates := *)
    (*   [specIdx <- {| ost_ifc := SpecOStateIfc; *)
    (*                  ost_st := {| IList.prim_fst := 0; *)
    (*                               IList.prim_snd := tt |} |}]. *)

    (* Definition spec: System := *)
    (*   {| sys_oinds := specIdx :: nil; *)
    (*      sys_minds := nil; *)
    (*      sys_merqs := erq1 :: erq2 :: nil; *)
    (*      sys_merss := ers1 :: ers2 :: nil; *)
    (*      sys_msg_inds_valid := NoDup_app_weakening_2 _ _ Hmvalid; *)
    (*      sys_inits := specInit; *)
    (*      sys_rules := *)
    (*        (specGetRq erq1 ers1) *)
    (*          :: (specSetRq erq1 ers1) *)
    (*          :: (specGetRq erq2 ers2) *)
    (*          :: (specSetRq erq2 ers2) :: nil *)
    (*   |}. *)

  End Spec.

  Section Impl.

    Definition parentIdx := 0.
    Definition child1Idx := 1.
    Definition child2Idx := 2.

    (* Already defined above: Definition valueIdx := 0. *)
    Definition statusIdx := 1.
    
    Definition stM := 2.
    Definition stS := 1.
    Definition stI := 0.

    (* Definition implInit: OStates := *)
    (*   [parentIdx <- [valueIdx <- VNat 0] +[statusIdx <- VNat stS]] *)
    (*   +[child1Idx <- [valueIdx <- VNat 0] +[statusIdx <- VNat stS]] *)
    (*   +[child2Idx <- [valueIdx <- VNat 0] +[statusIdx <- VNat stS]]. *)

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

