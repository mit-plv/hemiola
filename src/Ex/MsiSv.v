Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport Syntax Semantics StepT.
Require Import Topology RqRs.

Require Import Msi.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

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
      Variable ridxOfs: nat.
      Variables (erq ers: nat).

      Definition specNumOfRules := 3.
      
      Definition specGetRq: Rule SpecOStateIfc :=
        {| rule_idx := specNumOfRules * ridxOfs + 0;
           rule_msg_ids := [msiGetRq];
           rule_msgs_from := fun _ => [erq];
           rule_precond := ⊤oprec;
           rule_trs :=
             fun (ost: OState SpecOStateIfc) orq mins =>
               (ost, orq,
                [(ers, {| msg_id := msiGetRs;
                          msg_value := VNat (ost#[specValueIdx])
                       |})])
        |}.

      Definition specSetRq: Rule SpecOStateIfc :=
        {| rule_idx := specNumOfRules * ridxOfs + 1;
           rule_msg_ids := [msiSetRq];
           rule_msgs_from := fun _ => [erq];
           rule_precond := ⊤oprec;
           rule_trs :=
             fun (ost: OState SpecOStateIfc) orq mins =>
               ((hd_error mins) >>=[ost]
                  (fun idm =>
                     match msg_value (valOf idm) with
                     | VNat n => ost+#[specValueIdx <- n]
                     | _ => ost
                     end),
                orq,
                [(ers, {| msg_id := msiSetRs;
                          msg_value := VUnit |})])
        |}.

      Definition specEvictRq: Rule SpecOStateIfc :=
        {| rule_idx := specNumOfRules * ridxOfs + 2;
           rule_msg_ids := [msiEvictRq];
           rule_msgs_from := fun _ => [erq];
           rule_precond := ⊤oprec;
           rule_trs :=
             fun (ost: OState SpecOStateIfc) orq mins =>
               (ost, orq,
                [(ers, {| msg_id := msiEvictRs;
                          msg_value := VUnit |})])
        |}.
      
    End PerChn.

    Definition specInit: OStates :=
      [specIdx <- {| ost_ifc := SpecOStateIfc;
                     ost_st := hvcons 0 hvnil (* (0, tt) *) |}].

    Definition specObj: Object :=
      {| obj_idx := specIdx;
         obj_ifc := SpecOStateIfc;
         obj_rules := 
           [specGetRq 0 erq1 ers1;
              specSetRq 0 erq1 ers1;
              specEvictRq 0 erq1 ers1;
              specGetRq 1 erq2 ers2;
              specSetRq 1 erq2 ers2;
              specEvictRq 1 erq2 ers2];
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

    Definition ec1 := 4.
    Definition ce1 := 5.
    Definition ec2 := 6.
    Definition ce2 := 7.
    Definition c1pRq := 8.
    Definition c1pRs := 9.
    Definition pc1 := 10.
    Definition c2pRq := 11.
    Definition c2pRs := 12.
    Definition pc2 := 13.
    
    Definition parentIdx := 0.
    Definition child1Idx := 1.
    Definition child2Idx := 2.

    Definition implValueIdx: Fin.t 2 := Fin.F1.
    Definition implStatusIdx: Fin.t 2 := Fin.FS Fin.F1.
    
    Definition ImplOStateIfc: OStateIfc :=
      {| ost_sz := 2;
         ost_ty := [nat:Type; nat:Type]%vector |}.
    Definition implInit: OStates :=
      [parentIdx <- {| ost_ifc := ImplOStateIfc;
                       ost_st := (0, (msiS, tt)) |}]
      +[child1Idx <- {| ost_ifc := ImplOStateIfc;
                        ost_st := (0, (msiS, tt)) |}]
      +[child2Idx <- {| ost_ifc := ImplOStateIfc;
                        ost_st := (0, (msiS, tt)) |}].

    Section Child.
      Variable (coidx: IdxT).
      Variables (ec ce cpRq cpRs pc: IdxT).

      Definition childGetRqImm: Rule ImplOStateIfc :=
        {| rule_idx := 0;
           rule_msg_ids := [msiGetRq];
           rule_msgs_from := fun _ => [ec];
           rule_precond :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               LockFree orq O /\ ost#[implStatusIdx] >= msiS;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               (ost, orq,
                [(ce, {| msg_id := msiGetRs;
                         msg_value := VNat (ost#[implValueIdx])
                      |})])
        |}.

      Definition childGetRqS: Rule ImplOStateIfc :=
        {| rule_idx := 1;
           rule_msg_ids := [msiGetRq];
           rule_msgs_from := fun _ => [ec];
           rule_precond :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               LockFree orq O /\ ost#[implStatusIdx] = msiI;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               ((hd_error mins) >>=[(ost, orq, nil)]
                  (fun idm =>
                     (ost,
                      addRq orq O upRq (valOf idm) [pc] ce,
                      [(cpRq, {| msg_id := msiRqS;
                                 msg_value := VUnit |})])))
        |}.

      Definition childGetRsS: Rule ImplOStateIfc :=
        {| rule_idx := 2;
           rule_msg_ids := [msiRsS];
           rule_msgs_from := fun _ => [pc];
           rule_precond := ⊤oprec;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               ((hd_error mins) >>=[(ost, orq, nil)]
                  (fun idm =>
                     match msg_value (valOf idm) with
                     | VNat n =>
                       (ost +#[implValueIdx <- n] +#[implStatusIdx <- msiS],
                        removeRq orq O upRq,
                        [(ce, {| msg_id := msiGetRs;
                                 msg_value := VNat n |})])
                     | _ => (ost, orq, nil) (** TODO: how to efficiently handle this case? *)
                     end))
        |}.

      Definition childDownRqS: Rule ImplOStateIfc :=
        {| rule_idx := 3;
           rule_msg_ids := [msiDownRqS];
           rule_msgs_from := fun _ => [pc];
           rule_precond :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               HalfLockFree orq O;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               (ost+#[implStatusIdx <- msiS],
                orq,
                [(cpRs, {| msg_id := msiDownRsS;
                           msg_value := VUnit |})])
        |}.

      Definition childSetRqImm: Rule ImplOStateIfc :=
        {| rule_idx := 4;
           rule_msg_ids := [msiSetRq];
           rule_msgs_from := fun _ => [ec];
           rule_precond :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               LockFree orq O /\ ost#[implStatusIdx] = msiM;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               ((hd_error mins) >>=[(ost, orq, nil)]
                  (fun idm =>
                     match msg_value (valOf idm) with
                     | VNat n =>
                       (ost +#[implValueIdx <- n] +#[implStatusIdx <- msiM],
                        orq,
                        [(ce, {| msg_id := msiSetRs;
                                 msg_value := VUnit |})])
                     | _ => (ost, orq, nil)
                     end))
        |}.
    
      Definition childSetRqM: Rule ImplOStateIfc :=
        {| rule_idx := 5;
           rule_msg_ids := [msiSetRq];
           rule_msgs_from := fun _ => [ec];
           rule_precond :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               LockFree orq O /\ ost#[implStatusIdx] <> msiM;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               ((hd_error mins) >>=[(ost, orq, nil)]
                  (fun idm =>
                     (ost,
                      addRq orq O upRq (valOf idm) [pc] ce,
                      [(cpRq, {| msg_id := msiRqM;
                                 msg_value := VUnit |})])))
        |}.

      Definition childSetRsM: Rule ImplOStateIfc :=
        {| rule_idx := 6;
           rule_msg_ids := [msiRsM];
           rule_msgs_from := fun _ => [pc];
           rule_precond := ⊤oprec;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               (getRq orq O upRq) >>=[(ost, orq, nil)]
                 (fun rqinfo =>
                    match msg_value (rqi_msg rqinfo) with
                    | VNat n =>
                      (ost +#[implValueIdx <- n] +#[implStatusIdx <- msiM],
                       removeRq orq O upRq,
                       (ce,
                        {| msg_id := msiSetRs;
                           msg_value := VNat n |}) :: nil)
                    | _ => (ost, orq, nil)
                    end)
        |}.

      Definition childDownRqM: Rule ImplOStateIfc :=
        {| rule_idx := 7;
           rule_msg_ids := [msiDownRqM];
           rule_msgs_from := fun _ => [pc];
           rule_precond :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               HalfLockFree orq O;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               (ost +#[implStatusIdx <- msiI],
                orq,
                [(cpRs, {| msg_id := msiDownRsS;
                           msg_value := VNat (ost#[implValueIdx]) |})])
        |}.

      Definition childEvictRqI: Rule ImplOStateIfc :=
        {| rule_idx := 8;
           rule_msg_ids := [msiEvictRq];
           rule_msgs_from := fun _ => [ec];
           rule_precond :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               LockFree orq O /\ ost#[implStatusIdx] <> msiI;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               ((hd_error mins) >>=[(ost, orq, nil)]
                  (fun idm =>
                     (ost,
                      addRq orq O upRq (valOf idm) [pc] ce,
                      [(cpRq, {| msg_id := msiRqI;
                                 msg_value := VNat (ost#[implValueIdx]) |})])))
        |}.

      Definition childEvictRsI: Rule ImplOStateIfc :=
        {| rule_idx := 9;
           rule_msg_ids := [msiRsI];
           rule_msgs_from := fun _ => [pc];
           rule_precond := ⊤oprec;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               ((hd_error mins) >>=[(ost, orq, nil)]
                  (fun idm =>
                     (ost +#[implStatusIdx <- msiI],
                      removeRq orq O upRq,
                      [(ce, {| msg_id := msiEvictRs;
                               msg_value := VUnit |})])))
        |}.
      
      Definition child: Object :=
        {| obj_idx := coidx;
           obj_ifc := ImplOStateIfc;
           obj_rules :=
             [childGetRqImm; childGetRqS; childGetRsS; childDownRqS;
                childSetRqImm; childSetRqM; childSetRsM; childDownRqM;
                  childEvictRqI; childEvictRsI];
           obj_rules_valid := ltac:(inds_valid_tac) |}.
      
    End Child.

    Section Parent.

      Section Rules.
        Variable (ridxOfs: IdxT).
        Variables (cpRq pc cpRs' pc': IdxT).

        Definition parentNumOfRules := 7.

        Definition parentGetRqImm: Rule ImplOStateIfc :=
          {| rule_idx := parentNumOfRules * ridxOfs + 0;
             rule_msg_ids := [msiRqS];
             rule_msgs_from := fun _ => [cpRq];
             rule_precond :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 LockFree orq O /\ ost#[implStatusIdx] >= msiS;
             rule_trs :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 (ost, orq,
                  [(pc, {| msg_id := msiRsS;
                           msg_value := VNat (ost#[implValueIdx]) |})])
          |}.

        Definition parentGetDownRqS: Rule ImplOStateIfc :=
          {| rule_idx := parentNumOfRules * ridxOfs + 1;
             rule_msg_ids := [msiRqS];
             rule_msgs_from := fun _ => [cpRq];
             rule_precond :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 LockFree orq O /\ ost#[implStatusIdx] = msiI;
             rule_trs :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 ((hd_error mins) >>=[(ost, orq, nil)]
                    (fun idm =>
                       (ost,
                        addRq orq O downRq (valOf idm) [cpRs'] pc,
                        [(pc', {| msg_id := msiDownRqS;
                                  msg_value := VUnit |})])))
          |}.

        Definition parentGetDownRsS: Rule ImplOStateIfc :=
          {| rule_idx := parentNumOfRules * ridxOfs + 2;
             rule_msg_ids := [msiDownRsS];
             rule_msgs_from := fun _ => [cpRs'];
             rule_precond := ⊤oprec;
             rule_trs :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 ((hd_error mins) >>=[(ost, orq, nil)]
                    (fun idm =>
                       match msg_value (valOf idm) with
                       | VNat n =>
                         (ost +#[implValueIdx <- n] +#[implStatusIdx <-msiS],
                          removeRq orq O downRq,
                          [(pc, {| msg_id := msiRsS;
                                   msg_value := VNat n |})])
                       | _ => (ost, orq, nil)
                       end))
          |}.

        Definition parentSetRqImm: Rule ImplOStateIfc :=
          {| rule_idx := parentNumOfRules * ridxOfs + 3;
             rule_msg_ids := [msiRqM];
             rule_msgs_from := fun _ => [cpRq];
             rule_precond :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 LockFree orq O /\ ost#[implStatusIdx] = msiM;
             rule_trs :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 (ost +#[implStatusIdx <- msiI],
                  orq,
                  [(pc, {| msg_id := msiRsM;
                           msg_value := VNat (ost#[implValueIdx]) |})])
          |}.

        Definition parentSetDownRqM: Rule ImplOStateIfc :=
          {| rule_idx := parentNumOfRules * ridxOfs + 4;
             rule_msg_ids := [msiRqM];
             rule_msgs_from := fun _ => [cpRq];
             rule_precond :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 LockFree orq O /\ ost#[implStatusIdx] <> msiM;
             rule_trs :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 ((hd_error mins) >>=[(ost, orq, nil)]
                    (fun idm =>
                       (ost,
                        addRq orq O downRq (valOf idm) [cpRs'] pc,
                        [(pc', {| msg_id := msiDownRqM;
                                  msg_value := VUnit |})])))
          |}.

        Definition parentSetDownRsM: Rule ImplOStateIfc :=
          {| rule_idx := parentNumOfRules * ridxOfs + 5;
             rule_msg_ids := [msiDownRsM];
             rule_msgs_from := fun _ => [cpRs'];
             rule_precond := ⊤oprec;
             rule_trs :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 ((hd_error mins) >>=[(ost, orq, nil)]
                    (fun idm =>
                       match msg_value (valOf idm) with
                       | VNat n =>
                         (ost +#[implStatusIdx <- msiI],
                          removeRq orq O downRq,
                          [(pc, {| msg_id := msiRsM;
                                   msg_value := VNat n |})])
                       | _ => (ost, orq, nil)
                       end))
          |}.

        Definition parentEvictRqImm: Rule ImplOStateIfc :=
          {| rule_idx := parentNumOfRules * ridxOfs + 6;
             rule_msg_ids := [msiRqI];
             rule_msgs_from := fun _ => [cpRq];
             rule_precond :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 LockFree orq O;               
             rule_trs :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 ((hd_error mins) >>=[(ost, orq, nil)]
                    (fun idm =>
                       match msg_value (valOf idm) with
                       | VNat n =>
                         (ost +#[implValueIdx <- n] +#[implStatusIdx <- msiS],
                          orq,
                          [(pc, {| msg_id := msiRsI;
                                   msg_value := VUnit |})])
                       | _ => (ost, orq, nil)
                       end))
          |}.
        
        Definition parentRules :=
          [parentGetRqImm; parentGetDownRqS; parentGetDownRsS;
             parentSetRqImm; parentSetDownRqM; parentSetDownRsM;
               parentEvictRqImm].

      End Rules.
      
      Definition parent: Object :=
        {| obj_idx := parentIdx;
           obj_ifc := ImplOStateIfc;
           obj_rules :=
             (parentRules 0 c1pRq pc1 c2pRs pc2)
               ++ (parentRules 1 c2pRq pc2 c1pRs pc1);
           obj_rules_valid := ltac:(inds_valid_tac)
        |}.
      
    End Parent.
    
    Definition impl: System :=
      {| sys_objs :=
           [child child1Idx ec1 ce1 c1pRq c1pRs pc1;
              child child2Idx ec2 ce2 c2pRq c2pRs pc2;
              parent];
         sys_oinds_valid := ltac:(inds_valid_tac);
         sys_minds := [c1pRq; c1pRs; pc1; c2pRq; c2pRs; pc2];
         sys_merqs := [erq1; erq2];
         sys_merss := [ers1; ers2];
         sys_msg_inds_valid := ltac:(inds_valid_tac);
         sys_oss_inits := implInit;
         sys_orqs_inits := []
      |}.

    Definition implTopo: GTree :=
      Node parentIdx
           [([createEdge child1Idx c1pRq parentIdx;
                createEdge child1Idx c1pRs parentIdx;
                createEdge parentIdx pc1 child1Idx],
             Node child1Idx nil);
              ([createEdge child2Idx parentIdx c2pRq;
                  createEdge child2Idx parentIdx c2pRs;
                  createEdge parentIdx child2Idx pc2],
               Node child2Idx nil)].
                                            
  End Impl.

End System.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

