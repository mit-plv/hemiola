Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport Syntax Semantics.
Require Import Topology RqRsTopo.

Require Import Spec SpecSv Msi.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Section System.

  Definition erq1 := erq 0.
  Definition ers1 := ers 0.
  Definition erq2 := erq 1.
  Definition ers2 := ers 1.

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
  Definition implInit: OStates ImplOStateIfc :=
    [parentIdx <- (0, (msiS, tt))]
    +[child1Idx <- (0, (msiS, tt))]
    +[child2Idx <- (0, (msiS, tt))].

  Section Child.
    Variable (coidx: IdxT).
    Variables (ec ce cpRq cpRs pc: IdxT).

    Definition childGetRqImm: Rule ImplOStateIfc :=
      {| rule_idx := 0;
         rule_precond :=
           MsgsFrom [ec]
           /\oprec MsgIdsFrom [getRq]
           /\oprec RqAccepting
           /\oprec UpLockFree
           /\oprec
               fun (ost: OState ImplOStateIfc) orq mins =>
                 ost#[implStatusIdx] >= msiS;
         rule_trs :=
           fun (ost: OState ImplOStateIfc) orq mins =>
             (ost, orq,
              [(ce, {| msg_id := getRs;
                       msg_type := MRs;
                       msg_value := VNat (ost#[implValueIdx])
                    |})])
      |}.

    Definition childGetRqS: Rule ImplOStateIfc :=
      {| rule_idx := 1;
         rule_precond :=
           MsgsFrom [ec]
           /\oprec MsgIdsFrom [getRq]
           /\oprec RqAccepting
           /\oprec UpLockFree
           /\oprec
               fun (ost: OState ImplOStateIfc) orq mins =>
                 ost#[implStatusIdx] = msiI;
         rule_trs :=
           fun (ost: OState ImplOStateIfc) orq mins =>
             ((hd_error mins) >>=[(ost, orq, nil)]
               (fun idm =>
                  (ost,
                   addRq orq upRq (valOf idm) [pc] ce,
                   [(cpRq, {| msg_id := msiRqS;
                              msg_type := MRq;
                              msg_value := VUnit |})])))
      |}.

    Definition childGetRsS: Rule ImplOStateIfc :=
      {| rule_idx := 2;
         rule_precond :=
           MsgsFrom [pc]
           /\oprec MsgIdsFrom [msiRsS]
           /\oprec RsAccepting;
         rule_trs :=
           fun (ost: OState ImplOStateIfc) orq mins =>
             ((hd_error mins) >>=[(ost, orq, nil)]
               (fun idm =>
                  match msg_value (valOf idm) with
                  | VNat n =>
                    (ost +#[implValueIdx <- n] +#[implStatusIdx <- msiS],
                     removeRq orq upRq,
                     [(ce, {| msg_id := getRs;
                              msg_type := MRs;
                              msg_value := VNat n |})])
                  | _ => (ost, orq, nil) (** TODO: how to efficiently handle this case? *)
                  end))
      |}.

    Definition childDownRqS: Rule ImplOStateIfc :=
      {| rule_idx := 3;
         rule_precond :=
           MsgsFrom [pc]
           /\oprec MsgIdsFrom [msiDownRqS]
           /\oprec RqAccepting;
         rule_trs :=
           fun (ost: OState ImplOStateIfc) orq mins =>
             (ost+#[implStatusIdx <- msiS],
              orq,
              [(cpRs, {| msg_id := msiDownRsS;
                         msg_type := MRs;
                         msg_value := VUnit |})])
      |}.

    Definition childSetRqImm: Rule ImplOStateIfc :=
      {| rule_idx := 4;
         rule_precond :=
           MsgsFrom [ec]
           /\oprec MsgIdsFrom [setRq]
           /\oprec RqAccepting
           /\oprec UpLockFree
           /\oprec
               fun (ost: OState ImplOStateIfc) orq mins =>
                 ost#[implStatusIdx] = msiM;
         rule_trs :=
           fun (ost: OState ImplOStateIfc) orq mins =>
             ((hd_error mins) >>=[(ost, orq, nil)]
               (fun idm =>
                  match msg_value (valOf idm) with
                  | VNat n =>
                    (ost +#[implValueIdx <- n] +#[implStatusIdx <- msiM],
                     orq,
                     [(ce, {| msg_id := setRs;
                              msg_type := MRs;
                              msg_value := VUnit |})])
                  | _ => (ost, orq, nil)
                  end))
      |}.
    
    Definition childSetRqM: Rule ImplOStateIfc :=
      {| rule_idx := 5;
         rule_precond :=
           MsgsFrom [ec]
           /\oprec MsgIdsFrom [setRq]
           /\oprec RqAccepting
           /\oprec UpLockFree
           /\oprec
               fun (ost: OState ImplOStateIfc) orq mins =>
                 ost#[implStatusIdx] <> msiM;
         rule_trs :=
           fun (ost: OState ImplOStateIfc) orq mins =>
             ((hd_error mins) >>=[(ost, orq, nil)]
               (fun idm =>
                  (ost,
                   addRq orq upRq (valOf idm) [pc] ce,
                   [(cpRq, {| msg_id := msiRqM;
                              msg_type := MRq;
                              msg_value := VUnit |})])))
      |}.

    Definition childSetRsM: Rule ImplOStateIfc :=
      {| rule_idx := 6;
         rule_precond :=
           MsgsFrom [pc]
           /\oprec MsgIdsFrom [msiRsM]
           /\oprec RsAccepting;
         rule_trs :=
           fun (ost: OState ImplOStateIfc) orq mins =>
             (Syntax.getRq orq upRq) >>=[(ost, orq, nil)]
               (fun rqinfo =>
                  match msg_value (rqi_msg rqinfo) with
                  | VNat n =>
                    (ost +#[implValueIdx <- n] +#[implStatusIdx <- msiM],
                     removeRq orq upRq,
                     (ce,
                      {| msg_id := setRs;
                         msg_type := MRs;
                         msg_value := VNat n |}) :: nil)
                  | _ => (ost, orq, nil)
                  end)
      |}.

    Definition childDownRqM: Rule ImplOStateIfc :=
      {| rule_idx := 7;
         rule_precond :=
           MsgsFrom [pc]
           /\oprec MsgIdsFrom [msiDownRqM]
           /\oprec RqAccepting;
         rule_trs :=
           fun (ost: OState ImplOStateIfc) orq mins =>
             (ost +#[implStatusIdx <- msiI],
              orq,
              [(cpRs, {| msg_id := msiDownRsS;
                         msg_type := MRs;
                         msg_value := VNat (ost#[implValueIdx]) |})])
      |}.

    Definition childEvictRqI: Rule ImplOStateIfc :=
      {| rule_idx := 8;
         rule_precond :=
           MsgsFrom [ec]
           /\oprec MsgIdsFrom [evictRq]
           /\oprec RqAccepting
           /\oprec UpLockFree;
         rule_trs :=
           fun (ost: OState ImplOStateIfc) orq mins =>
             ((hd_error mins) >>=[(ost, orq, nil)]
               (fun idm =>
                  (ost,
                   addRq orq upRq (valOf idm) [pc] ce,
                   [(cpRq, {| msg_id := msiRqI;
                              msg_type := MRq;
                              msg_value := VNat (ost#[implValueIdx]) |})])))
      |}.

    Definition childEvictRsI: Rule ImplOStateIfc :=
      {| rule_idx := 9;
         rule_precond :=
           MsgsFrom [pc]
           /\oprec MsgIdsFrom [msiRsI]
           /\oprec RsAccepting;
         rule_trs :=
           fun (ost: OState ImplOStateIfc) orq mins =>
             ((hd_error mins) >>=[(ost, orq, nil)]
               (fun idm =>
                  (ost +#[implStatusIdx <- msiI],
                   removeRq orq upRq,
                   [(ce, {| msg_id := evictRs;
                            msg_type := MRs;
                            msg_value := VUnit |})])))
      |}.
      
    Definition child: Object ImplOStateIfc :=
      {| obj_idx := coidx;
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
           rule_precond :=
             MsgsFrom [cpRq]
             /\oprec MsgIdsFrom [msiRqS]
             /\oprec RqAccepting
             /\oprec DownLockFree
             /\oprec
                 fun (ost: OState ImplOStateIfc) orq mins =>
                   ost#[implStatusIdx] >= msiS;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               (ost, orq,
                [(pc, {| msg_id := msiRsS;
                         msg_type := MRs;
                         msg_value := VNat (ost#[implValueIdx]) |})])
        |}.

      Definition parentGetDownRqS: Rule ImplOStateIfc :=
        {| rule_idx := parentNumOfRules * ridxOfs + 1;
           rule_precond :=
             MsgsFrom [cpRq]
             /\oprec MsgIdsFrom [msiRqS]
             /\oprec RqAccepting
             /\oprec DownLockFree
             /\oprec
                 fun (ost: OState ImplOStateIfc) orq mins =>
                   ost#[implStatusIdx] = msiI;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               ((hd_error mins) >>=[(ost, orq, nil)]
                 (fun idm =>
                    (ost,
                     addRq orq downRq (valOf idm) [cpRs'] pc,
                     [(pc', {| msg_id := msiDownRqS;
                               msg_type := MRq;
                               msg_value := VNat (ost#[implValueIdx]) |})])))
        |}.

      Definition parentGetDownRsS: Rule ImplOStateIfc :=
        {| rule_idx := parentNumOfRules * ridxOfs + 2;
           rule_precond :=
             MsgsFrom [cpRs']
             /\oprec MsgIdsFrom [msiDownRsS]
             /\oprec RsAccepting;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               ((hd_error mins) >>=[(ost, orq, nil)]
                 (fun idm =>
                    match msg_value (valOf idm) with
                    | VNat n =>
                      (ost +#[implValueIdx <- n] +#[implStatusIdx <-msiS],
                       removeRq orq downRq,
                       [(pc, {| msg_id := msiRsS;
                                msg_type := MRs;
                                msg_value := VNat n |})])
                    | _ => (ost, orq, nil)
                    end))
        |}.

      Definition parentSetRqImm: Rule ImplOStateIfc :=
        {| rule_idx := parentNumOfRules * ridxOfs + 3;
           rule_precond :=
             MsgsFrom [cpRq]
             /\oprec MsgIdsFrom [msiRqM]
             /\oprec RqAccepting
             /\oprec DownLockFree
             /\oprec
                 fun (ost: OState ImplOStateIfc) orq mins =>
                   ost#[implStatusIdx] = msiM;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               (ost +#[implStatusIdx <- msiI],
                orq,
                [(pc, {| msg_id := msiRsM;
                         msg_type := MRs;
                         msg_value := VNat (ost#[implValueIdx]) |})])
        |}.

      Definition parentSetDownRqM: Rule ImplOStateIfc :=
        {| rule_idx := parentNumOfRules * ridxOfs + 4;
           rule_precond :=
             MsgsFrom [cpRq]
             /\oprec MsgIdsFrom [msiRqM]
             /\oprec RqAccepting
             /\oprec DownLockFree
             /\oprec
                 fun (ost: OState ImplOStateIfc) orq mins =>
                   ost#[implStatusIdx] <> msiM;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               ((hd_error mins) >>=[(ost, orq, nil)]
                 (fun idm =>
                    (ost,
                     addRq orq downRq (valOf idm) [cpRs'] pc,
                     [(pc', {| msg_id := msiDownRqM;
                               msg_type := MRq;
                               msg_value := VUnit |})])))
        |}.

      Definition parentSetDownRsM: Rule ImplOStateIfc :=
        {| rule_idx := parentNumOfRules * ridxOfs + 5;
           rule_precond :=
             MsgsFrom [cpRs']
             /\oprec MsgIdsFrom [msiDownRsM]
             /\oprec RsAccepting;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               ((hd_error mins) >>=[(ost, orq, nil)]
                 (fun idm =>
                    match msg_value (valOf idm) with
                    | VNat n =>
                      (ost +#[implStatusIdx <- msiI],
                       removeRq orq downRq,
                       [(pc, {| msg_id := msiRsM;
                                msg_type := MRs;
                                msg_value := VNat n |})])
                    | _ => (ost, orq, nil)
                    end))
        |}.

      Definition parentEvictRqImm: Rule ImplOStateIfc :=
        {| rule_idx := parentNumOfRules * ridxOfs + 6;
           rule_precond :=
             MsgsFrom [cpRq]
             /\oprec MsgIdsFrom [msiRqI]
             /\oprec RqAccepting
             /\oprec DownLockFree;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               ((hd_error mins) >>=[(ost, orq, nil)]
                 (fun idm =>
                    match msg_value (valOf idm) with
                    | VNat n =>
                      (ost +#[implValueIdx <- n] +#[implStatusIdx <- msiS],
                       orq,
                       [(pc, {| msg_id := msiRsI;
                                msg_type := MRs;
                                msg_value := VUnit |})])
                    | _ => (ost, orq, nil)
                    end))
        |}.
      
      Definition parentRules :=
        [parentGetRqImm; parentGetDownRqS; parentGetDownRsS;
           parentSetRqImm; parentSetDownRqM; parentSetDownRsM;
             parentEvictRqImm].

    End Rules.
    
    Definition parent: Object ImplOStateIfc :=
      {| obj_idx := parentIdx;
         obj_rules :=
           (parentRules 0 c1pRq pc1 c2pRs pc2)
             ++ (parentRules 1 c2pRq pc2 c1pRs pc1);
         obj_rules_valid := ltac:(inds_valid_tac)
      |}.
    
  End Parent.
  
  Definition impl: System ImplOStateIfc :=
    {| sys_objs :=
         [child child1Idx ec1 ce1 c1pRq c1pRs pc1;
            child child2Idx ec2 ce2 c2pRq c2pRs pc2;
            parent];
       sys_oinds_valid := ltac:(inds_valid_tac);
       sys_minds := [c1pRq; c1pRs; pc1; c2pRq; c2pRs; pc2];
       sys_merqs := [erq1; erq2];
       sys_merss := [ers1; ers2];
       sys_msg_inds_valid := ltac:(inds_valid_tac);
       sys_oss_inits := implInit
    |}.

End System.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

