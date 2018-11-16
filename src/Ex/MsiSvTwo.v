Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport Syntax Semantics StepT.
Require Import Topology RqRs.

Require Import Spec SpecSv Msi.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Section System.
  Variable numC: nat. (* if [numC = 0], then the system has a single child. *)

  Section Impl.

    Definition ec (i: nat) := 2 * numC + 5 * i.
    Definition ce (i: nat) := 2 * numC + 5 * i + 1.
    Definition cpRq (i: nat) := 2 * numC + 5 * i + 2.
    Definition cpRs (i: nat) := 2 * numC + 5 * i + 3.
    Definition pc (i: nat) := 2 * numC + 5 * i + 4.

    Definition cpRss (inds: list nat) := map cpRs inds.
    Definition pcs (inds: list nat) := map pc inds.
    
    Definition parentIdx := numC.

    Definition implValueIdx: Fin.t 3 := Fin.F1.
    Definition implStatusIdx: Fin.t 3 := Fin.FS Fin.F1.
    Definition implDirIdx: Fin.t 3 := Fin.FS (Fin.FS Fin.F1).
    
    Definition ImplOStateIfc: OStateIfc :=
      {| ost_sz := 3;
         ost_ty :=
           [nat:Type; (* child/parent:value *)
              nat:Type; (* child:status *)
              (list IdxT):Type (* parent:directory -- which children have the status? *)
           ]%vector |}.

    Fixpoint childrenInit (i: nat): OStates ImplOStateIfc :=
      match i with
      | O => [O <- (0, (msiS, (nil, tt)))]
      | S i' => (childrenInit i')+[i <- (0, (msiS, (nil, tt)))]
      end.

    Fixpoint childrenIndices (i: nat): list IdxT :=
      match i with
      | O => [O]
      | S i' => i :: childrenIndices i'
      end.

    (* NOTE: all the children have the status S in the beginning. *)
    Definition implInit: OStates ImplOStateIfc :=
      (childrenInit numC)
      +[parentIdx <- (0, (msiS, (childrenIndices numC, tt)))].

    Section Child.
      Variable (coidx: IdxT).

      Definition childGetRqImm: Rule ImplOStateIfc :=
        {| rule_idx := 0;
           rule_msg_ids_from := [getRq];
           rule_msg_ids_to := [getRs];
           rule_precond :=
             MsgsFrom [ec coidx] /\oprec
             fun (ost: OState ImplOStateIfc) orq mins =>
               LockFree orq O /\ ost#[implStatusIdx] >= msiS;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               (ost, orq,
                [(ce coidx, {| msg_id := getRs;
                               msg_value := VNat (ost#[implValueIdx])
                      |})])
        |}.

      Definition childGetRqS: Rule ImplOStateIfc :=
        {| rule_idx := 1;
           rule_msg_ids_from := [getRq];
           rule_msg_ids_to := [msiRqS];
           rule_precond :=
             MsgsFrom [ec coidx] /\oprec
             fun (ost: OState ImplOStateIfc) orq mins =>
               LockFree orq O /\ ost#[implStatusIdx] = msiI;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               ((hd_error mins) >>=[(ost, orq, nil)]
                  (fun idm =>
                     (ost,
                      addRq orq O upRq (valOf idm) [pc coidx] (ce coidx),
                      [(cpRq coidx, {| msg_id := msiRqS;
                                       msg_value := VUnit |})])))
        |}.

      Definition childGetRsS: Rule ImplOStateIfc :=
        {| rule_idx := 2;
           rule_msg_ids_from := [msiRsS];
           rule_msg_ids_to := [getRs];
           rule_precond := MsgsFrom [pc coidx];
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               ((hd_error mins) >>=[(ost, orq, nil)]
                  (fun idm =>
                     match msg_value (valOf idm) with
                     | VNat n =>
                       (ost +#[implValueIdx <- n] +#[implStatusIdx <- msiS],
                        removeRq orq O upRq,
                        [(ce coidx, {| msg_id := getRs;
                                       msg_value := VNat n |})])
                     | _ => (ost, orq, nil) (** TODO: how to efficiently handle this case? *)
                     end))
        |}.

      Definition childDownRqS: Rule ImplOStateIfc :=
        {| rule_idx := 3;
           rule_msg_ids_from := [msiDownRqS];
           rule_msg_ids_to := [msiDownRsS];
           rule_precond :=
             MsgsFrom [pc coidx] /\oprec
             fun (ost: OState ImplOStateIfc) orq mins =>
               HalfLockFree orq O;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               (ost+#[implStatusIdx <- msiS],
                orq,
                [(cpRs coidx, {| msg_id := msiDownRsS;
                                 msg_value := VNat (ost#[implValueIdx]) |})])
        |}.

      Definition childSetRqImm: Rule ImplOStateIfc :=
        {| rule_idx := 4;
           rule_msg_ids_from := [setRq];
           rule_msg_ids_to := [setRs];
           rule_precond :=
             MsgsFrom [ec coidx] /\oprec
             fun (ost: OState ImplOStateIfc) orq mins =>
               LockFree orq O /\ ost#[implStatusIdx] = msiM;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               ((hd_error mins) >>=[(ost, orq, nil)]
                  (fun idm =>
                     match msg_value (valOf idm) with
                     | VNat n =>
                       (ost +#[implValueIdx <- n],
                        orq,
                        [(ce coidx, {| msg_id := setRs;
                                       msg_value := VUnit |})])
                     | _ => (ost, orq, nil)
                     end))
        |}.
    
      Definition childSetRqM: Rule ImplOStateIfc :=
        {| rule_idx := 5;
           rule_msg_ids_from := [setRq];
           rule_msg_ids_to := [msiRqM];
           rule_precond :=
             MsgsFrom [ec coidx] /\oprec
             fun (ost: OState ImplOStateIfc) orq mins =>
               LockFree orq O /\ ost#[implStatusIdx] <> msiM;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               ((hd_error mins) >>=[(ost, orq, nil)]
                  (fun idm =>
                     (ost,
                      addRq orq O upRq (valOf idm) [pc coidx] (ce coidx),
                      [(cpRq coidx, {| msg_id := msiRqM;
                                       msg_value := VUnit |})])))
        |}.

      Definition childSetRsM: Rule ImplOStateIfc :=
        {| rule_idx := 6;
           rule_msg_ids_from := [msiRsM];
           rule_msg_ids_to := [setRs];
           rule_precond := MsgsFrom [pc coidx];
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               (Syntax.getRq orq O upRq) >>=[(ost, orq, nil)]
                 (fun rqinfo =>
                    match msg_value (rqi_msg rqinfo) with
                    | VNat n =>
                      (ost +#[implValueIdx <- n] +#[implStatusIdx <- msiM],
                       removeRq orq O upRq,
                       (ce coidx,
                        {| msg_id := setRs;
                           msg_value := VNat n |}) :: nil)
                    | _ => (ost, orq, nil)
                    end)
        |}.

      Definition childDownRqM: Rule ImplOStateIfc :=
        {| rule_idx := 7;
           rule_msg_ids_from := [msiDownRqM];
           rule_msg_ids_to := [msiDownRsM];
           rule_precond :=
             MsgsFrom [pc coidx] /\oprec
             fun (ost: OState ImplOStateIfc) orq mins =>
               HalfLockFree orq O;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               (ost +#[implStatusIdx <- msiI],
                orq,
                [(cpRs coidx, {| msg_id := msiDownRsM;
                                 msg_value := VNat (ost#[implValueIdx]) |})])
        |}.

      Definition childEvictRqI: Rule ImplOStateIfc :=
        {| rule_idx := 8;
           rule_msg_ids_from := nil;
           rule_msg_ids_to := [msiRqI];
           rule_precond :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               LockFree orq O /\ ost#[implStatusIdx] <> msiI;
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               ((hd_error mins) >>=[(ost, orq, nil)]
                  (fun idm =>
                     (ost,
                      addRq orq O upRq (valOf idm) [pc coidx] (ce coidx),
                      [(cpRq coidx, {| msg_id := msiRqI;
                                       msg_value := VNat (ost#[implValueIdx]) |})])))
        |}.

      Definition childEvictRsI: Rule ImplOStateIfc :=
        {| rule_idx := 9;
           rule_msg_ids_from := [msiRsI];
           rule_msg_ids_to := nil;
           rule_precond := MsgsFrom [pc coidx];
           rule_trs :=
             fun (ost: OState ImplOStateIfc) orq mins =>
               ((hd_error mins) >>=[(ost, orq, nil)]
                  (fun idm =>
                     (ost +#[implStatusIdx <- msiI],
                      removeRq orq O upRq,
                      nil)))
        |}.
      
      Definition child: Object ImplOStateIfc :=
        {| obj_idx := coidx;
           obj_rules :=
             [childGetRqImm; childGetRqS; childGetRsS; childDownRqS;
                childSetRqImm; childSetRqM; childSetRsM; childDownRqM;
                  childEvictRqI; childEvictRsI];
           obj_rules_valid := ltac:(inds_valid_tac) |}.
      
    End Child.

    Fixpoint childObjs (i: nat) :=
      match i with
      | O => [child O]
      | S i' => child i :: childObjs i'
      end.
    
    Section Parent.

      Section Rules.
        Variables (coidx: IdxT).

        Definition parentNumOfRules := 7.

        (* When a directory status is S, the parent always has the up-to-date 
         * value as well, which should be proven as an invariant.
         *)
        Definition parentGetRqImm: Rule ImplOStateIfc :=
          {| rule_idx := parentNumOfRules * coidx + 0;
             rule_msg_ids_from := [msiRqS];
             rule_msg_ids_to := [msiRsS];
             rule_precond :=
               MsgsFrom [cpRq coidx] /\oprec
               fun (ost: OState ImplOStateIfc) orq mins =>
                 LockFree orq O /\ ost#[implStatusIdx] <= msiS;
             rule_trs :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 (ost +#[implStatusIdx <- msiS],
                  orq,
                  [(pc coidx, {| msg_id := msiRsS;
                           msg_value := VNat (ost#[implValueIdx]) |})])
          |}.

        (* When a directory status is M, there must exist a child who has the M
         * status. The parent always stores the child index, which should be
         * proven as an invariant.
         *)
        Definition parentGetDownRqS: Rule ImplOStateIfc :=
          {| rule_idx := parentNumOfRules * coidx + 1;
             rule_msg_ids_from := [msiRqS];
             rule_msg_ids_to := [msiDownRqS];
             rule_precond :=
               MsgsFrom [cpRq coidx] /\oprec
               fun (ost: OState ImplOStateIfc) orq mins =>
                 LockFree orq O /\ ost#[implStatusIdx] = msiM;
             rule_trs :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 ((hd_error mins) >>=[(ost, orq, nil)]
                    (fun idm =>
                       (hd_error (ost#[implDirIdx])) >>=[(ost, orq, nil)]
                         (fun idxM =>
                            (ost,
                             addRq orq O downRq (valOf idm) [cpRs idxM] (pc coidx),
                             [(idxM, {| msg_id := msiDownRqS;
                                        msg_value := VUnit |})]))))
          |}.

        Definition parentGetDownRsS: Rule ImplOStateIfc :=
          {| rule_idx := parentNumOfRules * coidx + 2;
             rule_msg_ids_from := [msiDownRsS];
             rule_msg_ids_to := [msiRsS];
             rule_precond := MsgsFromORq O downRq;
             rule_trs :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 ((hd_error mins) >>=[(ost, orq, nil)]
                    (fun idm =>
                       match msg_value (valOf idm) with
                       | VNat n =>
                         (ost +#[implValueIdx <- n]
                              +#[implStatusIdx <- msiS]
                              +#[implDirIdx <- coidx :: ost#[implDirIdx]],
                          removeRq orq O downRq,
                          [(pc coidx, {| msg_id := msiRsS;
                                         msg_value := VNat n |})])
                       | _ => (ost, orq, nil)
                       end))
          |}.

        (* The parent can respond immediately for [Set] requests from a child
         * if the directory status is I, meaning all children have the I status.
         *)
        Definition parentSetRqImm: Rule ImplOStateIfc :=
          {| rule_idx := parentNumOfRules * coidx + 3;
             rule_msg_ids_from := [msiRqM];
             rule_msg_ids_to := [msiRsM];
             rule_precond :=
               MsgsFrom [cpRq coidx] /\oprec
               fun (ost: OState ImplOStateIfc) orq mins =>
                 LockFree orq O /\ ost#[implStatusIdx] = msiI;
             rule_trs :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 (ost +#[implStatusIdx <- msiM],
                  orq,
                  [(pc coidx, {| msg_id := msiRsM;
                                 msg_value := VNat (ost#[implValueIdx]) |})])
          |}.

        Definition parentSetDownRqM: Rule ImplOStateIfc :=
          {| rule_idx := parentNumOfRules * coidx + 4;
             rule_msg_ids_from := [msiRqM];
             rule_msg_ids_to := [msiDownRqM];
             rule_precond :=
               MsgsFrom [cpRq coidx] /\oprec
               fun (ost: OState ImplOStateIfc) orq mins =>
                 LockFree orq O /\ ost#[implStatusIdx] <> msiI;
             rule_trs :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 ((hd_error mins) >>=[(ost, orq, nil)]
                    (fun idm =>
                       (ost,
                        addRq orq O downRq (valOf idm) (cpRss (ost#[implDirIdx])) (pc coidx),
                        broadcaster (pcs (ost#[implDirIdx]))
                                    {| msg_id := msiDownRqM;
                                       msg_value := VUnit |})))
          |}.

        Definition parentSetDownRsM: Rule ImplOStateIfc :=
          {| rule_idx := parentNumOfRules * coidx + 5;
             rule_msg_ids_from := [msiDownRsM];
             rule_msg_ids_to := [msiRsM];
             rule_precond := MsgsFromORq O downRq;
             rule_trs :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 ((hd_error mins) >>=[(ost, orq, nil)]
                    (fun idm =>
                       match msg_value (valOf idm) with
                       | VNat n =>
                         (ost +#[implStatusIdx <- msiI],
                          removeRq orq O downRq,
                          [(pc coidx, {| msg_id := msiRsM;
                                         msg_value := VNat n |})])
                       | _ => (ost, orq, nil)
                       end))
          |}.

        (* When the parent getting an eviction request from a child with the S
         * status, it needs to check how many children are in S and to change 
         * the directory status accordingly.
         *)
        Definition parentEvictRqImmS: Rule ImplOStateIfc :=
          {| rule_idx := parentNumOfRules * coidx + 6;
             rule_msg_ids_from := [msiRqI];
             rule_msg_ids_to := [msiRsI];
             rule_precond :=
               MsgsFrom [cpRq coidx] /\oprec
               fun (ost: OState ImplOStateIfc) orq mins =>
                 LockFree orq O /\ ost#[implStatusIdx] = msiS;
             rule_trs :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 let rdir := List.remove eq_nat_dec coidx (ost#[implDirIdx]) in
                 (ost +#[implStatusIdx <- if eq_nat_dec (List.length rdir) 0
                                          then msiI
                                          else msiS]
                      +#[implDirIdx <- rdir],
                  orq,
                  [(pc coidx, {| msg_id := msiRsI;
                                 msg_value := VUnit |})])
          |}.

        Definition parentEvictRqImmM: Rule ImplOStateIfc :=
          {| rule_idx := parentNumOfRules * coidx + 7;
             rule_msg_ids_from := [msiRqI];
             rule_msg_ids_to := [msiRsI];
             rule_precond :=
               MsgsFrom [cpRq coidx] /\oprec
               fun (ost: OState ImplOStateIfc) orq mins =>
                 LockFree orq O /\ ost#[implStatusIdx] = msiM;
             rule_trs :=
               fun (ost: OState ImplOStateIfc) orq mins =>
                 ((hd_error mins) >>=[(ost, orq, nil)]
                    (fun idm =>
                       match msg_value (valOf idm) with
                       | VNat n =>
                         (ost +#[implValueIdx <- n] +#[implStatusIdx <- msiI],
                          orq,
                          [(pc coidx, {| msg_id := msiRsI;
                                         msg_value := VUnit |})])
                       | _ => (ost, orq, nil)
                       end))
          |}.
        
        Definition parentRulesC :=
          [parentGetRqImm; parentGetDownRqS; parentGetDownRsS;
             parentSetRqImm; parentSetDownRqM; parentSetDownRsM;
               parentEvictRqImmS; parentEvictRqImmM].

      End Rules.

      Fixpoint parentRules (i: nat) :=
        match i with
        | O => parentRulesC O
        | S i' => parentRulesC i ++ parentRules i'
        end.

      Lemma parent_obj_rules_valid:
        forall i, NoDup (map (@rule_idx _) (parentRules i)).
      Proof.
      Admitted.
      
      Definition parent: Object ImplOStateIfc :=
        {| obj_idx := parentIdx;
           obj_rules := parentRules numC;
           obj_rules_valid := parent_obj_rules_valid numC
        |}.
      
    End Parent.

    Lemma impl_oinds_valid:
      NoDup (map (@obj_idx _) (parent :: childObjs numC)).
    Proof.
    Admitted.

    Fixpoint impl_minds (i: nat) :=
      match i with
      | O => [cpRq O; cpRs O; pc O]
      | S i' => [cpRq i; cpRs i; pc i] ++ impl_minds i'
      end.

    Fixpoint impl_merqs (i: nat) :=
      match i with
      | O => [erq O]
      | S i' => [erq i] ++ impl_merqs i'
      end.
      
    Fixpoint impl_merss (i: nat) :=
      match i with
      | O => [ers O]
      | S i' => [ers i] ++ impl_merss i'
      end.

    Lemma impl_msg_inds_valid:
      NoDup (impl_minds numC ++ impl_merqs numC ++ impl_merss numC).
    Proof.
    Admitted.
    
    Definition impl: System ImplOStateIfc :=
      {| sys_objs := parent :: childObjs numC;
         sys_oinds_valid := impl_oinds_valid;
         sys_minds := impl_minds numC;
         sys_merqs := impl_merqs numC;
         sys_merss := impl_merss numC;
         sys_msg_inds_valid := impl_msg_inds_valid;
         sys_oss_inits := implInit;
         sys_orqs_inits := []
      |}.

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
                                            
  End Impl.

End System.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

