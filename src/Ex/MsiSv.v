Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport Syntax Semantics.
Require Import Topology RqRsTopo RqRsLang.

Require Import Spec SpecSv Msi.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Section System.

  Definition ecd1 := 2.
  Definition ecd2 := 3.
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
    {| ost_ty := [nat:Type; nat:Type]%vector |}.
  Definition implInit: OStates ImplOStateIfc :=
    [parentIdx <- (0, (msiS, tt))]
    +[child1Idx <- (0, (msiS, tt))]
    +[child2Idx <- (0, (msiS, tt))].

  Section Child.
    Variable (coidx: IdxT).
    Variables (ec ce cpRq cpRs pc: IdxT).

    Definition childGetRqImm: Rule ImplOStateIfc :=
      rule[0]
      :requires
         (MsgsFrom [ec]
          /\ MsgIdsFrom [getRq]
          /\ RqAccepting
          /\ UpLockFree
          /\ DownLockFree
          /\ (fun (ost: OState ImplOStateIfc) orq mins =>
                ost#[implStatusIdx] >= msiS))
      :transition
         (fun (ost: OState ImplOStateIfc) orq mins =>
            (ost, orq,
             [(ce, {| msg_id := getRs;
                      msg_type := MRs;
                      msg_value := VNat (ost#[implValueIdx])
                   |})])).
    
    Definition childGetRqS: Rule ImplOStateIfc :=
      rule[1]
      :requires
         (MsgsFrom [ec]
          /\ MsgIdsFrom [getRq]
          /\ RqAccepting
          /\ UpLockFree
          /\ (fun (ost: OState ImplOStateIfc) orq mins =>
                ost#[implStatusIdx] = msiI))
      :transition
         (do (msg <-- getFirstMsg;
                st --> (st.ost,
                        addRq (st.orq) upRq msg [pc] ce,
                        [(cpRq, {| msg_id := msiRqS;
                                   msg_type := MRq;
                                   msg_value := VUnit |})]))).
    
    Definition childGetRsS: Rule ImplOStateIfc :=
      rule[2]
      :requires
         (MsgsFromORq upRq
          /\ MsgIdsFrom [msiRsS]
          /\ RsAccepting
          /\ FirstNatMsg
          /\ UpLocked
          /\ DownLockFree)
      :transition
         (do (n <-- getFirstNatMsg;
                ursb <-- getUpLockIdxBack;
                st {{ ImplOStateIfc }}
                   --> (st.ost +#[implValueIdx <- n]
                               +#[implStatusIdx <- msiS],
                        removeRq (st.orq) upRq,
                        [(ursb, {| msg_id := getRs;
                                   msg_type := MRs;
                                   msg_value := VNat n |})]))).

    Definition childDownRqS: Rule ImplOStateIfc :=
      rule[3]
      :requires
         (MsgsFrom [pc]
          /\ MsgIdsFrom [msiDownRqS]
          /\ RqAccepting
          /\ DownLockFree
          /\ (fun (ost: OState ImplOStateIfc) orq mins =>
                ost#[implStatusIdx] >= msiS))
      :transition
         (fun (ost: OState ImplOStateIfc) orq mins =>
            (ost+#[implStatusIdx <- msiS],
             orq,
             [(cpRs, {| msg_id := msiDownRsS;
                        msg_type := MRs;
                        msg_value := VNat (ost#[implValueIdx]) |})])).

    Definition childSetRqImm: Rule ImplOStateIfc :=
      rule[4]
      :requires
         (MsgsFrom [ec]
          /\ MsgIdsFrom [setRq]
          /\ RqAccepting
          /\ UpLockFree
          /\ DownLockFree
          /\ FirstNatMsg
          /\ (fun (ost: OState ImplOStateIfc) orq mins =>
                ost#[implStatusIdx] = msiM))
      :transition
         (do (n <-- getFirstNatMsg;
                st {{ ImplOStateIfc }}
                   --> (st.ost +#[implValueIdx <- n]
                               +#[implStatusIdx <- msiM],
                        st.orq,
                        [(ce, {| msg_id := setRs;
                                 msg_type := MRs;
                                 msg_value := VUnit |})]))).

    Definition childSetRqM: Rule ImplOStateIfc :=
      rule[5]
      :requires
         (MsgsFrom [ec]
          /\ MsgIdsFrom [setRq]
          /\ RqAccepting
          /\ UpLockFree
          /\ (fun (ost: OState ImplOStateIfc) orq mins =>
                ost#[implStatusIdx] <> msiM))
      :transition
         (do (msg <-- getFirstMsg;
                st --> (st.ost,
                        addRq (st.orq) upRq msg [pc] ce,
                        [(cpRq, {| msg_id := msiRqM;
                                   msg_type := MRq;
                                   msg_value := VUnit |})]))).

    Definition childSetRsM: Rule ImplOStateIfc :=
      rule[6]
      :requires
         (MsgsFromORq upRq
          /\ MsgIdsFrom [msiRsM]
          /\ RsAccepting
          /\ UpLockNatMsg
          /\ DownLockFree)
      :transition
         (do (n <-- getUpLockNatMsg;
                ursb <-- getUpLockIdxBack;
                st {{ ImplOStateIfc }}
                   --> (st.ost +#[implValueIdx <- n]
                               +#[implStatusIdx <- msiM],
                        removeRq (st.orq) upRq,
                        (ursb,
                         {| msg_id := setRs;
                            msg_type := MRs;
                            msg_value := VNat n |}) :: nil))).

    Definition childDownRqM: Rule ImplOStateIfc :=
      rule[7]
      :requires
         (MsgsFrom [pc]
          /\ MsgIdsFrom [msiDownRqM]
          /\ RqAccepting
          /\ DownLockFree
          /\ (fun (ost: OState ImplOStateIfc) orq mins =>
                ost#[implStatusIdx] >= msiS))
      :transition
         (fun (ost: OState ImplOStateIfc) orq mins =>
            (ost +#[implStatusIdx <- msiI],
             orq,
             [(cpRs, {| msg_id := msiDownRsM;
                        msg_type := MRs;
                        msg_value := VNat (ost#[implValueIdx]) |})])).

    Definition childEvictRqI: Rule ImplOStateIfc :=
      rule[8]
      :requires
         (MsgsFrom [ec]
          /\ MsgIdsFrom [evictRq]
          /\ RqAccepting
          /\ UpLockFree)
      :transition
         (do (msg <-- getFirstMsg;
                st {{ ImplOStateIfc }}
                   --> (st.ost,
                        addRq (st.orq) upRq msg [pc] ce,
                        [(cpRq, {| msg_id := msiRqI;
                                   msg_type := MRq;
                                   msg_value := VNat (st.ost#[implValueIdx])
                                |})]))).

    Definition childEvictRsI: Rule ImplOStateIfc :=
      rule[9]
      :requires
         (MsgsFromORq upRq
          /\ MsgIdsFrom [msiRsI]
          /\ RsAccepting
          /\ UpLocked
          /\ DownLockFree)
      :transition
         (do (ursb <-- getUpLockIdxBack;
                st {{ ImplOStateIfc }}
                   --> (st.ost +#[implStatusIdx <- msiI],
                        removeRq (st.orq) upRq,
                        [(ursb, {| msg_id := evictRs;
                                   msg_type := MRs;
                                   msg_value := VUnit |})]))).
      
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

      Section PerChild.
        Variable (ridxOfs: IdxT).
        Variables (cpRq pc cpRs' pc': IdxT).

        Definition parentNumOfRules := 5.

        Definition parentGetRqImm: Rule ImplOStateIfc :=
          rule[parentNumOfRules * ridxOfs + 0]
          :requires
             (MsgsFrom [cpRq]
              /\ MsgIdsFrom [msiRqS]
              /\ RqAccepting
              /\ UpLockFree
              /\ DownLockFree
              /\ (fun (ost: OState ImplOStateIfc) orq mins =>
                    ost#[implStatusIdx] >= msiS))
          :transition
             (fun (ost: OState ImplOStateIfc) orq mins =>
                (ost, orq,
                 [(pc, {| msg_id := msiRsS;
                          msg_type := MRs;
                          msg_value := VNat (ost#[implValueIdx]) |})])).

        Definition parentGetDownRqS: Rule ImplOStateIfc :=
          rule[parentNumOfRules * ridxOfs + 1]
          :requires
             (MsgsFrom [cpRq]
              /\ MsgIdsFrom [msiRqS]
              /\ RqAccepting
              /\ DownLockFree
              /\ (fun (ost: OState ImplOStateIfc) orq mins =>
                    ost#[implStatusIdx] = msiI))
          :transition
             (do (msg <-- getFirstMsg;
                    st {{ ImplOStateIfc }}
                       --> (st.ost,
                            addRq (st.orq) downRq msg [cpRs'] pc,
                            [(pc', {| msg_id := msiDownRqS;
                                      msg_type := MRq;
                                      msg_value := VNat (st.ost#[implValueIdx])
                                   |})]))).

        Definition parentSetRqImm: Rule ImplOStateIfc :=
          rule[parentNumOfRules * ridxOfs + 2]
          :requires
             (MsgsFrom [cpRq]
              /\ MsgIdsFrom [msiRqM]
              /\ RqAccepting
              /\ UpLockFree
              /\ DownLockFree
              /\ (fun (ost: OState ImplOStateIfc) orq mins =>
                    ost#[implStatusIdx] = msiM))
          :transition
             (fun (ost: OState ImplOStateIfc) orq mins =>
                (ost +#[implStatusIdx <- msiI],
                 orq,
                 [(pc, {| msg_id := msiRsM;
                          msg_type := MRs;
                          msg_value := VNat (ost#[implValueIdx]) |})])).

        Definition parentSetDownRqM: Rule ImplOStateIfc :=
          rule[parentNumOfRules * ridxOfs + 3]
          :requires
             (MsgsFrom [cpRq]
              /\ MsgIdsFrom [msiRqM]
              /\ RqAccepting
              /\ DownLockFree
              /\ (fun (ost: OState ImplOStateIfc) orq mins =>
                    ost#[implStatusIdx] <> msiM))
          :transition
             (do (msg <-- getFirstMsg;
                    st --> (st.ost,
                            addRq (st.orq) downRq msg [cpRs'] pc,
                            [(pc', {| msg_id := msiDownRqM;
                                      msg_type := MRq;
                                      msg_value := VUnit |})]))).

        Definition parentEvictRqImm: Rule ImplOStateIfc :=
          rule[parentNumOfRules * ridxOfs + 4]
          :requires
             (MsgsFrom [cpRq]
              /\ MsgIdsFrom [msiRqI]
              /\ RqAccepting
              /\ UpLockFree
              /\ DownLockFree
              /\ FirstNatMsg)
          :transition
             (do (n <-- getFirstNatMsg;
                    st {{ ImplOStateIfc }}
                       --> (st.ost +#[implValueIdx <- n]
                                   +#[implStatusIdx <- msiS],
                            st.orq,
                            [(pc, {| msg_id := msiRsI;
                                     msg_type := MRs;
                                     msg_value := VUnit |})]))).

        Definition parentRulesPerChild :=
          [parentGetRqImm; parentGetDownRqS;
             parentSetRqImm; parentSetDownRqM;
               parentEvictRqImm].
        
      End PerChild.
      
      Definition parentGetDownRsS: Rule ImplOStateIfc :=
        rule[parentNumOfRules * 2]
        :requires
           (MsgsFromORq downRq
            /\ MsgIdsFrom [msiDownRsS]
            /\ RsAccepting
            /\ FirstNatMsg
            /\ DownLocked)
        :transition
           (do (nv <-- getFirstNatMsg;
                  ursb <-- getDownLockIdxBack;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implValueIdx <- nv]
                                 +#[implStatusIdx <- msiS],
                          removeRq (st.orq) downRq,
                          [(ursb, {| msg_id := msiRsS;
                                     msg_type := MRs;
                                     msg_value := VNat nv |})]))).

      Definition parentSetDownRsM: Rule ImplOStateIfc :=
        rule[parentNumOfRules * 2 + 1]
        :requires
           (MsgsFromORq downRq
            /\ MsgIdsFrom [msiDownRsM]
            /\ RsAccepting
            /\ FirstNatMsg
            /\ DownLocked)
        :transition
           (do (n <-- getFirstNatMsg;
                  ursb <-- getDownLockIdxBack;
                  st {{ ImplOStateIfc }}
                     --> (st.ost +#[implStatusIdx <- msiI],
                          removeRq (st.orq) downRq,
                          [(ursb, {| msg_id := msiRsM;
                                     msg_type := MRs;
                                     msg_value := VNat n |})]))).
      
      Definition parentRules :=
        (parentRulesPerChild 0 c1pRq pc1 c2pRs pc2)
          ++ (parentRulesPerChild 1 c2pRq pc2 c1pRs pc1)
          ++ [parentGetDownRsS; parentSetDownRsM].

    End Rules.
    
    Definition parent: Object ImplOStateIfc :=
      {| obj_idx := parentIdx;
         obj_rules := parentRules;
         obj_rules_valid := ltac:(inds_valid_tac)
      |}.
    
  End Parent.

  Definition ext1Idx := 3.
  Definition ext2Idx := 4.

  Definition rootDmc (ridx: IdxT) :=
    {| dmc_me := ridx;
       dmc_ups := nil;
       dmc_downs := nil |}.

  Definition topo: DTree :=
    DNode
      (rootDmc parentIdx)
      [(DNode {| dmc_me := child1Idx;
                 dmc_ups := [c1pRq; c1pRs];
                 dmc_downs := [pc1] |}
              [DNode {| dmc_me := ext1Idx;
                        dmc_ups := [ec1; ecd1];
                        dmc_downs := [ce1] |} nil]);
         (DNode {| dmc_me := child2Idx;
                   dmc_ups := [c2pRq; c2pRs];
                   dmc_downs := [pc2] |}
                [DNode {| dmc_me := ext2Idx;
                          dmc_ups := [ec2; ecd2];
                          dmc_downs := [ce2] |} nil])].
  
  Definition impl: System ImplOStateIfc :=
    {| sys_objs :=
         [child child1Idx ec1 ce1 c1pRq c1pRs pc1;
            child child2Idx ec2 ce2 c2pRq c2pRs pc2;
            parent];
       sys_oinds_valid := ltac:(inds_valid_tac);
       sys_minds := [c1pRq; c1pRs; pc1; c2pRq; c2pRs; pc2];
       sys_merqs := [ec1; ec2];
       sys_merss := [ce1; ce2];
       sys_msg_inds_valid := ltac:(inds_valid_tac);
       sys_oss_inits := implInit
    |}.

End System.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

