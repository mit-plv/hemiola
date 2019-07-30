Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport Syntax Semantics.
Require Import Topology RqRsTopo.
Require Import RqRsLang. Import RqRsNotations.

Require Import Ex.Spec Ex.SpecSv Ex.Msi.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Section System.

  Definition ec1 := erq 0.
  Definition ce1 := ers 0.
  Definition ec2 := erq 1.
  Definition ce2 := ers 1.
  Definition ecd1: IdxT := 4.
  Definition ecd2: IdxT := 5.
  Definition c1pRq: IdxT := 6.
  Definition c1pRs: IdxT := 7.
  Definition pc1: IdxT := 8.
  Definition c2pRq: IdxT := 9.
  Definition c2pRs: IdxT := 10.
  Definition pc2: IdxT := 11.
    
  Definition parentIdx: IdxT := 0.
  Definition child1Idx: IdxT := 1.
  Definition child2Idx: IdxT := 2.
  Definition ext1Idx: IdxT := 3.
  Definition ext2Idx: IdxT := 4.

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
  
  Definition implValueIdx: Fin.t 3 := F1.
  Definition implStatusIdx: Fin.t 3 := F2.
  Definition implDirIdx: Fin.t 3 := F3.

  Definition DirT: Type := MSI * MSI.
  Definition dirInit: DirT := (msiS, msiS).

  Definition getDir (cidx: IdxT) (dir: DirT): MSI :=
    if idx_dec cidx child1Idx then fst dir else snd dir.

  Definition setDir (cidx: IdxT) (stt: MSI) (dir: DirT): DirT :=
    if idx_dec cidx child1Idx
    then (stt, snd dir)
    else (fst dir, stt).
  
  Instance ImplOStateIfc: OStateIfc :=
    {| ost_ty := [nat:Type; MSI:Type; DirT]%vector |}.
  
  Definition implOStatesInit: OStates :=
    [parentIdx <- (0, (msiS, (dirInit, tt)))]
    +[child1Idx <- (0, (msiS, (dirInit, tt)))]
    +[child2Idx <- (0, (msiS, (dirInit, tt)))].
  Definition implORqsInit: ORqs Msg :=
    [parentIdx <- []]
    +[child1Idx <- []]
    +[child2Idx <- []].

  Section Child.
    Variable (coidx: IdxT).
    Variables (ec ce cpRq cpRs pc: IdxT).

    Definition childGetRqImm: Rule :=
      rule[0]
      :requires
         (MsgsFrom [ec]
          /\ MsgIdsFrom [getRq]
          /\ RqAccepting
          /\ UpLockFree
          /\ DownLockFree
          /\ (fun ost orq mins =>
                ost#[implStatusIdx] >= msiS))
      :transition
         (fun ost orq mins =>
            (ost, orq,
             [(ce, {| msg_id := getRs;
                      msg_type := MRs;
                      msg_value := VNat (ost#[implValueIdx])
                   |})])).
    
    Definition childGetRqS: Rule :=
      rule[1]
      :requires
         (MsgsFrom [ec]
          /\ MsgIdsFrom [getRq]
          /\ RqAccepting
          /\ UpLockFree
          /\ (fun ost orq mins =>
                ost#[implStatusIdx] = msiI))
      :transition
         (do (msg <-- getFirstMsg;
                st --> (st.ost,
                        addRq (st.orq) upRq msg [pc] ce,
                        [(cpRq, {| msg_id := msiRqS;
                                   msg_type := MRq;
                                   msg_value := VUnit |})]))).
    
    Definition childGetRsS: Rule :=
      rule[2]
      :requires
         (MsgsFromORq upRq
          /\ MsgIdsFrom [msiRsS]
          /\ RsAccepting
          /\ FirstNatMsg
          /\ UpLockMsgId MRq Spec.getRq
          /\ DownLockFree)
      :transition
         (do (n <-- getFirstNatMsg;
                ursb <-- getUpLockIdxBack;
                st --> (st.ost +#[implValueIdx <- n]
                               +#[implStatusIdx <- msiS],
                        removeRq (st.orq) upRq,
                        [(ursb, {| msg_id := getRs;
                                   msg_type := MRs;
                                   msg_value := VNat n |})]))).

    Definition childDownRqS: Rule :=
      rule[3]
      :requires
         (MsgsFrom [pc]
          /\ MsgIdsFrom [msiDownRqS]
          /\ RqAccepting
          /\ DownLockFree
          /\ (fun ost orq mins =>
                ost#[implStatusIdx] >= msiS))
      :transition
         (fun ost orq mins =>
            (ost+#[implStatusIdx <- msiS],
             orq,
             [(cpRs, {| msg_id := msiDownRsS;
                        msg_type := MRs;
                        msg_value := VNat (ost#[implValueIdx]) |})])).

    Definition childSetRqImm: Rule :=
      rule[4]
      :requires
         (MsgsFrom [ec]
          /\ MsgIdsFrom [setRq]
          /\ RqAccepting
          /\ UpLockFree
          /\ DownLockFree
          /\ FirstNatMsg
          /\ (fun ost orq mins =>
                ost#[implStatusIdx] = msiM))
      :transition
         (do (n <-- getFirstNatMsg;
                st --> (st.ost +#[implValueIdx <- n],
                        st.orq,
                        [(ce, {| msg_id := setRs;
                                 msg_type := MRs;
                                 msg_value := VUnit |})]))).

    Definition childSetRqM: Rule :=
      rule[5]
      :requires
         (MsgsFrom [ec]
          /\ MsgIdsFrom [setRq]
          /\ RqAccepting
          /\ UpLockFree
          /\ (fun ost orq mins =>
                ost#[implStatusIdx] <= msiS))
      :transition
         (do (msg <-- getFirstMsg;
                st --> (st.ost,
                        addRq (st.orq) upRq msg [pc] ce,
                        [(cpRq, {| msg_id := msiRqM;
                                   msg_type := MRq;
                                   msg_value := VUnit |})]))).

    Definition childSetRsM: Rule :=
      rule[6]
      :requires
         (MsgsFromORq upRq
          /\ MsgIdsFrom [msiRsM]
          /\ RsAccepting
          /\ UpLockNatMsg
          /\ UpLockMsgId MRq Spec.setRq
          /\ DownLockFree)
      :transition
         (do (n <-- getUpLockNatMsg;
                ursb <-- getUpLockIdxBack;
                st --> (st.ost +#[implValueIdx <- n]
                               +#[implStatusIdx <- msiM],
                        removeRq (st.orq) upRq,
                        (ursb,
                         {| msg_id := setRs;
                            msg_type := MRs;
                            msg_value := VUnit |}) :: nil))).

    Definition childDownRqI: Rule :=
      rule[7]
      :requires
         (MsgsFrom [pc]
          /\ MsgIdsFrom [msiDownRqI]
          /\ RqAccepting
          /\ DownLockFree
          /\ (fun ost orq mins =>
                ost#[implStatusIdx] >= msiS))
      :transition
         (fun ost orq mins =>
            (ost +#[implStatusIdx <- msiI],
             orq,
             [(cpRs, {| msg_id := msiDownRsI;
                        msg_type := MRs;
                        msg_value := VUnit |})])).

    Definition childEvictRqI: Rule :=
      rule[8]
      :requires
         (MsgsFrom [ec]
          /\ MsgIdsFrom [evictRq]
          /\ RqAccepting
          /\ UpLockFree)
      :transition
         (do (msg <-- getFirstMsg;
                st --> (st.ost,
                        addRq (st.orq) upRq msg [pc] ce,
                        [(cpRq, {| msg_id := msiRqI;
                                   msg_type := MRq;
                                   msg_value := VNat (st.ost#[implValueIdx])
                                |})]))).

    Definition childEvictRsI: Rule :=
      rule[9]
      :requires
         (MsgsFromORq upRq
          /\ MsgIdsFrom [msiRsI]
          /\ RsAccepting
          /\ UpLockMsgId MRq Spec.evictRq
          /\ DownLockFree)
      :transition
         (do (ursb <-- getUpLockIdxBack;
                st --> (st.ost +#[implStatusIdx <- msiI],
                        removeRq (st.orq) upRq,
                        [(ursb, {| msg_id := evictRs;
                                   msg_type := MRs;
                                   msg_value := VUnit |})]))).

    Definition child: Object :=
      {| obj_idx := coidx;
         obj_rules :=
           [childGetRqImm; childGetRqS; childGetRsS; childDownRqS;
              childSetRqImm; childSetRqM; childSetRsM; childDownRqI;
                childEvictRqI; childEvictRsI];
         obj_rules_valid := ltac:(inds_valid_tac) |}.

  End Child.
    
  Section Parent.

    Section Rules.

      Section PerChild.
        Variable (ridxOfs: nat).
        Variables (childIdx childIdx': IdxT)
                  (cpRq pc cpRs' pc': IdxT).

        Definition parentNumOfRules := 10.

        Definition parentGetRqImm: Rule :=
          rule[parentNumOfRules * ridxOfs + 0]
          :requires
             (MsgsFrom [cpRq]
              /\ MsgIdsFrom [msiRqS]
              /\ RqAccepting
              /\ UpLockFree
              /\ DownLockFree
              /\ (fun ost orq mins =>
                    msiS <= ost#[implStatusIdx]))
          :transition
             (fun ost orq mins =>
                (ost +#[implStatusIdx <- msiS]
                     +#[implDirIdx <- setDir childIdx msiS ost#[implDirIdx]],
                 orq,
                 [(pc, {| msg_id := msiRsS;
                          msg_type := MRs;
                          msg_value := VNat (ost#[implValueIdx]) |})])).

        Definition parentGetDownRqS: Rule :=
          rule[parentNumOfRules * ridxOfs + 1]
          :requires
             (MsgsFrom [cpRq]
              /\ MsgIdsFrom [msiRqS]
              /\ RqAccepting
              /\ DownLockFree
              /\ (fun ost orq mins =>
                    getDir childIdx ost#[implDirIdx] = msiI)
              /\ (fun ost orq mins =>
                    ost#[implStatusIdx] = msiI))
          :transition
             (do (msg <-- getFirstMsg;
                    st --> (st.ost,
                            addRq (st.orq) downRq msg [cpRs'] pc,
                            [(pc', {| msg_id := msiDownRqS;
                                      msg_type := MRq;
                                      msg_value := VNat (st.ost#[implValueIdx])
                                   |})]))).

        Definition parentSetRqImm: Rule :=
          rule[parentNumOfRules * ridxOfs + 2]
          :requires
             (MsgsFrom [cpRq]
              /\ MsgIdsFrom [msiRqM]
              /\ RqAccepting
              /\ UpLockFree
              /\ DownLockFree
              /\ (fun ost orq mins =>
                    getDir childIdx' ost#[implDirIdx] = msiI))
          :transition
             (fun ost orq mins =>
                (ost +#[implStatusIdx <- msiI]
                     +#[implDirIdx <- setDir childIdx msiM ost#[implDirIdx]],
                 orq,
                 [(pc, {| msg_id := msiRsM;
                          msg_type := MRs;
                          msg_value := VUnit |})])).

        Definition parentSetDownRqI: Rule :=
          rule[parentNumOfRules * ridxOfs + 3]
          :requires
             (MsgsFrom [cpRq]
              /\ MsgIdsFrom [msiRqM]
              /\ RqAccepting
              /\ DownLockFree
              /\ (fun ost orq mins =>
                    msiS <= getDir childIdx' ost#[implDirIdx]))
          :transition
             (do (msg <-- getFirstMsg;
                    st --> (st.ost,
                            addRq (st.orq) downRq msg [cpRs'] pc,
                            [(pc', {| msg_id := msiDownRqI;
                                      msg_type := MRq;
                                      msg_value := VUnit |})]))).

        Definition parentGetDownRsS: Rule :=
          rule[parentNumOfRules * ridxOfs + 4]
          :requires
             (MsgsFromRsUp topo [childIdx']
              /\ MsgIdsFrom [msiDownRsS]
              /\ RsAccepting
              /\ FirstNatMsg
              /\ DownLockMsgId MRq msiDownRqS)
          :transition
             (do (nv <-- getFirstNatMsg;
                    ursb <-- getDownLockIdxBack;
                    st --> (st.ost +#[implValueIdx <- nv]
                                   +#[implStatusIdx <- msiS]
                                   +#[implDirIdx <- setDir childIdx' msiS (setDir childIdx msiS (st.ost)#[implDirIdx])],
                            removeRq (st.orq) downRq,
                            [(ursb, {| msg_id := msiRsS;
                                       msg_type := MRs;
                                       msg_value := VNat nv |})]))).

        Definition parentSetDownRsI: Rule :=
          rule[parentNumOfRules * ridxOfs + 5]
          :requires
             (MsgsFromRsUp topo [childIdx']
              /\ MsgIdsFrom [msiDownRsI]
              /\ RsAccepting
              /\ FirstNatMsg
              /\ DownLockMsgId MRq msiDownRqI)
          :transition
             (do (ursb <-- getDownLockIdxBack;
                    st --> (st.ost +#[implStatusIdx <- msiI]
                                   +#[implDirIdx <- (setDir childIdx' msiI
                                                            (setDir childIdx msiM
                                                                    (st.ost)#[implDirIdx]))],
                            removeRq (st.orq) downRq,
                            [(ursb, {| msg_id := msiRsM;
                                       msg_type := MRs;
                                       msg_value := VUnit |})]))).

        Definition parentEvictRqImmI: Rule :=
          rule[parentNumOfRules * ridxOfs + 6]
          :requires
             (MsgsFrom [cpRq]
              /\ MsgIdsFrom [msiRqI]
              /\ RqAccepting
              /\ UpLockFree
              /\ DownLockFree
              /\ (fun ost orq mins =>
                    getDir childIdx ost#[implDirIdx] = msiI))
          :transition
             (do (st --> (st.ost,
                          st.orq,
                          [(pc, {| msg_id := msiRsI;
                                   msg_type := MRs;
                                   msg_value := VUnit |})]))).
        
        Definition parentEvictRqImmS: Rule :=
          rule[parentNumOfRules * ridxOfs + 7]
          :requires
             (MsgsFrom [cpRq]
              /\ MsgIdsFrom [msiRqI]
              /\ RqAccepting
              /\ UpLockFree
              /\ DownLockFree
              /\ (fun ost orq mins =>
                    getDir childIdx ost#[implDirIdx] = msiS)
              /\ (fun ost orq mins =>
                    getDir childIdx' ost#[implDirIdx] = msiS))
          :transition
             (do (st --> (st.ost +#[implDirIdx <- (setDir childIdx msiI
                                                          (st.ost)#[implDirIdx])],
                          st.orq,
                          [(pc, {| msg_id := msiRsI;
                                   msg_type := MRs;
                                   msg_value := VUnit |})]))).

        Definition parentEvictRqImmLastS: Rule :=
          rule[parentNumOfRules * ridxOfs + 8]
          :requires
             (MsgsFrom [cpRq]
              /\ MsgIdsFrom [msiRqI]
              /\ RqAccepting
              /\ UpLockFree
              /\ DownLockFree
              /\ (fun ost orq mins =>
                    getDir childIdx ost#[implDirIdx] = msiS)
              /\ (fun ost orq mins =>
                    getDir childIdx' ost#[implDirIdx] = msiI))
          :transition
             (do (st --> (st.ost +#[implStatusIdx <- msiM]
                                 +#[implDirIdx <- (setDir childIdx msiI
                                                          (st.ost)#[implDirIdx])],
                          st.orq,
                          [(pc, {| msg_id := msiRsI;
                                   msg_type := MRs;
                                   msg_value := VUnit |})]))).

        Definition parentEvictRqImmM: Rule :=
          rule[parentNumOfRules * ridxOfs + 9]
          :requires
             (MsgsFrom [cpRq]
              /\ MsgIdsFrom [msiRqI]
              /\ RqAccepting
              /\ UpLockFree
              /\ DownLockFree
              /\ FirstNatMsg
              /\ (fun ost orq mins =>
                    getDir childIdx ost#[implDirIdx] = msiM))
          :transition
             (do (n <-- getFirstNatMsg;
                    st --> (st.ost +#[implValueIdx <- n]
                                   +#[implStatusIdx <- msiM]
                                   +#[implDirIdx <- (setDir childIdx msiI
                                                            (st.ost)#[implDirIdx])],
                            st.orq,
                            [(pc, {| msg_id := msiRsI;
                                     msg_type := MRs;
                                     msg_value := VUnit |})]))).

        Definition parentRulesPerChild :=
          [parentGetRqImm; parentGetDownRqS;
             parentSetRqImm; parentSetDownRqI;
               parentGetDownRsS; parentSetDownRsI;
                 parentEvictRqImmI; parentEvictRqImmS; parentEvictRqImmLastS;
                   parentEvictRqImmM].

        (* just checking *)
        Definition parentNumOfRules_ok:
          parentNumOfRules = List.length parentRulesPerChild := eq_refl.
        
      End PerChild.
      
      Definition parentRules :=
        (parentRulesPerChild 0 child1Idx child2Idx c1pRq pc1 c2pRs pc2)
          ++ (parentRulesPerChild 1 child2Idx child1Idx c2pRq pc2 c1pRs pc1).

    End Rules.

    Definition parent: Object :=
      {| obj_idx := parentIdx;
         obj_rules := parentRules;
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
       sys_merqs := [ec2; ec1];
       sys_merss := [ce2; ce1];
       sys_msg_inds_valid := ltac:(inds_valid_tac);
       sys_oss_inits := implOStatesInit;
       sys_orqs_inits := implORqsInit
    |}.

End System.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

