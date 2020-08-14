Require Import Bool Vector List String PeanoNat Lia.
Require Import Common FMap HVector IndexSupport Syntax Semantics.
Require Import Topology RqRsLang.

Require Import Ex.Spec.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Global Instance NatDecValue: DecValue :=
  {| t_type := nat;
     t_default := O;
     t_eq_dec := Nat.eq_dec
  |}.

Section System.
  Variable numC: nat. (* if [numC = 0], then the system has channels for a single child. *)

  Definition erq (i: nat): IdxT := extendIdx 0 [i].
  Definition ers (i: nat): IdxT := extendIdx 1 [i].

  Instance SpecOStateIfc: OStateIfc :=
    {| ost_sz := 1;
       ost_ty := [nat:Type]%vector |}.

  Section Spec.

    Definition specIdx: IdxT := 0.

    Definition specValueIdx: Fin.t 1 := Fin.F1.
    Definition specOStatesInit: OStates :=
      [specIdx <- hvcons 0 hvnil].
    Definition specORqsInit: ORqs Msg :=
      [specIdx <- []].

    Section PerChn.
      Variable i: nat.

      Definition specGetRq: Rule :=
        {| rule_idx := [i; 0];
           rule_precond :=
             MsgsFrom [erq i]
             /\oprec MsgIdsFrom [getRq]
             /\oprec RqAccepting;
           rule_trs :=
             fun ost orq mins =>
               (ost, orq,
                [(ers i, {| msg_id := getRs;
                            msg_type := MRs;
                            msg_addr := tt;
                            msg_value := ost#[specValueIdx]
                         |})])
        |}.

      Definition specSetRq: Rule :=
        {| rule_idx := [i; 1];
           rule_precond :=
             MsgsFrom [erq i]
             /\oprec MsgIdsFrom [setRq]
             /\oprec RqAccepting;
           rule_trs :=
             fun (ost: OState) orq mins =>
               ((hd_error mins)
                  >>=[ost] (fun idm =>
                              ost+#[specValueIdx <- msg_value (valOf idm)]),
                orq,
                [(ers i, {| msg_id := setRs;
                            msg_type := MRs;
                            msg_addr := tt;
                            msg_value := O |})])
        |}.

      Definition specEvictRq: Rule :=
        {| rule_idx := [i; 2];
           rule_precond :=
             MsgsFrom [erq i]
             /\oprec MsgIdsFrom [evictRq]
             /\oprec RqAccepting;
           rule_trs :=
             fun (ost: OState) orq mins =>
               (ost, orq,
                [(ers i, {| msg_id := evictRs;
                            msg_type := MRs;
                            msg_addr := tt;
                            msg_value := O
                         |})])
        |}.

    End PerChn.

    Definition specRulesI (i: nat): list (Rule) :=
      [specGetRq i; specSetRq i; specEvictRq i].

    Fixpoint specRules (i: nat): list (Rule) :=
      match i with
      | O => specRulesI O
      | S i' => (specRulesI i) ++ (specRules i')
      end.

    Lemma specRules_head:
      forall i,
        SubList
          (map idxHd (map rule_idx (specRules i)))
          (nat_seq_rev i).
    Proof.
      induction i; simpl; intros; [solve_SubList|].
      repeat (apply SubList_cons; [left; reflexivity|]).
      apply SubList_cons_right.
      assumption.
    Qed.

    Lemma specObj_obj_rules_valid:
      forall i, NoDup (map rule_idx (specRules i)).
    Proof.
      induction i; [solve_NoDup|].
      simpl.
      apply NoDup_DisjList with (l1:= [[S i; 0]; [S i; 1]; [S i; 2]]).
      - solve_NoDup.
      - assumption.
      - apply idx_DisjList_head; simpl.
        eapply DisjList_comm, DisjList_SubList.
        * apply specRules_head.
        * apply DisjList_comm.
          repeat (apply (DisjList_cons_inv Nat.eq_dec);
                  [|apply nat_seq_rev_not_in; lia]).
          apply DisjList_nil_1.
    Qed.

    Definition specObj: Object :=
      {| obj_idx := specIdx;
         obj_rules := specRules numC;
         obj_rules_valid := specObj_obj_rules_valid numC
      |}.

    Definition specMerqs (i: nat): list IdxT :=
      extendInds 0 (liftInds (nat_seq_rev i)).

    Definition specMerss (i: nat): list IdxT :=
      extendInds 1 (liftInds (nat_seq_rev i)).

    Lemma spec_msg_inds_valid:
      forall i, NoDup (specMerqs i ++ specMerss i).
    Proof.
      intros.
      apply NoDup_DisjList.
      - apply extendIdx_NoDup.
        apply liftInds_NoDup.
        apply nat_seq_rev_NoDup.
      - apply extendIdx_NoDup.
        apply liftInds_NoDup.
        apply nat_seq_rev_NoDup.
      - apply idx_DisjList_head.
        eapply DisjList_SubList; [apply extendInds_idxHd_SubList|].
        eapply DisjList_comm, DisjList_SubList; [apply extendInds_idxHd_SubList|].
        apply (DisjList_cons_inv Nat.eq_dec).
        + apply DisjList_nil_1.
        + solve_not_in.
    Qed.

    Definition spec: System :=
      {| sys_objs := [specObj];
         sys_oinds_valid := ltac:(inds_valid_tac);
         sys_minds := nil;
         sys_merqs := specMerqs numC;
         sys_merss := specMerss numC;
         sys_msg_inds_valid := spec_msg_inds_valid numC;
         sys_oss_inits := specOStatesInit;
         sys_orqs_inits := specORqsInit
      |}.

  End Spec.

End System.

Close Scope list.
Close Scope hvec.
Close Scope fmap.
