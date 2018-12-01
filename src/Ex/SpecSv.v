Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport Syntax Semantics StepT.
Require Import Topology RqRs.

Require Import Spec.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Section System.
  Variable numC: nat. (* if [numC = 0], then the system has channels for a single child. *)

  Definition erq (i: nat) := 2 * i.
  Definition ers (i: nat) := 2 * i + 1.

  Section Spec.

    Definition specIdx := 0.

    Definition SpecOStateIfc: OStateIfc :=
      {| ost_sz := 1;
         ost_ty := [nat:Type]%vector |}.
    Definition specValueIdx: Fin.t 1 := Fin.F1.
    Definition specInit: OStates SpecOStateIfc :=
      [specIdx <- hvcons 0 hvnil].
    
    Section PerChn.
      Variable ridxOfs: nat.
      Variables (erq ers: nat).

      Definition specNumOfRules := 2.

      Definition specGetRq: Rule SpecOStateIfc :=
        {| rule_idx := specNumOfRules * ridxOfs + 0;
           rule_msg_ids_from := [getRq];
           rule_msg_ids_to := [getRs];
           rule_msg_type_from := MRq;
           rule_msg_type_to := MRs;
           rule_precond := MsgsFrom [erq];
           rule_trs :=
             fun (ost: OState SpecOStateIfc) orq mins =>
               (ost, orq,
                [(ers, {| msg_id := getRs;
                          msg_type := MRs;
                          msg_value := VNat (ost#[specValueIdx])
                       |})])
        |}.

      Definition specSetRq: Rule SpecOStateIfc :=
        {| rule_idx := specNumOfRules * ridxOfs + 1;
           rule_msg_ids_from := [setRq];
           rule_msg_ids_to := [setRs];
           rule_msg_type_from := MRq;
           rule_msg_type_to := MRs;
           rule_precond := MsgsFrom [erq];
           rule_trs :=
             fun (ost: OState SpecOStateIfc) orq mins =>
               ((hd_error mins) >>=[ost]
                                (fun idm =>
                                   match msg_value (valOf idm) with
                                   | VNat n => ost+#[specValueIdx <- n]
                                   | _ => ost
                                   end),
                orq,
                [(ers, {| msg_id := setRs;
                          msg_type := MRs;
                          msg_value := VUnit |})])
        |}.

    End PerChn.
    
    Definition specRulesI (i: nat): list (Rule SpecOStateIfc) :=
      [specGetRq i (erq i) (ers i); specSetRq i (erq i) (ers i)].

    Fixpoint specRules (i: nat): list (Rule SpecOStateIfc) :=
      match i with
      | O => specRulesI O
      | S i' => (specRulesI i) ++ (specRules i')
      end.

    Lemma specObj_obj_rules_valid:
      forall i, NoDup (map (@rule_idx _) (specRules i)).
    Proof.
    Admitted.

    Definition specObj: Object SpecOStateIfc :=
      {| obj_idx := specIdx;
         obj_rules := specRules numC;
         obj_rules_valid := specObj_obj_rules_valid numC
      |}.

    Fixpoint specMerqs (i: nat): list IdxT :=
      match i with
      | O => [erq O]
      | S i' => erq i :: specMerqs i'
      end.

    Fixpoint specMerss (i: nat): list IdxT :=
      match i with
      | O => [ers O]
      | S i' => ers i :: specMerss i'
      end.

    Lemma spec_msg_inds_valid:
      forall i, NoDup (nil ++ specMerqs i ++ specMerss i).
    Proof.
    Admitted.

    Definition spec: System SpecOStateIfc :=
      {| sys_objs := [specObj];
         sys_oinds_valid := ltac:(inds_valid_tac);
         sys_minds := nil;
         sys_merqs := specMerqs numC;
         sys_merss := specMerss numC;
         sys_msg_inds_valid := spec_msg_inds_valid numC;
         sys_oss_inits := specInit;
         sys_orqs_inits := []
      |}.

  End Spec.

End System.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

