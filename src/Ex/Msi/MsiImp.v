Require Import Bool Vector List String Peano_dec Lia.
Require Import Common FMap HVector IndexSupport Syntax Semantics.
Require Import Topology RqRsTopo.
Require Import RqRsLang. Import RqRsNotations.

Require Import Ex.Spec Ex.SpecInds Ex.Template Ex.RuleTransform Ex.Msi.
Require Import Ex.Msi.Msi.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Msi.ImplOStateIfc.

Section System.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo := fst (tree2Topo tr 0).
  Let cifc := snd (tree2Topo tr 0).

  Section Rules.
    Variables (oidx cidx: IdxT).

    (** L1 caches remain the same. *)

    Section Li.

      Definition liDownSRsUpDownOne: Rule :=
        rule.rsuo[0~>4~>0~~cidx]
        :accepts msiDownRsS
        :holding msiRqS
        :from cidx.

      Definition liDownSRsUpDownRel: Rule :=
        rule.rsro[0~>4~>1]
        :holding msiRqS
        :requires (fun _ _ _ => True)
        :transition
           (!|ost, idm, rq, rsbTo|
            --> (ost +#[owned <- true]
                     +#[val <- msg_value (valOf idm)]
                     +#[status <- msiS]
                     +#[dir <- setDirS [objIdxOf rsbTo; objIdxOf (idOf idm)]],
                 <| msiRsS; msg_value (valOf idm) |>)).

      Definition liDownSRsUpUpOne: Rule :=
        rule.rsuo[0~>7~>0~~cidx]
        :accepts msiDownRsS
        :holding msiDownRqS
        :from cidx.

      Definition liDownSRsUpUpRel: Rule :=
        rule.rsro[0~>7~>1]
        :holding msiDownRqS
        :requires (fun _ _ _ => True)
        :transition
           (!|ost, idm, rq, rsbTo|
            --> (ost +#[val <- msg_value (valOf idm)]
                     +#[owned <- false]
                     +#[status <- msiS]
                     +#[dir <- setDirS [objIdxOf (idOf idm)]],
                 <| msiDownRsS; msg_value (valOf idm) |>)).

      Definition liDownIRsUpDownSOne: Rule :=
        rule.rsuo[1~>6~>0~>0~~cidx]
        :accepts msiDownRsIS
        :holding msiRqM
        :from cidx.

      Definition liDownIRsUpDownMOne: Rule :=
        rule.rsuo[1~>6~>0~>1~~cidx]
        :accepts msiDownRsIM
        :holding msiRqM
        :from cidx.

      Definition liDownIRsUpDownRel: Rule :=
        rule.rsr[1~>6~>1]
        :holding msiRqM
        :requires (fun _ _ _ => True)
        :transition
           (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- msiI]
                     +#[dir <- setDirM (objIdxOf rsbTo)],
                 <| msiRsM; O |>)).

      Definition liDownIRsUpUpSOne: Rule :=
        rule.rsuo[1~>10~>0~>0~~cidx]
        :accepts msiDownRsIS
        :holding msiDownRqIS
        :from cidx.

      Definition liDownIRsUpUpMOne: Rule :=
        rule.rsuo[1~>10~>0~>1~~cidx]
        :accepts msiDownRsIM
        :holding msiDownRqIM
        :from cidx.

      Definition liDownIRsUpUpSRel: Rule :=
        rule.rsr[1~>10~>1~>0]
        :holding msiDownRqIS
        :requires (fun _ _ _ => True)
        :transition
           (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- msiI]
                     +#[dir <- setDirI],
                 <| msiDownRsIS; O |>)).

      Definition liDownIRsUpUpMRel: Rule :=
        rule.rsr[1~>10~>1~>1]
        :holding msiDownRqIM
        :requires (fun _ _ _ => True)
        :transition
           (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- msiI]
                     +#[dir <- setDirI],
                 <| msiDownRsIM; O |>)).

    End Li.

  End Rules.

  Section Objects.
    Variable (oidx: IdxT).

    Definition liRulesFromChild (cidx: IdxT): list Rule :=
      (Msi.liRulesFromChild tr oidx cidx)
        ++ [liDownSRsUpDownOne cidx; liDownSRsUpUpOne cidx;
           liDownIRsUpDownSOne cidx; liDownIRsUpDownMOne cidx;
           liDownIRsUpUpSOne cidx; liDownIRsUpUpMOne cidx].

    Definition liRulesFromChildren (coinds: list IdxT): list Rule :=
      List.concat (map liRulesFromChild coinds).

    Hint Unfold liRulesFromChild liRulesFromChildren: RuleConds.

    Ltac disc_child_inds_disj :=
      pose proof (tree2Topo_TreeTopo tr 0);
      try match goal with
          | [Hn: ?n1 <> ?n2,
                 H1: nth_error (subtreeChildrenIndsOf ?topo ?sidx) ?n1 = Some _,
                     H2: nth_error (subtreeChildrenIndsOf ?topo ?sidx) ?n2 = Some _ |- _] =>
            eapply TreeTopo_children_inds_disj in Hn; eauto; destruct Hn
          end.

    Program Definition li: Object :=
      {| obj_idx := oidx;
         obj_rules :=
           (liRulesFromChildren (subtreeChildrenIndsOf topo oidx))
             (** rules involved with [GetS] *)
             ++ [liGetSRsDownDown; liDownSRsUpDownRel;
                liDownSImm oidx; liDownSRqDownDownM tr oidx; liDownSRsUpUpRel]
             (** rules involved with [GetM] *)
             ++ [liGetMRsDownDownDirI; liGetMRsDownRqDownDirS tr oidx; liDownIRsUpDownRel;
                liDownIImmS oidx; liDownIImmM oidx;
                liDownIRqDownDownDirS tr oidx; liDownIRqDownDownDirM tr oidx;
                liDownIRsUpUpSRel; liDownIRsUpUpMRel]
             (** rules involved with [Put] *)
             ++ [liInvRqUpUp oidx; liInvRqUpUpWB oidx; liInvRsDownDown; liPushImm];
         obj_rules_valid := _ |}.
    Next Obligation.
      solve_inds_NoDup disc_child_inds_disj.
    Qed.

    Definition memRulesFromChild (cidx: IdxT): list Rule :=
      (Msi.memRulesFromChild tr oidx cidx)
        ++ [liDownSRsUpDownOne cidx; liDownIRsUpDownSOne cidx; liDownIRsUpDownMOne cidx].

    Definition memRulesFromChildren (coinds: list IdxT): list Rule :=
      List.concat (map memRulesFromChild coinds).

    Hint Unfold memRulesFromChild memRulesFromChildren: RuleConds.

    Program Definition mem: Object :=
      {| obj_idx := oidx;
         obj_rules :=
           (memRulesFromChildren (subtreeChildrenIndsOf topo oidx))
             ++ [liDownSRsUpDownRel; liDownIRsUpDownRel];
         obj_rules_valid := _ |}.
    Next Obligation.
      solve_inds_NoDup disc_child_inds_disj.
    Qed.

  End Objects.

  Program Definition impl: System :=
    {| sys_objs :=
         ((mem (rootOf topo) :: map li (tl cifc.(c_li_indices)))
            ++ map l1 cifc.(c_l1_indices));
       sys_oinds_valid := _;
       sys_minds := cifc.(c_minds);
       sys_merqs := cifc.(c_merqs);
       sys_merss := cifc.(c_merss);
       sys_msg_inds_valid := _;
       sys_oss_inits := implOStatesInit tr;
       sys_orqs_inits := implORqsInit tr |}.
  Next Obligation.
    unfold mem, li, l1.
    rewrite map_app.
    do 2 rewrite map_trans.
    do 2 rewrite map_id.
    unfold topo, cifc.
    rewrite app_comm_cons.
    rewrite <-c_li_indices_head_rootOf by assumption.
    apply tree2Topo_WfCIfc.
  Qed.
  Next Obligation.
    apply tree2Topo_WfCIfc.
  Qed.

End System.

Hint Unfold liDownSRsUpDownOne liDownSRsUpDownRel
     liDownSRsUpUpOne liDownSRsUpUpRel
     liDownIRsUpDownSOne liDownIRsUpDownMOne
     liDownIRsUpDownRel
     liDownIRsUpUpSOne liDownIRsUpUpMOne
     liDownIRsUpUpSRel liDownIRsUpUpMRel: MsiRules.
