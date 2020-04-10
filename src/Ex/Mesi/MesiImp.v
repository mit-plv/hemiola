Require Import Bool Vector List String Peano_dec Lia.
Require Import Common FMap HVector IndexSupport Syntax Semantics.
Require Import Topology RqRsTopo.
Require Import RqRsLang. Import RqRsNotations.

Require Import Ex.Spec Ex.SpecInds Ex.Template Ex.RuleTransform Ex.Mesi.
Require Import Ex.Mesi.Mesi.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Mesi.ImplOStateIfc. 

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
        :accepts mesiDownRsS
        :holding mesiRqS
        :from cidx.

      Definition liDownSRsUpDownRel: Rule :=
        rule.rsro[0~>4~>1]
        :requires (fun _ _ _ => True)
        :transition
           (!|ost, idm, rq, rsbTo|
            --> (ost +#[owned <- true]
                     +#[val <- msg_value (valOf idm)]
                     +#[status <- mesiS]
                     +#[dir <- setDirS [objIdxOf rsbTo; objIdxOf (idOf idm)]],
                 <| mesiRsS; msg_value (valOf idm) |>)).

      Definition liDownSRsUpUpOne: Rule :=
        rule.rsuo[0~>7~>0~~cidx]
        :accepts mesiDownRsS
        :holding mesiDownRqS
        :from cidx.

      Definition liDownSRsUpUpRel: Rule :=
        rule.rsro[0~>7~>1]
        :requires (fun _ _ _ => True)
        :transition
           (!|ost, idm, rq, rsbTo|
            --> (ost +#[val <- msg_value (valOf idm)]
                     +#[owned <- false]
                     +#[status <- mesiS]
                     +#[dir <- setDirS [objIdxOf (idOf idm)]],
                 <| mesiDownRsS; msg_value (valOf idm) |>)).

      Definition liDownIRsUpDownOne: Rule :=
        rule.rsuo[1~>6~>0~~cidx]
        :accepts mesiDownRsI
        :holding mesiRqM
        :from cidx.

      Definition liDownIRsUpDownRel: Rule :=
        rule.rsr[1~>6~>1]
        :requires (fun _ _ _ => True)
        :transition
           (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- mesiI] 
                     +#[dir <- setDirM (objIdxOf rsbTo)],
                 <| mesiRsM; O |>)).

      Definition liDownIRsUpUpOne: Rule :=
        rule.rsuo[1~>10~>0~~cidx]
        :accepts mesiDownRsI
        :holding mesiDownRqI
        :from cidx.

      Definition liDownIRsUpUpRel: Rule :=
        rule.rsr[1~>10~>1]
        :requires (fun _ _ _ => True)
        :transition
           (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- mesiI]
                     +#[dir <- setDirI],
                 <| mesiDownRsI; O |>)).

    End Li.

  End Rules.

  Section Objects.
    Variable (oidx: IdxT).

    Definition liRulesFromChild (cidx: IdxT): list Rule :=
      (Mesi.liRulesFromChild tr oidx cidx)
        ++ [liDownSRsUpDownOne cidx; liDownSRsUpUpOne cidx;
           liDownIRsUpDownOne cidx; liDownIRsUpUpOne cidx].

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
             ++ [liGetSRsDownDownS; liGetSRsDownDownE; liDownSRsUpDownRel;
                liDownSImm oidx; liDownSRqDownDownME tr oidx; liDownSRsUpUpRel]
             (** rules involved with [GetM] *)
             ++ [liGetMRsDownDownDirI; liGetMRsDownRqDownDirS tr oidx; liDownIRsUpDownRel;
                liDownIImm oidx; liDownIRqDownDownDirS tr oidx; liDownIRqDownDownDirME tr oidx;
                liDownIRsUpUpRel]
             (** rules involved with [Put] *)
             ++ [liInvRqUpUp oidx; liInvRqUpUpWB oidx; liInvRsDownDown; liPushImm];
         obj_rules_valid := _ |}.
    Next Obligation.
      solve_inds_NoDup disc_child_inds_disj.
    Qed.

    Definition memRulesFromChild (cidx: IdxT): list Rule :=
      (Mesi.memRulesFromChild tr oidx cidx)
        ++ [liDownSRsUpDownOne cidx; liDownSRsUpUpOne cidx;
           liDownIRsUpDownOne cidx; liDownIRsUpUpOne cidx].

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
     liDownIRsUpDownOne liDownIRsUpDownRel
     liDownIRsUpUpOne liDownIRsUpUpRel: MesiRules.
