Require Import Peano_dec List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

(** Useful invariants on top of [RqRsSys] *)

Ltac inv_steps :=
  repeat
    match goal with
    | [H: steps _ _ _ _ _ |- _] => inv H
    end.

Ltac inv_step :=
  repeat
    match goal with
    | [H: step_m _ _ (RlblInt _ _ _ _) _ |- _] => inv H
    | [H: {| bst_oss := _; bst_orqs := _; bst_msgs := _ |} =
          {| bst_oss := _; bst_orqs := _; bst_msgs := _ |} |- _] => inv H
    end.

Ltac red_obj_rule :=
  repeat
    match goal with
    | [H: step_m _ _ (RlblInt _ _ _ _) _ |- _] => inv H
    | [H: {| bst_oss := _; bst_orqs := _; bst_msgs := _ |} =
          {| bst_oss := _; bst_orqs := _; bst_msgs := _ |} |- _] => inv H
    | [H0: In ?obj1 (sys_objs ?sys),
       H1: In ?obj2 (sys_objs ?sys),
       H2: obj_idx ?obj1 = obj_idx ?obj2 |- _] =>
      pose proof (obj_same_id_in_system_same _ _ _ H0 H1 H2);
      subst; clear H0 H2
    | [H0: In ?rule1 (obj_rules ?obj),
       H1: In ?rule2 (obj_rules ?obj),
       H2: rule_idx ?obj1 = rule_idx ?obj2 |- _] =>
      pose proof (rules_same_id_in_object_same _ _ _ H0 H1 H2);
      subst; clear H0 H2
    end.

Ltac good_rqrs_rule_get rule :=
  match goal with
  | [H: GoodRqRsSys _ ?sys,
     Hobj: In ?obj (sys_objs ?sys),
     Hrule: In rule (obj_rules ?obj) |- _] =>
    let Hg := fresh "H" in
    pose proof H as Hg;
    red in Hg; rewrite Forall_forall in Hg;
    specialize (Hg _ Hobj);
    red in Hg; rewrite Forall_forall in Hg;
    specialize (Hg _ Hrule)
  end.

Ltac good_rqrs_rule_cases rule :=
  match goal with
  | [H: GoodRqRsRule _ _ rule |- _] =>
    destruct H as [|[|[|[|]]]]
  end.

Ltac disc_rule_custom := idtac.
Ltac disc_rule_conds :=
  repeat
    (match goal with
     | [H: ImmDownRule _ _ _ |- _] =>
       let cidx := fresh "cidx" in
       let rqFrom := fresh "rqFrom" in
       let rsTo := fresh "rsTo" in
       destruct H as [cidx [rqFrom [rsTo ?]]]; dest
     | [H: ImmUpRule _ _ _ |- _] =>
       let rqFrom := fresh "rqFrom" in
       let rsTo := fresh "rsTo" in
       destruct H as [rqFrom [rsTo ?]]; dest
     | [H: RqFwdRule _ _ _ |- _] =>
       let rqFrom := fresh "rqFrom" in
       let rqTos := fresh "rqTos" in
       red in H;
       destruct H as [rqFrom [rqTos ?]]; dest
     | [H: RqUpUp _ _ _ _ ?rule \/
           RqUpDown _ _ _ _ ?rule \/
           RqDownDown _ _ _ _ ?rule |- _] =>
       destruct H as [|[|]]
     | [H: RqUpUp _ _ _ _ _ |- _] => red in H; dest
     | [H: RqUpDown _ _ _ _ _ |- _] => red in H; dest
     | [H: RqDownDown _ _ _ _ _ |- _] => red in H; dest
     | [H: RsBackRule _ |- _] =>
       let rssFrom := fresh "rssFrom" in
       let rsbTo := fresh "rsbTo" in
       destruct H as [rssFrom [rsbTo ?]]; dest
     | [H: RsDownRqDownRule _ _ _ |- _] =>
       let rsFrom := fresh "rsFrom" in
       let rqTos := fresh "rqTos" in
       destruct H as [rsFrom [rqTos ?]]; dest

     | [H: (FootprintReleasingUp _ _ _ /\ _) \/
           (FootprintReleasingDown _ _ _ /\ _) |- _] => destruct H; dest
     | [H: FootprintReleasingUp _ _ _ |- _] => red in H; dest
     | [H: FootprintReleasingDown _ _ _ |- _] => red in H; dest
     | [H: FootprintingUp _ _ _ |- _] => red in H
     | [H: FootprintingDown _ _ _ |- _] => red in H
     | [H: FootprintedUp _ _ _ |- _] =>
       let rqi := fresh "rqi" in
       destruct H as [rqi ?]; dest
     | [H: FootprintedDown _ _ _ |- _] =>
       let rqi := fresh "rqi" in
       destruct H as [rqi ?]; dest
     | [H: FootprintUpToDown _ _ _ _ |- _] =>
       let rqFrom := fresh "rqFrom" in
       let rsbTo := fresh "rsbTo" in
       let nrssFrom := fresh "nrssFrom" in
       destruct H as [rqFrom [rsbTo [nrssFrom ?]]]; dest
                                
     | [H: MsgsFrom _ _ _ _ |- _] => red in H
     | [H: MsgsTo _ _ |- _] => red in H
     | [H: RqAccepting _ _ _ |- _] => red in H
     | [H: RsAccepting _ _ _ |- _] => red in H
     | [H: RqReleasing _ |- _] => red in H
     | [H: RsReleasing _ |- _] => red in H

     | [H: DownLockFree _ _ _ |- _] => red in H
     | [H: DownLockFreeORq _ |- _] => red in H
     | [H: UpLockFree _ _ _ |- _] => red in H
     | [H: UpLockFreeORq _ |- _] => red in H

     | [H: StateSilent _ |- _] => red in H
     | [H: FootprintSilent _ |- _] => red in H; dest
     | [H: FootprintUpSilent _ |- _] => red in H
     | [H: FootprintDownSilent _ |- _] => red in H
                                             
     | [H1: rule_precond ?rule ->oprec _, H2: rule_precond ?rule _ _ _ |- _] =>
       specialize (H1 _ _ _ H2)
     | [H: (_ /\oprec _) _ _ _ |- _] => destruct H
     | [H1: rule_trs ?rule ?ost ?orq ?ins = _, H2: context[rule_trs ?rule _ _ _] |- _] =>
       specialize (H2 ost orq ins); rewrite H1 in H2; simpl in H2

     | [H1: ?m@[?k] = None, H2: context[?m@[?k]] |- _] =>
       rewrite H1 in H2; simpl in H2
     | [H1: ?m@[?k] = Some _, H2: context[?m@[?k]] |- _] =>
       rewrite H1 in H2; simpl in H2
     | [H1: None = ?m@[?k], H2: context[?m@[?k]] |- _] =>
       rewrite <-H1 in H2; simpl in H2
     | [H1: Some _ = ?m@[?k], H2: context[?m@[?k]] |- _] =>
       rewrite <-H1 in H2; simpl in H2

     | [H: Forall _ (_ :: _) |- _] => inv H
     | [H: Forall _ nil |- _] => clear H

     | [H: idsOf ?ivs = _ :: nil |- _] =>
       destruct ivs; [discriminate|simpl in H; inv H]
     | [H: idsOf ?ivs = nil |- _] => destruct ivs; [|discriminate]
     | [H: nil = nil |- _] => clear H
     end;
     try disc_rule_custom;
     simpl in *; subst).

Ltac solve_rule_conds :=
  repeat red;
  repeat
    (repeat
       match goal with
       | [ |- exists _, _] => eexists
       | [ |- _ /\ _] => split
       end;
     try reflexivity; try eassumption).

Section SysOnDTree.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hsd: SysOnDTree dtr sys).

  Lemma rqEdgeUpFrom_parentChnsOf_Some:
    forall oidx midx,
      rqEdgeUpFrom dtr oidx = Some midx ->
      exists ups downs pidx,
        parentChnsOf dtr oidx = Some (ups, downs, pidx) /\
        hd_error ups = Some midx.
  Proof.
    unfold rqEdgeUpFrom, upEdgesFrom; intros.
    destruct (parentChnsOf dtr oidx) as [[[ups downs] pidx]|];
      simpl in *; [|discriminate].
    repeat eexists; eauto.
  Qed.

  Lemma rsEdgeUpFrom_parentChnsOf_Some:
    forall oidx midx,
      rsEdgeUpFrom dtr oidx = Some midx ->
      exists ups downs pidx,
        parentChnsOf dtr oidx = Some (ups, downs, pidx) /\
        hd_error (tail ups) = Some midx.
  Proof.
    unfold rsEdgeUpFrom, upEdgesFrom; intros.
    destruct (parentChnsOf dtr oidx) as [[[ups downs] pidx]|];
      simpl in *; [|discriminate].
    repeat eexists; eauto.
  Qed.

  Lemma edgeDownTo_parentChnsOf_Some:
    forall oidx midx,
      edgeDownTo dtr oidx = Some midx ->
      exists ups downs pidx,
        parentChnsOf dtr oidx = Some (ups, downs, pidx) /\
        hd_error downs = Some midx.
  Proof.
    unfold edgeDownTo, downEdgesTo; intros.
    destruct (parentChnsOf dtr oidx) as [[[ups downs] pidx]|];
      simpl in *; [|discriminate].
    repeat eexists; eauto.
  Qed.
  
  Lemma sysOnDTree_rqEdgeUpFrom_sys_minds:
    forall oidx midx,
      rqEdgeUpFrom dtr oidx = Some midx ->
      In midx sys.(sys_minds).
  Proof.
    intros.
    apply rqEdgeUpFrom_parentChnsOf_Some in H.
    destruct H as [ups [downs [pidx ?]]]; dest.
    destruct Hsd.
    specialize (H2 _ _ _ _ H); dest.
    apply hd_error_In in H0.
    auto.
  Qed.

  Lemma sysOnDTree_rsEdgeUpFrom_sys_minds:
    forall oidx midx,
      rsEdgeUpFrom dtr oidx = Some midx ->
      In midx sys.(sys_minds).
  Proof.
    intros.
    apply rsEdgeUpFrom_parentChnsOf_Some in H.
    destruct H as [ups [downs [pidx ?]]]; dest.
    destruct Hsd.
    specialize (H2 _ _ _ _ H); dest.
    apply hd_error_In in H0.
    apply tl_In in H0.
    auto.
  Qed.

  Lemma sysOnDTree_edgeDownTo_sys_minds:
    forall oidx midx,
      edgeDownTo dtr oidx = Some midx ->
      In midx sys.(sys_minds).
  Proof.
    intros.
    apply edgeDownTo_parentChnsOf_Some in H.
    destruct H as [ups [downs [pidx ?]]]; dest.
    destruct Hsd.
    specialize (H2 _ _ _ _ H); dest.
    apply hd_error_In in H0.
    auto.
  Qed.

  Lemma sysOnDTree_rqrs_updown_NoDup:
    forall oidx rqUp rsUp down,
      rqEdgeUpFrom dtr oidx = Some rqUp ->
      rsEdgeUpFrom dtr oidx = Some rsUp ->
      edgeDownTo dtr oidx = Some down ->
      NoDup [rqUp; rsUp; down].
  Proof.
    intros.
    destruct Hsd.
    apply rqEdgeUpFrom_parentChnsOf_Some in H.
    destruct H as [ups [downs [pidx ?]]].
    apply rsEdgeUpFrom_parentChnsOf_Some in H0.
    apply edgeDownTo_parentChnsOf_Some in H1.
    dest.
    rewrite H0 in H; inv H.
    rewrite H1 in H0; inv H0.
    apply parentChnsOf_NoDup in H1; [|assumption].
    
    destruct ups as [|? ups]; [discriminate|].
    simpl in *; inv H4.
    destruct ups as [|? ups]; [discriminate|].
    simpl in *; inv H6.
    destruct downs as [|? downs]; [discriminate|].
    simpl in *; inv H5.

    inv H1; inv H5.
    constructor; [intro Hx; Common.dest_in; intuition|].
    constructor; [intro Hx; Common.dest_in; intuition|].
    repeat constructor.
    auto.
  Qed.

  Lemma sysOnDTree_rqrs_updown_disj:
    forall oidx1 rqUp1 rsUp1 down1 oidx2 rqUp2 rsUp2 down2
           (Hoidx: oidx1 <> oidx2),
      rqEdgeUpFrom dtr oidx1 = Some rqUp1 ->
      rsEdgeUpFrom dtr oidx1 = Some rsUp1 ->
      edgeDownTo dtr oidx1 = Some down1 ->
      rqEdgeUpFrom dtr oidx2 = Some rqUp2 ->
      rsEdgeUpFrom dtr oidx2 = Some rsUp2 ->
      edgeDownTo dtr oidx2 = Some down2 ->
      DisjList [rqUp1; rsUp1; down1] [rqUp2; rsUp2; down2].
  Proof.
    intros.
    destruct Hsd.
    apply rqEdgeUpFrom_parentChnsOf_Some in H.
    destruct H as [ups1 [downs1 [pidx1 ?]]].
    apply rsEdgeUpFrom_parentChnsOf_Some in H0.
    apply edgeDownTo_parentChnsOf_Some in H1.
    dest.
    rewrite H0 in H; inv H.
    rewrite H1 in H0; inv H0.
    apply rqEdgeUpFrom_parentChnsOf_Some in H2.
    destruct H2 as [ups2 [downs2 [pidx2 ?]]].
    apply rsEdgeUpFrom_parentChnsOf_Some in H3.
    apply edgeDownTo_parentChnsOf_Some in H4.
    dest.
    rewrite H2 in H; inv H.
    rewrite H3 in H2; inv H2.

    destruct ups1 as [|? ups1]; [discriminate|].
    simpl in *; inv H7.
    destruct ups1 as [|? ups1]; [discriminate|].
    simpl in *; inv H9.
    destruct downs1 as [|? downs1]; [discriminate|].
    simpl in *; inv H8.
    destruct ups2 as [|? ups2]; [discriminate|].
    simpl in *; inv H0.
    destruct ups2 as [|? ups2]; [discriminate|].
    simpl in *; inv H10.
    destruct downs2 as [|? downs2]; [discriminate|].
    simpl in *; inv H4.

    pose proof (parentChnsOf_DisjList H5 Hoidx H1 H3).
    eapply DisjList_SubList;
      [|apply DisjList_comm;
        eapply DisjList_SubList;
        [|apply DisjList_comm; exact H]].
    - red; intros.
      Common.dest_in; clear; firstorder.
    - red; intros.
      Common.dest_in; clear; firstorder.
  Qed.
  
End SysOnDTree.

Section FootprintInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hitr: GoodRqRsSys dtr sys).

  Definition FootprintUpOkEx (oidx: IdxT) (rqi: RqInfo Msg) :=
    exists rqTo rsFrom rsbTo,
      rqi.(rqi_minds_rss) = [rsFrom] /\
      rqi.(rqi_midx_rsb) = rsbTo /\
      FootprintUpOk dtr oidx rqTo rsFrom rsbTo.

  Definition FootprintDownOkEx (rqi: RqInfo Msg) :=
    exists rqTos rssFrom rsbTo,
      rqi.(rqi_minds_rss) = rssFrom /\
      rqi.(rqi_midx_rsb) = rsbTo /\
      ((exists rqFrom, FootprintUpDownOk dtr rqFrom rqTos rssFrom rsbTo) \/
       FootprintDownDownOk dtr rqTos rssFrom).

  Definition FootprintsOkORqs (orqs: ORqs Msg) :=
    forall oidx,
      orqs@[oidx] >>=[True]
          (fun orq =>
             (orq@[upRq] >>=[True] (fun rqiu => FootprintUpOkEx oidx rqiu)) /\
             (orq@[downRq] >>=[True] (fun rqid => FootprintDownOkEx rqid))).

  Lemma footprints_ok_orqs_add:
    forall orqs,
      FootprintsOkORqs orqs ->
      forall oidx norq,
        norq@[upRq] >>=[True] (fun rqiu => FootprintUpOkEx oidx rqiu) ->
        norq@[downRq] >>=[True] (fun rqid => FootprintDownOkEx rqid) ->
        FootprintsOkORqs (orqs +[oidx <- norq]).
  Proof.
    unfold FootprintsOkORqs; intros.
    mred; simpl; intros; auto.
  Qed.
  
  Definition FootprintsOk (st: MState oifc) :=
    FootprintsOkORqs st.(bst_orqs).

  Ltac disc_rule_custom ::=
    repeat
      match goal with
      | [H1: FootprintsOkORqs ?orqs, H2: ?orqs @[?oidx] = _ |- _] =>
        let Hf := fresh "H" in
        pose proof (H1 oidx) as Hf;
        rewrite H2 in Hf; simpl in Hf; dest;
        clear H2
      end.

  Lemma footprints_ok_init:
    InvInit sys FootprintsOk.
  Proof.
    intros; do 3 red.
    intros; simpl; auto.
  Qed.
  
  Lemma footprints_ok_step:
    InvStep sys step_m FootprintsOk.
  Proof.
    red; intros.
    red in H0; red.
    inv H1; try assumption.

    simpl in *.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      mred.
      apply footprints_ok_orqs_add; auto; try (mred; fail).
    - disc_rule_conds.
      mred.
      apply footprints_ok_orqs_add; auto; try (mred; fail).
    - disc_rule_conds.
      + apply footprints_ok_orqs_add; auto.
        * rewrite H15; simpl.
          do 3 eexists; repeat split; eassumption.
        * rewrite <-H22; assumption.
      + apply footprints_ok_orqs_add; auto.
        * rewrite <-H21; assumption.
        * rewrite H13; simpl.
          do 3 eexists; repeat split.
          left; eexists; eassumption.
      + apply footprints_ok_orqs_add; auto.
        * rewrite <-H21; assumption.
        * rewrite H13; simpl.
          do 3 eexists; repeat split.
          right; eassumption.
    - disc_rule_conds.
      + apply footprints_ok_orqs_add; auto.
        * rewrite H17; simpl; auto.
        * rewrite <-H6; assumption.
      + apply footprints_ok_orqs_add; auto.
        * rewrite <-H6; assumption.
        * rewrite H17; simpl; auto.
    - disc_rule_conds.
      apply footprints_ok_orqs_add; auto.
      + rewrite H20; simpl; auto.
      + rewrite H14; simpl.
        do 3 eexists; repeat split.
        left; eexists; rewrite <-H19 in H6; eassumption.
  Qed.

  Lemma footprints_ok:
    InvReachable sys step_m FootprintsOk.
  Proof.
    eapply inv_reachable.
    - apply footprints_ok_init.
    - apply footprints_ok_step.
  Qed.
  
End FootprintInv.

Ltac disc_footprints_ok :=
  repeat
    match goal with
    | [H: FootprintsOk _ _ |- _] => red in H
    | [H1: FootprintsOkORqs _ ?orqs, H2: ?orqs @[?oidx] = _ |- _] =>
      let Hf := fresh "H" in
      pose proof (H1 oidx) as Hf;
      rewrite H2 in Hf; simpl in Hf; dest;
      clear H2
    | [H: FootprintUpOkEx _ _ _ |- _] =>
      let rqTo := fresh "rqTo" in
      let rsFrom := fresh "rsFrom" in
      let rsbTo := fresh "rsbTo" in
      destruct H as [rqTo [rsFrom [rsbTo ?]]]; dest
    | [H: FootprintDownOkEx _ _ |- _] =>
      let rqTos := fresh "rqTos" in
      let rssFrom := fresh "rssFrom" in
      let rsbTo := fresh "rsbTo" in
      destruct H as [rqTos [rssFrom [rsbTo ?]]]; dest
                                                   
    | [H: FootprintUpOk _ _ _ _ _ |- _] =>
      let cidx := fresh "cidx" in
      destruct H as [cidx ?]; dest
    | [H: (exists _, FootprintUpDownOk _ _ _ _ _) \/
          FootprintDownDownOk _ _ _ |- _] => destruct H
    | [H: exists _, FootprintUpDownOk _ _ _ _ _ |- _] =>
      let rsFrom := fresh "rqFrom" in
      destruct H as [rqFrom ?]; dest
    | [H: FootprintUpDownOk _ _ _ _ _ |- _] =>
      let upCIdx := fresh "upCIdx" in
      let downCInds := fresh "downCInds" in
      destruct H as [upCIdx [downCInds ?]]; dest
    | [H: FootprintDownDownOk _ _ _ |- _] =>
      let downCInds := fresh "downCInds" in
      destruct H as [downCInds ?]; dest
    end.

Section MessageInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hitr: GoodRqRsSys dtr sys).

  Definition RqUpMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    exists cidx rqUp,
      msgs = [rqUp] /\
      msg_type (valOf rqUp) = MRq /\
      parentIdxOf dtr cidx = Some oidx /\
      rqEdgeUpFrom dtr cidx = Some (idOf rqUp).

  Definition RqDownMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    exists rqDown, msgs = [rqDown] /\
                   msg_type (valOf rqDown) = MRq /\
                   edgeDownTo dtr oidx = Some (idOf rqDown).

  Definition RsUpMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    Forall (fun msg => msg_type (valOf msg) = MRs) msgs /\
    exists cinds,
      Forall (fun crs => rsEdgeUpFrom dtr (fst crs) = Some (snd crs))
             (combine cinds (idsOf msgs)).

  Definition RsDownMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    exists rsDown, msgs = [rsDown] /\
                   msg_type (valOf rsDown) = MRs /\
                   edgeDownTo dtr oidx = Some (idOf rsDown).
  
  Ltac disc_rule_custom ::=
    disc_footprints_ok.
  
  Lemma messages_in_cases:
    forall st1 oidx ridx rins routs st2,
      Reachable (steps step_m) sys st1 ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      RqUpMsgs oidx rins \/
      RqDownMsgs oidx rins \/
      RsUpMsgs oidx rins \/
      RsDownMsgs oidx rins.
  Proof.
    intros.

    (* Register some necessary invariants to prove this invariant. *)
    pose proof (footprints_ok Hitr H).

    inv H0.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - left.
      disc_rule_conds.
      solve_rule_conds.

    - right; left.
      disc_rule_conds.
      solve_rule_conds.

    - disc_rule_conds.
      + left; solve_rule_conds.
      + left; solve_rule_conds.
      + right; left; solve_rule_conds.

    - disc_rule_conds.
      + right; right; right.
        (* [disc_rule_conds] currently can't discharge below automatically. *)
        rewrite H8 in H2.
        disc_rule_conds.
        solve_rule_conds.
      + right; right; left.
        (* [disc_rule_conds] currently can't discharge below automatically. *)
        rewrite <-H2 in H24.
        solve_rule_conds.
      + right; right; left.
        (* [disc_rule_conds] currently can't discharge below automatically. *)
        rewrite <-H2 in H21.
        solve_rule_conds.

    - right; right; right.
      disc_rule_conds.
      solve_rule_conds.
  Qed.
    
End MessageInv.

(** NOTE: With [LockInv] below we may need some invariants 
 * for [Atomic] histories, such as: if [Atomic hst] and [st1 -(hst)-> st2]
 * then [hst.eouts ⊆ st2.msgs].
 *)

(* Want: between two continuous histories H1 and H2, after H1, related locks are
 * never released until H2; it can be proven by [LockInv] below and
 * [atomic_messages_spec_in] in SerialFacts.v.
 *)
Section LockInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypotheses (Hrr: GoodRqRsSys dtr sys)
             (Hsd: SysOnDTree dtr sys).

  Section OnMState.
    Variables (orqs: ORqs Msg)
              (msgs: MessagePool Msg).

    Definition OUpLocked (oidx: IdxT) :=
      orqs@[oidx] >>=[False] (fun orq => UpLockedORq orq).

    Definition ODownLocked (oidx: IdxT) :=
      orqs@[oidx] >>=[False] (fun orq => DownLockedORq orq).

    Definition ODownLockedTo (oidx: IdxT) (rsbTo: IdxT) :=
      orqs@[oidx] >>=[False]
          (fun orq =>
             exists rqi,
               orq@[downRq] = Some rqi /\
               rqi.(rqi_midx_rsb) = rsbTo).
    
    Definition OUpLockFree (oidx: IdxT) :=
      orqs@[oidx] >>=[True] (fun orq => UpLockFreeORq orq).

    Definition ODownLockFree (oidx: IdxT) :=
      orqs@[oidx] >>=[True] (fun orq => DownLockFreeORq orq).

    Definition rqsQ (midx: IdxT) :=
      filter (fun msg => msg.(msg_type) ==n MRq) (findQ midx msgs).

    Definition rssQ (midx: IdxT) :=
      filter (fun msg => msg.(msg_type) ==n MRs) (findQ midx msgs).

    Definition UpLockFreeInv (oidx: IdxT) :=
      (rqEdgeUpFrom dtr oidx) >>=[True] (fun rqUp => findQ rqUp msgs = nil) /\
      (edgeDownTo dtr oidx) >>=[True] (fun down => rssQ down = nil) /\
      (parentIdxOf dtr oidx) >>=[True] (fun pidx => OUpLockFree pidx).
    
    Definition UpLockedInv (oidx: IdxT) :=
      exists rqUp down pidx,
        rqEdgeUpFrom dtr oidx = Some rqUp /\
        edgeDownTo dtr oidx = Some down /\
        parentIdxOf dtr oidx = Some pidx /\
        xor3 (findQ rqUp msgs <> nil)
             (rssQ down <> nil)
             (OUpLocked pidx).

    Definition DownLockFreeInv (oidx: IdxT) :=
      forall cidx,
        parentIdxOf dtr cidx = Some oidx ->
        ((edgeDownTo dtr cidx) >>=[True] (fun down => rqsQ down = nil) /\
         (rsEdgeUpFrom dtr cidx) >>=[True] (fun rsUp => findQ rsUp msgs = nil)).
    
    Definition DownLockedInv (oidx: IdxT) (rqi: RqInfo Msg) :=
      Forall (fun rsUp =>
                exists down cidx,
                  edgeDownTo dtr cidx = Some down /\
                  rsEdgeUpFrom dtr cidx = Some rsUp /\
                  parentIdxOf dtr cidx = Some oidx /\
                  xor3 (rqsQ down <> nil)
                       (findQ rsUp msgs <> nil)
                       (ODownLockedTo cidx rsUp))
             rqi.(rqi_minds_rss).

    Definition UpLockInvORq (oidx: IdxT) (orq: ORq Msg) :=
      match orq@[upRq] with
      | Some _ => UpLockedInv oidx
      | None => UpLockFreeInv oidx
      end.

    Definition DownLockInvORq (oidx: IdxT) (orq: ORq Msg) :=
      match orq@[downRq] with
      | Some downRqi => DownLockedInv oidx downRqi
      | None => DownLockFreeInv oidx
      end.

    Definition LockInvMO :=
      forall oidx,
        In oidx (map (@obj_idx _) sys.(sys_objs)) ->
        let orq := orqs@[oidx] >>=[[]] (fun orq => orq) in
        UpLockInvORq oidx orq /\ DownLockInvORq oidx orq.

  End OnMState.
  
  Definition LockInv (st: MState oifc) :=
    LockInvMO st.(bst_orqs) st.(bst_msgs).

  Lemma lockInv_init:
    InvInit sys LockInv.
  Proof.
    intros; do 3 red; cbn.
    intros; cbn.
    split.
    - red; cbn; repeat split.
      + destruct (rqEdgeUpFrom dtr oidx); simpl; auto.
      + destruct (edgeDownTo dtr oidx); simpl; auto.
      + destruct (parentIdxOf dtr oidx); simpl; auto.
    - red; cbn; repeat split.
      + destruct (edgeDownTo dtr cidx); simpl; auto.
      + destruct (rsEdgeUpFrom dtr cidx); simpl; auto.
  Qed.

  (** TODO: need to prove following facts:
   * 1) [rqEdgeUpFrom dtr _ = Some midx -> In midx (sys_minds sys)]
   * 2) [rsEdgeUpFrom dtr _ = Some midx -> In midx (sys_minds sys)]
   * 3) [edgeDownTo dtr _ = Some midx -> In midx (sys_minds sys)]
   *
   * 4) [NoDup [rqEdgeUpFrom dtr oidx; 
   *            rsEdgeUpFrom dtr oidx;
   *            edgeDownTo dtr oidx]]
   * 5) [parentIdxOf dtr cidx = Some oidx ->
   *     {rqEdgeUpFrom dtr cidx, rsEdgeUpFrom dtr cidx, edgeDownTo dtr cidx}
   *     <>
   *     {rqEdgeUpFrom dtr oidx, rsEdgeUpFrom dtr oidx, edgeDownTo dtr oidx}]
   * 5') Better to prove more generally:
   *     a) [parentIdxOf dtr cidx = Some oidx -> cidx <> oidx] and
   *     b) [∀oidx1 oidx2, oidx1 <> oidx2 -> ...]
   *)
  
  Lemma upLockedInv_msgs_preserved:
    forall orqs msgs1 msgs2 oidx,
      UpLockedInv orqs msgs1 oidx ->
      (match rqEdgeUpFrom dtr oidx with
       | Some rqUp => findQ rqUp msgs1 = findQ rqUp msgs2
       | None => False
       end) ->
      (match edgeDownTo dtr oidx with
       | Some down => rssQ msgs1 down = rssQ msgs2 down
       | None => False
       end) ->
      UpLockedInv orqs msgs2 oidx.
  Proof.
    unfold UpLockedInv; simpl; intros.
    destruct H as [rqUp [down [pidx ?]]]; dest.
    rewrite H in H0.
    rewrite H2 in H1.
    exists rqUp, down, pidx.
    repeat split; try assumption.
    rewrite <-H0, <-H1.
    assumption.
  Qed.
  
  Corollary upLockedInv_enqMsgs_preserved:
    forall orqs msgs emsgs oidx,
      UpLockedInv orqs msgs oidx ->
      DisjList (idsOf emsgs) (sys_minds sys) ->
      UpLockedInv orqs (enqMsgs emsgs msgs) oidx.
  Proof.
    intros.
    eapply upLockedInv_msgs_preserved; eauto.
    - destruct H as [rqUp [down [pidx ?]]]; dest.
      rewrite H.
      rewrite findQ_not_In_enqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply sysOnDTree_rqEdgeUpFrom_sys_minds; eauto.
    - destruct H as [rqUp [down [pidx ?]]]; dest.
      rewrite H1.
      unfold rssQ.
      rewrite findQ_not_In_enqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply sysOnDTree_edgeDownTo_sys_minds; eauto.
  Qed.

  Corollary upLockedInv_deqMsgs_preserved:
    forall orqs msgs eminds oidx,
      UpLockedInv orqs msgs oidx ->
      DisjList eminds (sys_minds sys) ->
      UpLockedInv orqs (deqMsgs eminds msgs) oidx.
  Proof.
    intros.
    eapply upLockedInv_msgs_preserved; eauto.
    - destruct H as [rqUp [down [pidx ?]]]; dest.
      rewrite H.
      rewrite findQ_not_In_deqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply sysOnDTree_rqEdgeUpFrom_sys_minds; eauto.
    - destruct H as [rqUp [down [pidx ?]]]; dest.
      rewrite H1.
      unfold rssQ.
      rewrite findQ_not_In_deqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply sysOnDTree_edgeDownTo_sys_minds; eauto.
  Qed.

  Lemma upLockFreeInv_msgs_preserved:
    forall orqs msgs1 msgs2 oidx,
      UpLockFreeInv orqs msgs1 oidx ->
      (match rqEdgeUpFrom dtr oidx with
       | Some rqUp => findQ rqUp msgs1 = findQ rqUp msgs2
       | None => True
       end) ->
      (match edgeDownTo dtr oidx with
       | Some down => rssQ msgs1 down = rssQ msgs2 down
       | None => True
       end) ->
      UpLockFreeInv orqs msgs2 oidx.
  Proof.
    unfold UpLockFreeInv; simpl; intros.
    repeat split.
    - destruct (rqEdgeUpFrom dtr oidx); simpl in *; dest; auto.
      rewrite <-H0; assumption.
    - destruct (edgeDownTo dtr oidx); simpl in *; dest; auto.
      rewrite <-H1; assumption.
    - destruct (parentIdxOf dtr oidx); simpl in *; dest; auto.
  Qed.
  
  Corollary upLockFreeInv_enqMsgs_preserved:
    forall orqs msgs emsgs oidx,
      UpLockFreeInv orqs msgs oidx ->
      DisjList (idsOf emsgs) (sys_minds sys) ->
      UpLockFreeInv orqs (enqMsgs emsgs msgs) oidx.
  Proof.
    intros.
    eapply upLockFreeInv_msgs_preserved; eauto.
    - red in H; dest.
      remember (rqEdgeUpFrom dtr oidx) as rqUp.
      destruct rqUp as [rqUp|]; simpl in *; dest; auto.
      rewrite findQ_not_In_enqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply sysOnDTree_rqEdgeUpFrom_sys_minds; eauto.
    - red in H; dest.
      remember (edgeDownTo dtr oidx) as down.
      destruct down as [down|]; simpl in *; dest; auto.
      unfold rssQ.
      rewrite findQ_not_In_enqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply sysOnDTree_edgeDownTo_sys_minds; eauto.
  Qed.

  Corollary upLockFreeInv_deqMsgs_preserved:
    forall orqs msgs eminds oidx,
      UpLockFreeInv orqs msgs oidx ->
      DisjList eminds (sys_minds sys) ->
      UpLockFreeInv orqs (deqMsgs eminds msgs) oidx.
  Proof.
    intros.
    eapply upLockFreeInv_msgs_preserved; eauto.
    - red in H; dest.
      remember (rqEdgeUpFrom dtr oidx) as rqUp.
      destruct rqUp as [rqUp|]; simpl in *; dest; auto.
      rewrite findQ_not_In_deqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply sysOnDTree_rqEdgeUpFrom_sys_minds; eauto.
    - red in H; dest.
      remember (edgeDownTo dtr oidx) as down.
      destruct down as [down|]; simpl in *; dest; auto.
      unfold rssQ.
      rewrite findQ_not_In_deqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply sysOnDTree_edgeDownTo_sys_minds; eauto.
  Qed.

  Lemma downLockedInv_enqMsgs_preserved:
    forall orqs msgs emsgs oidx rqi,
      DownLockedInv orqs msgs oidx rqi ->
      DisjList (idsOf emsgs) (sys_minds sys) ->
      DownLockedInv orqs (enqMsgs emsgs msgs) oidx rqi.
  Proof.
    (** TODO: ditto *)
  Admitted.

  Lemma downLockedInv_deqMsgs_preserved:
    forall orqs msgs eminds oidx rqi,
      DownLockedInv orqs msgs oidx rqi ->
      DisjList eminds (sys_minds sys) ->
      DownLockedInv orqs (deqMsgs eminds msgs) oidx rqi.
  Proof.
    (** TODO: ditto *)
  Admitted.

  Lemma downLockFreeInv_enqMsgs_preserved:
    forall msgs emsgs oidx,
      DownLockFreeInv msgs oidx ->
      DisjList (idsOf emsgs) (sys_minds sys) ->
      DownLockFreeInv (enqMsgs emsgs msgs) oidx.
  Proof.
    (** TODO: ditto *)
  Admitted.

  Lemma downLockFreeInv_deqMsgs_preserved:
    forall msgs eminds oidx,
      DownLockFreeInv msgs oidx ->
      DisjList eminds (sys_minds sys) ->
      DownLockFreeInv (deqMsgs eminds msgs) oidx.
  Proof.
    (** TODO: ditto *)
  Admitted.
  
  Lemma lockInv_step_ext_in:
    forall oss orqs msgs eins,
      LockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      eins <> nil ->
      ValidMsgsExtIn sys eins ->
      LockInv {| bst_oss := oss;
                 bst_orqs := orqs;
                 bst_msgs := enqMsgs eins msgs |}.
  Proof.
    unfold LockInv; simpl; intros.
    red; intros.
    specialize (H oidx H2).

    destruct H1.
    assert (DisjList (idsOf eins) (sys_minds sys)).
    { eapply DisjList_SubList; eauto.
      apply DisjList_comm.
      apply sys_minds_sys_merqs_DisjList.
    }
    
    destruct (orqs@[oidx]) as [orq|]; simpl in *; dest.

    - split.
      + clear H5; red in H; red.
        remember (orq@[upRq]) as orqi.
        destruct orqi as [rqi|].
        * apply upLockedInv_enqMsgs_preserved; assumption.
        * apply upLockFreeInv_enqMsgs_preserved; assumption.
      + clear H; red in H5; red.
        remember (orq@[downRq]) as orqi.
        destruct orqi as [rqi|].
        * apply downLockedInv_enqMsgs_preserved; assumption.
        * apply downLockFreeInv_enqMsgs_preserved; assumption.

    - red in H; simpl in H.
      red in H5; simpl in H5.
      split.
      + red; simpl.
        apply upLockFreeInv_enqMsgs_preserved; assumption.
      + red; simpl.
        apply downLockFreeInv_enqMsgs_preserved; assumption.
  Qed.

  Lemma lockInv_step_ext_out:
    forall oss orqs msgs eouts,
      LockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      eouts <> nil ->
      Forall (FirstMPI msgs) eouts ->
      ValidMsgsExtOut sys eouts ->
      LockInv {| bst_oss := oss;
                 bst_orqs := orqs;
                 bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    unfold LockInv; simpl; intros.
    red; intros.
    specialize (H oidx H3).

    destruct H2.
    assert (DisjList (idsOf eouts) (sys_minds sys)).
    { eapply DisjList_SubList; eauto.
      apply DisjList_comm.
      apply sys_minds_sys_merss_DisjList.
    }
    
    destruct (orqs@[oidx]) as [orq|]; simpl in *; dest.

    - split.
      + clear H6; red in H; red.
        remember (orq@[upRq]) as orqi.
        destruct orqi as [rqi|].
        * apply upLockedInv_deqMsgs_preserved; assumption.
        * apply upLockFreeInv_deqMsgs_preserved; assumption.
      + clear H; red in H6; red.
        remember (orq@[downRq]) as orqi.
        destruct orqi as [rqi|].
        * apply downLockedInv_deqMsgs_preserved; assumption.
        * apply downLockFreeInv_deqMsgs_preserved; assumption.

    - red in H; simpl in H.
      red in H6; simpl in H6.
      split.
      + red; simpl.
        apply upLockFreeInv_deqMsgs_preserved; assumption.
      + red; simpl.
        apply downLockFreeInv_deqMsgs_preserved; assumption.
  Qed.
  
  Lemma lockInv_step_int:
    forall oss orqs msgs obj rule
           post porq mins nost norq mouts,
      LockInv {| bst_oss := oss;
                 bst_orqs := orqs;
                 bst_msgs := msgs |} ->
      In obj (sys_objs sys) ->
      In rule (obj_rules obj) ->
      orqs@[obj_idx obj] = Some porq ->
      oss@[obj_idx obj] = Some post ->
      Forall (FirstMPI msgs) mins ->
      ValidMsgsIn sys mins ->
      rule_precond rule post porq mins ->
      rule_trs rule post porq mins = (nost, norq, mouts) ->
      ValidMsgsOut sys mouts ->
      DisjList (idsOf mins) (idsOf mouts) ->
      LockInv
        {| bst_oss := (oss) +[ obj_idx obj <- nost];
           bst_orqs := (orqs) +[ obj_idx obj <- norq];
           bst_msgs := enqMsgs mouts (deqMsgs (idsOf mins) msgs) |}.
  Proof.
    intros.
    do 2 red; simpl; intros.
    do 2 red in H; simpl in H.
    good_rqrs_rule_get rule.
    specialize (H _ H10); dest; split.

    - (** Proving invariants about uplocks *)
      clear H12.
      red; red in H.
      M.cmp (obj_idx obj) oidx; mred; simpl in *.

      + (* case [oidx = obj_idx obj] *)
        good_rqrs_rule_cases rule.

        * (* case [ImmDownRule] *)
          disc_rule_conds.
          rewrite H18.
          replace (orqs +[obj_idx obj <- porq]) with orqs by meq.
          destruct i as [rsMIdx rsd]; simpl in *.

          eapply upLockFreeInv_msgs_preserved; eauto.
          { admit. }
          { admit. }

        * (* case [ImmUpRule] *)
          disc_rule_conds.
          replace (orqs +[obj_idx obj <- porq]) with orqs by meq.
          destruct i as [rsMIdx rsd]; simpl in *.
          destruct (porq@[upRq]).
          { eapply upLockedInv_msgs_preserved; eauto.
            { admit. }
            { rewrite H11.
              (* provable since [msg_type (valOf i0) = MRq]. *)
              admit.
            }
          }
          { eapply upLockFreeInv_msgs_preserved; eauto.
            { admit. }
            { rewrite H11.
              (* provable since [msg_type (valOf i0) = MRq]. *)
              admit.
            }
          }

        * (* case [RqFwdRule] *)
          disc_rule_conds.
          { (* case [RqUpUp]; setting an uplock. *)
            admit.
          }
          { (* case [RqUpDown]; setting a downlock; [UpLockInvORq] preserved. *)
            rewrite <-H20.
            admit.
          }
          { (* case [RqDownDown]; setting a downlock; [UpLockInvORq] preserved. *)
            rewrite <-H20.
            admit.
          }

        * (* case [RsBackRule] *)
          disc_rule_conds.
          { (* case [FootprintReleasingUp]; releasing the uplock. *)
            rewrite H16.
            red in H.
            (** * we need [footprints_ok] here to say the footprint is valid!! *)
            admit.
          }
          { (* case [FootprintReleasingDown]; releasing the downlock;
             * [UpLockInvORq] preserved *)
            rewrite <-H15.
            (** * we need [footprints_ok] here to say the footprint is valid!! *)
            admit.
          }

        * (* case [RsDownRqDownRule]; releasing the uplock; setting a downlock.
           * The proof must be similar to that of [FootprintReleasingUp].
           *)
          disc_rule_conds.
          admit.

      + (* case [oidx <> obj_idx obj]:
         * The only nontrivial case will be when [oidx = parentIdxOf dtr (obj_idx obj)].
         * Otherwise state transitions are orthogonal.
         *)
        admit.

    - (** Proving invariants about downlocks *)
      admit.

  Admitted.
  
  Lemma lockInv_step:
    InvStep sys step_m LockInv.
  Proof.
    red; intros.
    inv H1;
      [auto
      |apply lockInv_step_ext_in; auto
      |apply lockInv_step_ext_out; auto
      |eapply lockInv_step_int; eauto].
  Qed.

  Lemma lockInv_ok:
    InvReachable sys step_m LockInv.
  Proof.
    apply inv_reachable.
    - apply lockInv_init.
    - apply lockInv_step.
  Qed.
  
End LockInv.

Section RqUpInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: GoodRqRsSys dtr sys)
             (Hrud: RqUpRsUpOkSys dtr sys).
  
  (* Lemma rqUp_reducible: *)
  (*   forall oidx1 ridx1 rins1 routs1 rule1 obj1 *)
  (*          (Hobj1: In obj1 sys.(sys_objs)) (Hoidx1: obj1.(obj_idx) = oidx1) *)
  (*          (Hrule1: In rule1 obj1.(obj_rules)) *)
  (*          (Hridx1: rule1.(rule_idx) = ridx1) *)
  (*          oidx2 ridx2 rins2 routs2 rule2 obj2 *)
  (*          (Hobj2: In obj2 sys.(sys_objs)) (Hoidx2: obj2.(obj_idx) = oidx2) *)
  (*          (Hrule2: In rule2 obj2.(obj_rules)) *)
  (*          (Hridx2: rule2.(rule_idx) = ridx2), *)
  (*     RqToUpRule dtr oidx1 rule1 -> *)
  (*     DisjList routs1 rins2 -> *)
  (*     Reducible sys [RlblInt oidx2 ridx2 rins2 routs2; *)
  (*                      RlblInt oidx1 ridx1 rins1 routs1] *)
  (*               [RlblInt oidx1 ridx1 rins1 routs1; *)
  (*                  RlblInt oidx2 ridx2 rins2 routs2]. *)
  (* Proof. *)
  (* Admitted. *)

End RqUpInv.

Inductive TrsType := RqUp | RqDown | RsUp | RsDown.
(* Object index -> TrsTypes (ordered, head is the oldest one) *)
Definition TrsState := M.t (list TrsType).

Definition addTrsState (oidx: IdxT) (tr: TrsType) (ts: TrsState): TrsState :=
  match ts@[oidx] with
  | Some tts => ts +[oidx <- tr :: tts]
  | None => ts +[oidx <- [tr]]
  end.

Definition rssOfL (lbl: MLabel) :=
  match lbl with
  | RlblInt oidx _ _ mouts =>
    match mouts with
    | nil => Some oidx (* Requests are never ignored. *)
    | (midx, mout) :: _ =>
      if eq_nat_dec (msg_type mout) MRs
      then Some oidx else None
    end
  | _ => None
  end.

Fixpoint rssOf (hst: MHistory): list IdxT :=
  match hst with
  | nil => nil
  | lbl :: hst' => (rssOfL lbl) ::> (rssOf hst')
  end.

(* Definition rqsOfL (lbl: MLabel) := *)
(*   match lbl with *)
(*   | RlblInt oidx _ _ mouts => *)
(*     match mouts with *)
(*     | nil => None (* Requests are never ignored. *) *)
(*     | (midx, mout) :: _ => *)
(*       if eq_nat_dec (msg_type mout) MRq *)
(*       then Some oidx else None *)
(*     end *)
(*   | _ => None *)
(*   end. *)

Section AtomicInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hitr: GoodRqRsSys dtr sys).

  Definition rsUpCover (idm: Id Msg): list IdxT :=
    nil. (** TODO: define it. *)

  Fixpoint rsUpCovers (eouts: list (Id Msg)): list IdxT :=
    match eouts with
    | nil => nil
    | idm :: eouts' => rsUpCover idm ++ rsUpCovers eouts'
    end.

  Definition rsDownCover (idm: Id Msg): list IdxT :=
    nil. (** TODO: define it. *)

  Fixpoint rsDownCovers (eouts: list (Id Msg)): list IdxT :=
    match eouts with
    | nil => nil
    | idm :: eouts' => rsDownCover idm ++ rsDownCovers eouts'
    end.

  Definition AtomicInv (inits eouts: list (Id Msg)) (hst: MHistory) :=
    NoDup (rssOf hst) /\
    SubList (rssOf hst) (rsUpCovers eouts) /\
    DisjList (rssOf hst) (rsDownCovers eouts).

  Lemma atomic_inv:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        steps step_m sys s1 hst s2 ->
        AtomicInv inits eouts hst.
  Proof.
  Admitted.
  
End AtomicInv.

Close Scope list.
Close Scope fmap.

