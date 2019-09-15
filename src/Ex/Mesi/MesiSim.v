Require Import Bool List String Peano_dec.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo Ex.Mesi.MesiInvB Ex.Mesi.MesiInv.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Ltac solve_DisjList_ex dec :=
  repeat (rewrite map_trans; simpl);
  apply (DisjList_spec_1 dec); intros;
  repeat
    match goal with
    | [H: In _ (map _ _) |- _] => apply in_map_iff in H; dest; subst
    end;
  solve_not_in.

(** TODO: refactor; will be used by MOSI as well. *)
Lemma tree2Topo_internal_chns_not_exts:
  forall tr bidx oidx,
    let cifc := snd (tree2Topo tr bidx) in
    In oidx (c_li_indices cifc ++ c_l1_indices cifc) ->
    DisjList [rqUpFrom oidx; rsUpFrom oidx; downTo oidx]
             ((map (fun cidx => rqUpFrom (l1ExtOf cidx)) (c_l1_indices cifc))
                ++ map (fun cidx => downTo (l1ExtOf cidx)) (c_l1_indices cifc)).
Proof.
  intros.
  eapply DisjList_SubList.
  - apply tree2Topo_obj_chns_minds_SubList; eassumption.
  - subst cifc; rewrite <-c_merqs_l1_rqUpFrom, <-c_merss_l1_downTo.
    apply DisjList_comm, DisjList_app_4.
    + apply DisjList_comm, tree2Topo_minds_merqs_disj.
    + apply DisjList_comm, tree2Topo_minds_merss_disj.
Qed.

Lemma tree2Topo_internal_rqUp_exts_disj:
  forall tr bidx cinds,
    let cifc := snd (tree2Topo tr bidx) in
    SubList cinds (c_li_indices cifc ++ c_l1_indices cifc) ->
    DisjList (map rqUpFrom cinds)
             ((map (fun cidx => rqUpFrom (l1ExtOf cidx)) (c_l1_indices cifc))
                ++ map (fun cidx => downTo (l1ExtOf cidx)) (c_l1_indices cifc)).
Proof.
  intros.
  eapply DisjList_SubList with (l1:= c_minds cifc).
  - red; intros.
    apply in_map_iff in H0; dest; subst.
    apply tree2Topo_obj_chns_minds_SubList with (oidx:= x); [auto|].
    simpl; tauto.
  - subst cifc; rewrite <-c_merqs_l1_rqUpFrom, <-c_merss_l1_downTo.
    apply DisjList_comm, DisjList_app_4.
    + apply DisjList_comm, tree2Topo_minds_merqs_disj.
    + apply DisjList_comm, tree2Topo_minds_merss_disj.
Qed.

Lemma tree2Topo_internal_rsUp_exts_disj:
  forall tr bidx cinds,
    let cifc := snd (tree2Topo tr bidx) in
    SubList cinds (c_li_indices cifc ++ c_l1_indices cifc) ->
    DisjList (map rsUpFrom cinds)
             ((map (fun cidx => rqUpFrom (l1ExtOf cidx)) (c_l1_indices cifc))
                ++ map (fun cidx => downTo (l1ExtOf cidx)) (c_l1_indices cifc)).
Proof.
  intros.
  eapply DisjList_SubList with (l1:= c_minds cifc).
  - red; intros.
    apply in_map_iff in H0; dest; subst.
    apply tree2Topo_obj_chns_minds_SubList with (oidx:= x); [auto|].
    simpl; tauto.
  - subst cifc; rewrite <-c_merqs_l1_rqUpFrom, <-c_merss_l1_downTo.
    apply DisjList_comm, DisjList_app_4.
    + apply DisjList_comm, tree2Topo_minds_merqs_disj.
    + apply DisjList_comm, tree2Topo_minds_merss_disj.
Qed.

Lemma tree2Topo_internal_down_exts_disj:
  forall tr bidx cinds,
    let cifc := snd (tree2Topo tr bidx) in
    SubList cinds (c_li_indices cifc ++ c_l1_indices cifc) ->
    DisjList (map downTo cinds)
             ((map (fun cidx => rqUpFrom (l1ExtOf cidx)) (c_l1_indices cifc))
                ++ map (fun cidx => downTo (l1ExtOf cidx)) (c_l1_indices cifc)).
Proof.
  intros.
  eapply DisjList_SubList with (l1:= c_minds cifc).
  - red; intros.
    apply in_map_iff in H0; dest; subst.
    apply tree2Topo_obj_chns_minds_SubList with (oidx:= x); [auto|].
    simpl; tauto.
  - subst cifc; rewrite <-c_merqs_l1_rqUpFrom, <-c_merss_l1_downTo.
    apply DisjList_comm, DisjList_app_4.
    + apply DisjList_comm, tree2Topo_minds_merqs_disj.
    + apply DisjList_comm, tree2Topo_minds_merss_disj.
Qed.



Lemma tree2Topo_li_children_li_l1:
  forall tr bidx oidx,
    In oidx (c_li_indices (snd (tree2Topo tr bidx))) ->
    SubList (subtreeChildrenIndsOf (fst (tree2Topo tr bidx)) oidx)
            (c_li_indices (snd (tree2Topo tr bidx)) ++ c_l1_indices (snd (tree2Topo tr bidx))).
Proof.
  intros; red; intros.
  apply subtreeChildrenIndsOf_parentIdxOf in H0; [|apply tree2Topo_WfDTree].
  eapply tree2Topo_li_child_li_l1; eauto.
Qed.

Lemma tree2Topo_li_RqRsDownMatch_children:
  forall tr bidx oidx,
    In oidx (c_li_indices (snd (tree2Topo tr bidx))) ->
    forall (rssFrom: list (Id Msg)) rqTos P,
      RqRsDownMatch (fst (tree2Topo tr bidx)) oidx rqTos (idsOf rssFrom) P ->
      exists cinds,
        idsOf rssFrom = map rsUpFrom cinds /\
        SubList cinds ((c_li_indices (snd (tree2Topo tr bidx)))
                         ++ c_l1_indices (snd (tree2Topo tr bidx))).
Proof.
  intros.
  pose proof (tree2Topo_TreeTopo tr bidx).
  destruct H1 as [[? _] _].
  pose proof (RqRsDownMatch_rs_rq H0); clear H0.
  apply Forall_forall in H2.
  induction rssFrom; [exists nil; split; [reflexivity|apply SubList_nil]|].
  inv H2; destruct H4 as [cidx [down ?]].
  specialize (IHrssFrom H5); destruct IHrssFrom as [cinds ?]; dest.
  pose proof (tree2Topo_li_child_li_l1 _ _ _ H H3).
  specialize (H1 _ _ H3); dest.
  disc_rule_conds_ex.
  exists (cidx :: cinds).
  split.
  - simpl; congruence.
  - apply SubList_cons; assumption.
Qed.

Ltac solve_in_l1_li :=
  repeat
    match goal with
    | [H: In ?oidx ?l |- In ?oidx ?l] => assumption
    | [H: In ?oidx ?l |- In ?oidx (?l ++ _) ] => apply in_or_app; auto
    | [H: In ?oidx ?l |- In ?oidx (_ ++ ?l) ] => apply in_or_app; auto
    | [H: In ?oidx (tl ?l) |- In ?oidx ?l ] => apply tl_In; assumption
    | [H: In ?oidx (tl ?l) |- In ?oidx (?l ++ _) ] =>
      apply tl_In in H; apply in_or_app; auto
    end.

Ltac solve_not_in_ext_chns :=
  match goal with
  | |- ~ In (_ ?idx) _ =>
    eapply DisjList_In_2;
    [eapply tree2Topo_internal_chns_not_exts with (oidx:= idx);
     solve_in_l1_li; fail
    |simpl; tauto]
  end.

Ltac solve_ext_chns_disj :=
  repeat
    match goal with
    | |- context [idsOf (map _ _)] =>
      unfold idsOf; rewrite map_trans; simpl
    | |- context[fun x => ?f x] => change (fun x => f x) with f
    | |- DisjList (map rqUpFrom _) (map _ (c_l1_indices _) ++ map _ (c_l1_indices _)) =>
      apply tree2Topo_internal_rqUp_exts_disj
    | |- DisjList (map rsUpFrom _) (map _ (c_l1_indices _) ++ map _ (c_l1_indices _)) =>
      apply tree2Topo_internal_rsUp_exts_disj
    | |- DisjList (map downTo _) (map _ (c_l1_indices _) ++ map _ (c_l1_indices _)) =>
      apply tree2Topo_internal_down_exts_disj
    | [H: SubList ?inds _ |- SubList ?inds _] =>
      first [assumption|eapply SubList_trans; [eassumption|]]
    | |- SubList (subtreeChildrenIndsOf _ _) (c_li_indices _ ++ c_l1_indices _) =>
      apply tree2Topo_li_children_li_l1; solve_in_l1_li; fail
    end.

(** TODO: refactor; will be used by MOSI as well. *)
Section SimExtMP.
  Variable (l1s: list IdxT).

  Let erqs := map (fun cidx => rqUpFrom (l1ExtOf cidx)) l1s.
  Let erss := map (fun cidx => downTo (l1ExtOf cidx)) l1s.

  Definition SimExtMP (imsgs: MessagePool Msg) (iorqs: ORqs Msg)
             (smsgs: MessagePool Msg) :=
    Forall
      (fun cidx =>
         let eidx := l1ExtOf cidx in
         (corq <-- iorqs@[cidx];
            (corq@[upRq] >>= (fun rqiu => rqiu.(rqi_msg)))
              ::> (findQ (rqUpFrom eidx) imsgs) = findQ (rqUpFrom eidx) smsgs) /\
         findQ (downTo eidx) imsgs = findQ (downTo eidx) smsgs)
      l1s.

  Ltac disc_SimExtMP :=
    unfold SimExtMP; intros;
    repeat
      match goal with
      | [ |- Forall _ l1s] =>
        let cidx := fresh "cidx" in
        let He := fresh "He" in
        apply Forall_forall; intros cidx He
      | [H1: Forall _ l1s, H2: In _ l1s |- _] =>
        rewrite Forall_forall in H1; specialize (H1 _ H2)
      end.

  Lemma SimExtMP_enqMsgs:
    forall eins,
      NoDup (idsOf eins) ->
      forall imsgs orqs smsgs,
        SimExtMP imsgs orqs smsgs ->
        SimExtMP (enqMsgs eins imsgs) orqs (enqMsgs eins smsgs).
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    repeat split.
    - destruct (in_dec idx_dec (rqUpFrom (l1ExtOf cidx)) (idsOf eins)).
      + apply in_map_iff in i.
        destruct i as [[midx msg] ?]; dest; simpl in *; subst.
        do 2 (erewrite findQ_In_NoDup_enqMsgs; eauto).
        rewrite ocons_app; congruence.
      + do 2 (rewrite findQ_not_In_enqMsgs by assumption).
        assumption.
    - destruct (in_dec idx_dec (downTo (l1ExtOf cidx)) (idsOf eins)).
      + apply in_map_iff in i.
        destruct i as [[midx msg] ?]; dest; simpl in *; subst.
        do 2 (erewrite findQ_In_NoDup_enqMsgs; eauto).
        congruence.
      + do 2 (rewrite findQ_not_In_enqMsgs by assumption).
        assumption.
  Qed.

  Corollary SimExtMP_enqMP:
    forall midx msg imsgs orqs smsgs,
      SimExtMP imsgs orqs smsgs ->
      SimExtMP (enqMP midx msg imsgs) orqs (enqMP midx msg smsgs).
  Proof.
    intros.
    eapply SimExtMP_enqMsgs with (eins:= [(midx, msg)]) in H; auto.
    repeat constructor; intro; dest_in.
  Qed.

  Lemma SimExtMP_orqs:
    forall imsgs orqs1 orqs2 smsgs,
      SimExtMP imsgs orqs1 smsgs ->
      Forall (fun cidx => orqs1@[cidx] = orqs2@[cidx]) l1s ->
      SimExtMP imsgs orqs2 smsgs.
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
  Qed.

  Lemma SimExtMP_ext_outs_deqMsgs:
    forall eouts,
      SubList (idsOf eouts) erss ->
      NoDup (idsOf eouts) ->
      forall imsgs orqs smsgs,
        Forall (FirstMPI imsgs) eouts ->
        SimExtMP imsgs orqs smsgs ->
        SimExtMP (deqMsgs (idsOf eouts) imsgs) orqs (deqMsgs (idsOf eouts) smsgs).
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    repeat split.
    - destruct (in_dec idx_dec (rqUpFrom (l1ExtOf cidx)) (idsOf eouts)).
      + exfalso.
        apply H in i.
        apply in_map_iff in i; dest.
        discriminate.
      + do 2 (rewrite findQ_not_In_deqMsgs by assumption).
        assumption.
    - destruct (in_dec idx_dec (downTo (l1ExtOf cidx)) (idsOf eouts)).
      + apply in_map_iff in i; destruct i as [[midx msg] ?]; dest.
        simpl in *; subst.
        apply findQ_deqMsgs_eq; assumption.
      + do 2 (rewrite findQ_not_In_deqMsgs by assumption).
        assumption.
  Qed.

  Lemma SimExtMP_ext_outs_FirstMPI:
    forall eouts,
      SubList (idsOf eouts) erss ->
      NoDup (idsOf eouts) ->
      forall imsgs orqs smsgs,
        SimExtMP imsgs orqs smsgs ->
        Forall (FirstMPI imsgs) eouts ->
        Forall (FirstMPI smsgs) eouts.
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    apply Forall_forall; intros [midx msg] ?.
    rewrite Forall_forall in H2; specialize (H2 _ H3).
    apply in_map with (f:= idOf) in H3.
    apply H in H3; unfold idOf, fst in H3.
    apply in_map_iff in H3; destruct H3 as [cidx ?]; dest; subst.
    rewrite Forall_forall in H1; specialize (H1 _ H4); dest.
    unfold FirstMPI, FirstMP, firstMP in *; simpl in *.
    congruence.
  Qed.

  Lemma SimExtMP_outs_deqMP_child:
    forall cidx msg imsgs (orqs: ORqs Msg) smsgs corq,
      In cidx l1s ->
      orqs@[cidx] = Some corq ->
      corq@[upRq] = None ->
      FirstMPI imsgs (rqUpFrom (l1ExtOf cidx), msg) ->
      SimExtMP imsgs orqs smsgs ->
      SimExtMP (deqMP (rqUpFrom (l1ExtOf cidx)) imsgs) orqs
               (deqMP (rqUpFrom (l1ExtOf cidx)) smsgs).
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    destruct (idx_dec cidx cidx0); subst.
    - disc_rule_conds_ex.
      pose proof (findQ_eq_FirstMPI H2 _ H3).
      apply findQ_In_deqMP_FirstMP in H2.
      apply findQ_In_deqMP_FirstMP in H5; simpl in *.
      rewrite <-H2, <-H5 in H3; inv H3.
      split; auto.
      do 2 (rewrite findQ_not_In_deqMP by (intro; subst; discriminate)).
      assumption.
    - do 2 (rewrite findQ_not_In_deqMP
             by (intro Hx; injection Hx; intros; auto)).
      do 2 (rewrite findQ_not_In_deqMP by (intro; subst; discriminate)).
      split; assumption.
  Qed.
  
  Lemma SimExtMP_impl_enqMP_indep:
    forall midx msg imsgs (orqs: ORqs Msg) smsgs,
      ~ In midx (erqs ++ erss) ->
      SimExtMP imsgs orqs smsgs ->
      SimExtMP (enqMP midx msg imsgs) orqs smsgs.
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    split.
    - rewrite findQ_not_In_enqMP; [assumption|].
      intro; subst.
      elim H; apply in_or_app; left.
      apply in_map with (f:= fun cidx => rqUpFrom (l1ExtOf cidx)) in He.
      assumption.
    - rewrite findQ_not_In_enqMP; [assumption|].
      intro; subst.
      elim H. apply in_or_app; right.
      apply in_map with (f:= fun cidx => downTo (l1ExtOf cidx)) in He.
      assumption.
  Qed.

  Lemma SimExtMP_impl_enqMsgs_indep:
    forall nmsgs imsgs (orqs: ORqs Msg) smsgs,
      DisjList (idsOf nmsgs) (erqs ++ erss) ->
      SimExtMP imsgs orqs smsgs ->
      SimExtMP (enqMsgs nmsgs imsgs) orqs smsgs.
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    split.
    - rewrite findQ_not_In_enqMsgs; [assumption|].
      eapply DisjList_In_1; [eassumption|].
      apply in_or_app; left.
      apply in_map with (f:= fun cidx => rqUpFrom (l1ExtOf cidx)) in He.
      assumption.
    - rewrite findQ_not_In_enqMsgs; [assumption|].
      eapply DisjList_In_1; [eassumption|].
      apply in_or_app; right.
      apply in_map with (f:= fun cidx => downTo (l1ExtOf cidx)) in He.
      assumption.
  Qed.

  Lemma SimExtMP_impl_deqMP_indep:
    forall midx imsgs (orqs: ORqs Msg) smsgs,
      ~ In midx (erqs ++ erss) ->
      SimExtMP imsgs orqs smsgs ->
      SimExtMP (deqMP midx imsgs) orqs smsgs.
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    split.
    - rewrite findQ_not_In_deqMP; [assumption|].
      intro; subst.
      elim H; apply in_or_app; left.
      apply in_map with (f:= fun cidx => rqUpFrom (l1ExtOf cidx)) in He.
      assumption.
    - rewrite findQ_not_In_deqMP; [assumption|].
      intro; subst.
      elim H. apply in_or_app; right.
      apply in_map with (f:= fun cidx => downTo (l1ExtOf cidx)) in He.
      assumption.
  Qed.

  Lemma SimExtMP_impl_deqMsgs_indep:
    forall minds imsgs (orqs: ORqs Msg) smsgs,
      DisjList minds (erqs ++ erss) ->
      SimExtMP imsgs orqs smsgs ->
      SimExtMP (deqMsgs minds imsgs) orqs smsgs.
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    split.
    - rewrite findQ_not_In_deqMsgs; [assumption|].
      eapply DisjList_In_1; [eassumption|].
      apply in_or_app; left.
      apply in_map with (f:= fun cidx => rqUpFrom (l1ExtOf cidx)) in He.
      assumption.
    - rewrite findQ_not_In_deqMsgs; [assumption|].
      eapply DisjList_In_1; [eassumption|].
      apply in_or_app; right.
      apply in_map with (f:= fun cidx => downTo (l1ExtOf cidx)) in He.
      assumption.
  Qed.

  Lemma SimExtMP_impl_silent_locked:
    forall imsgs (orqs: ORqs Msg) smsgs,
      SimExtMP imsgs orqs smsgs ->
      forall oidx porq norq,
        orqs@[oidx] = Some porq -> porq@[upRq] = None ->
        (norq@[upRq] >>= (fun rqiu => rqiu.(rqi_msg)) = None) ->
        SimExtMP imsgs (orqs +[oidx <- norq]) smsgs.
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    split; assumption.
  Qed.

  Lemma SimExtMP_impl_silent_unlocked:
    forall cidx imsgs (orqs: ORqs Msg) smsgs porq rqiu norq,
      orqs@[cidx] = Some porq ->
      porq@[upRq] = Some rqiu -> rqiu.(rqi_msg) = None ->
      norq@[upRq] = None ->
      SimExtMP imsgs orqs smsgs ->
      SimExtMP imsgs (orqs +[cidx <- norq]) smsgs.
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
  Qed.

  Lemma SimExtMP_spec_deqMP_locked:
    forall cidx imsgs (orqs: ORqs Msg) smsgs porq norq rqiu msg,
      orqs@[cidx] = Some porq ->
      porq@[upRq] = None -> norq@[upRq] = Some rqiu ->
      FirstMPI imsgs (rqUpFrom (l1ExtOf cidx), msg) ->
      rqiu.(rqi_msg) = Some msg ->
      SimExtMP imsgs orqs smsgs ->
      SimExtMP (deqMP (rqUpFrom (l1ExtOf cidx)) imsgs)
               (orqs +[cidx <- norq]) smsgs.
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    - split.
      + rewrite findQ_In_deqMP_FirstMP; assumption.
      + rewrite findQ_not_In_deqMP by discriminate; assumption.
    - split.
      + rewrite findQ_not_In_deqMP
          by (intro Hx; subst; injection Hx; intros; auto).
        assumption.
      + rewrite findQ_not_In_deqMP by (intro; subst; discriminate).
        assumption.
  Qed.

  Lemma SimExtMP_spec_deqMP_unlocked:
    forall cidx imsgs (orqs: ORqs Msg) smsgs porq rqiu norq,
      orqs@[cidx] = Some porq ->
      porq@[upRq] = Some rqiu -> rqiu.(rqi_msg) <> None ->
      norq@[upRq] = None ->
      SimExtMP imsgs orqs smsgs ->
      SimExtMP imsgs (orqs +[cidx <- norq]) (deqMP (rqUpFrom (l1ExtOf cidx)) smsgs).
  Proof.
    disc_SimExtMP.
    disc_rule_conds_ex.
    - split.
      + destruct (rqi_msg rqiu); [|exfalso; auto].
        unfold deqMP, findQ in *; simpl in *.
        rewrite <-H3; mred.
      + rewrite findQ_not_In_deqMP by discriminate; assumption.
    - split.
      + rewrite findQ_not_In_deqMP
          by (intro Hx; subst; injection Hx; intros; auto).
        assumption.
      + rewrite findQ_not_In_deqMP by (intro; subst; discriminate).
        assumption.
  Qed.
  
End SimExtMP.

Section Sim.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo := fst (tree2Topo tr 0).
  Let cifc := snd (tree2Topo tr 0).
  Let impl := Mesi.impl Htr.

  Axiom c_l1_indices_NoPrefix: NoPrefix (c_l1_indices cifc).
  Local Definition spec := @SpecInds.spec (c_l1_indices cifc) c_l1_indices_NoPrefix.

  Existing Instance Mesi.ImplOStateIfc.

  (** NOTE: simulation only states about coherent values. 
   * Exclusiveness is stated and proven as an invariant. *)

  Section ObjCoh.
    Variables (cv: nat)
              (cidx: IdxT)
              (cost: OState)
              (msgs: MessagePool Msg).

    Definition cohMsgs: list (MSig * (Id Msg -> Prop)) :=
      (| (downTo cidx, (MRs, mesiRsS)): fun idm => (valOf idm).(msg_value) = cv
       | (downTo cidx, (MRs, mesiRsE)): fun idm => (valOf idm).(msg_value) = cv
       | (rsUpFrom cidx, (MRs, mesiDownRsS)): fun idm => (valOf idm).(msg_value) = cv)%cases.

    Definition MsgCoh := MsgP cohMsgs.
    Definition MsgsCoh := MsgsP cohMsgs msgs.

    Definition ObjCoh :=
      ImplOStateMESI cidx cost msgs cv /\ MsgsCoh.

  End ObjCoh.

  Section ObjCohFacts.

    Lemma ObjInvalid_ObjCoh:
      forall oidx orq ost msgs (Hrsi: RsDownConflicts oidx orq msgs),
        ObjInvalid oidx ost msgs ->
        forall cv, ObjCoh cv oidx ost msgs.
    Proof.
      unfold ObjInvalid, ObjCoh; intros.
      destruct H.
      - red in H; dest; split.
        + red; intros; rewrite H in H1; solve_mesi.
        + do 2 red; intros.
          specialize (H0 _ H1); red in H0.
          red; unfold cohMsgs, map, caseDec, fst in *.
          repeat (find_if_inside; [exfalso; auto; fail|]).
          auto.

      - split.
        + red; intros.
          exfalso; eapply NoRsI_MsgExistsSig_InvRs_false; eauto.
        + destruct H as [idm [? ?]].
          red; intros.
          specialize (Hrsi idm ltac:(rewrite H0; reflexivity)
                                      ltac:(rewrite H0; reflexivity) H); dest.
          red; intros.
          red; unfold cohMsgs, map, caseDec, fst.
          repeat find_if_inside; [..|auto].
          * exfalso; eapply (H3 idm0); try rewrite H0; try rewrite e; auto.
            destruct idm as [midx msg], idm0 as [midx0 msg0].
            simpl in *; inv H0; inv e.
            intro; subst; rewrite H10 in H11; discriminate.
          * exfalso; eapply (H3 idm0); try rewrite H0; try rewrite e; auto.
            destruct idm as [midx msg], idm0 as [midx0 msg0].
            simpl in *; inv H0; inv e.
            intro; subst; rewrite H10 in H11; discriminate.
          * exfalso; eapply H5; try rewrite e; eauto.
    Qed.

    Lemma ObjExcl0_ObjCoh:
      forall oidx ost msgs,
        InvObjExcl0 oidx ost msgs ->
        ObjExcl0 oidx ost msgs ->
        ObjCoh ost#[val] oidx ost msgs.
    Proof.
      unfold InvObjExcl0, CohInvRq, CohPushRq, ObjCoh; intros.
      specialize (H H0).
      split; [red; intros; reflexivity|].
      do 2 red; intros.
      specialize (H _ H1); red in H.
      red; unfold cohMsgs, map, caseDec, fst in *.
      repeat (find_if_inside; [exfalso; auto; fail|]).
      auto.
    Qed.

    Lemma MsgsCoh_enqMP:
      forall cv cidx msgs,
        MsgsCoh cv cidx msgs ->
        forall midx msg,
          MsgCoh cv cidx (midx, msg) ->
          MsgsCoh cv cidx (enqMP midx msg msgs).
    Proof.
      intros; apply MsgsP_enqMP; auto.
    Qed.

    Lemma MsgsCoh_other_midx_enqMP:
      forall cv cidx msgs,
        MsgsCoh cv cidx msgs ->
        forall midx msg,
          ~ In midx [rqUpFrom cidx; rsUpFrom cidx; downTo cidx] ->
          MsgsCoh cv cidx (enqMP midx msg msgs).
    Proof.
      intros.
      apply MsgsP_other_midx_enqMP; auto.
      intro Hx; elim H0; dest_in; simpl; tauto.
    Qed.

    Lemma MsgsCoh_other_midx_enqMsgs:
      forall cv cidx msgs,
        MsgsCoh cv cidx msgs ->
        forall eins,
          DisjList (idsOf eins) [rqUpFrom cidx; rsUpFrom cidx; downTo cidx] ->
          MsgsCoh cv cidx (enqMsgs eins msgs).
    Proof.
      intros.
      apply MsgsP_other_midx_enqMsgs; auto.
      simpl.
      eapply DisjList_comm, DisjList_SubList;
        [|apply DisjList_comm; eassumption].
      solve_SubList.
    Qed.

    Lemma MsgsCoh_other_msg_id_enqMP:
      forall cv cidx msgs,
        MsgsCoh cv cidx msgs ->
        forall midx msg,
          ~ In (msg_id msg) [mesiRsS; mesiRsE; mesiDownRsS] ->
          MsgsCoh cv cidx (enqMP midx msg msgs).
    Proof.
      intros; apply MsgsP_other_msg_id_enqMP; auto.
    Qed.

    Lemma MsgsCoh_other_msg_id_enqMsgs:
      forall cv cidx msgs,
        MsgsCoh cv cidx msgs ->
        forall eins,
          DisjList (map (fun idm => msg_id (valOf idm)) eins)
                   [mesiRsS; mesiRsE; mesiDownRsS] ->
          MsgsCoh cv cidx (enqMsgs eins msgs).
    Proof.
      intros; apply MsgsP_other_msg_id_enqMsgs; auto.
    Qed.

    Lemma MsgsCoh_deqMP:
      forall cv cidx msgs,
        MsgsCoh cv cidx msgs ->
        forall midx,
          MsgsCoh cv cidx (deqMP midx msgs).
    Proof.
      intros; apply MsgsP_deqMP; auto.
    Qed.

    Lemma MsgsCoh_deqMsgs:
      forall cv cidx msgs,
        MsgsCoh cv cidx msgs ->
        forall minds,
          MsgsCoh cv cidx (deqMsgs minds msgs).
    Proof.
      intros; apply MsgsP_deqMsgs; auto.
    Qed.

  End ObjCohFacts.

  Definition ImplStateCoh (cv: nat) (st: MState): Prop :=
    Forall (fun oidx =>
              ost <-- (bst_oss st)@[oidx];
                _ <-- (bst_orqs st)@[oidx];
                ObjCoh cv oidx ost (bst_msgs st))
           (c_li_indices cifc ++ c_l1_indices cifc).

  Definition SpecStateCoh (cv: nat) (st: @MState SpecOStateIfc): Prop :=
    sost <-- (bst_oss st)@[specIdx];
      sorq <-- (bst_orqs st)@[specIdx];
      sost#[specValueIdx] = cv.

  Inductive SimState: MState -> @MState SpecOStateIfc -> Prop :=
  | SimStateIntro:
      forall cv ist sst,
        SpecStateCoh cv sst ->
        ImplStateCoh cv ist ->
        SimState ist sst.

  Definition SimMESI (ist: MState) (sst: @MState SpecOStateIfc): Prop :=
    SimState ist sst /\
    SimExtMP (c_l1_indices cifc) ist.(bst_msgs) ist.(bst_orqs) sst.(bst_msgs).

  Hint Unfold ObjCoh ImplStateCoh: RuleConds.

  Lemma mesi_sim_init:
    SimMESI (initsOf impl) (initsOf spec).
  Proof.
    split.
    - apply SimStateIntro with (cv:= 0).
      + reflexivity.
      + apply Forall_forall; intros oidx ?.
        subst cifc; rewrite c_li_indices_head_rootOf in H by assumption.
        simpl in H; icase oidx.
        * simpl; rewrite implOStatesInit_value_root by assumption.
          unfold implORqsInit; simpl.
          rewrite initORqs_value
            by (rewrite c_li_indices_head_rootOf by assumption; left; reflexivity).
          simpl; split; [compute; auto|].
          do 3 red; intros.
          do 2 red in H0; dest_in.
        * simpl; rewrite implOStatesInit_value_non_root by assumption.
          unfold implORqsInit; simpl.
          rewrite initORqs_value
            by (rewrite c_li_indices_head_rootOf by assumption; right; assumption).
          simpl; split; [compute; auto|].
          do 3 red; intros.
          do 2 red in H0; dest_in.
    - red; apply Forall_forall; intros oidx ?.
      repeat split.
      simpl; unfold implORqsInit.
      rewrite initORqs_value; [|apply in_or_app; auto].
      simpl; mred.
  Qed.

  Lemma mesi_sim_silent:
    forall ist sst1,
      SimMESI ist sst1 ->
      exists slbl sst2,
        getLabel (RlblEmpty Msg) = getLabel slbl /\
        step_m spec sst1 slbl sst2 /\ SimMESI ist sst2.
  Proof.
    simpl; intros.
    exists (RlblEmpty _); eexists.
    repeat ssplit; eauto.
    constructor.
  Qed.

  Lemma sim_mesi_ext_in:
    forall oss orqs msgs sst1,
      SimMESI {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} sst1 ->
      forall eins,
        eins <> nil -> ValidMsgsExtIn impl eins ->
        exists slbl sst2,
          getLabel (RlblIns eins) = getLabel slbl /\
          step_m spec sst1 slbl sst2 /\
          SimMESI {| bst_oss := oss;
                     bst_orqs := orqs;
                     bst_msgs := enqMsgs eins msgs |} sst2.
  Proof.
    destruct sst1 as [soss1 sorqs1 smsgs1]; simpl; intros.
    red in H; simpl in *; dest.
    exists (RlblIns eins); eexists.
    repeat ssplit.
    + reflexivity.
    + eapply SmIns; eauto.
      destruct H1; split; [|assumption].
      simpl in *; rewrite c_merqs_l1_rqUpFrom in H1.
      assumption.
    + split.
      * inv H.
        apply SimStateIntro with (cv:= cv); [assumption|].
        red in H4; simpl in H4.
        apply Forall_forall; intros oidx ?.
        rewrite Forall_forall in H4; specialize (H4 _ H).
        disc_rule_conds_ex.
        split.
        { intros; apply H4; auto.
          eapply MsgsP_enqMsgs_inv; eauto.
        }              
        { apply MsgsCoh_other_midx_enqMsgs; [assumption|].
          destruct H1; simpl in H1.
          eapply DisjList_SubList; [eassumption|].
          apply DisjList_comm, DisjList_SubList with (l1:= c_minds (snd (tree2Topo tr 0))).
          { apply tree2Topo_obj_chns_minds_SubList; auto. }
          { apply tree2Topo_minds_merqs_disj. }
        }
      * apply SimExtMP_enqMsgs; auto.
        apply H1.
  Qed.

  Lemma sim_mesi_ext_out:
    forall oss orqs msgs sst1,
      SimMESI {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} sst1 ->
      forall eouts: list (Id Msg),
        eouts <> nil ->
        Forall (FirstMPI msgs) eouts ->
        ValidMsgsExtOut impl eouts ->
        exists slbl sst2,
          getLabel (RlblOuts eouts) = getLabel slbl /\
          step_m spec sst1 slbl sst2 /\
          SimMESI {| bst_oss := oss;
                     bst_orqs := orqs;
                     bst_msgs := deqMsgs (idsOf eouts) msgs |} sst2.
  Proof.
    destruct sst1 as [soss1 sorqs1 smsgs1]; simpl; intros.
    red in H; simpl in *; dest.
    destruct H2; unfold impl in H2; simpl in H2.
    exists (RlblOuts eouts); eexists.
    repeat ssplit.
    - reflexivity.
    - rewrite c_merss_l1_downTo in H2.
      eapply SmOuts with (msgs0:= smsgs1); eauto.
      + eapply SimExtMP_ext_outs_FirstMPI; eauto.
      + split; assumption.
    - split.
      + inv H.
        apply SimStateIntro with (cv:= cv); [assumption|].
        red in H6; simpl in H6.
        apply Forall_forall; intros oidx ?.
        rewrite Forall_forall in H6; specialize (H6 _ H).
        disc_rule_conds_ex.
        split.
        { intros; apply H6; auto.
          eapply MsgsP_other_midx_deqMsgs_inv; [eassumption|].
          simpl.
          apply DisjList_comm, DisjList_SubList with (l1:= c_minds (snd (tree2Topo tr 0))).
          { eapply SubList_trans;
              [|apply tree2Topo_obj_chns_minds_SubList; eauto].
            solve_SubList.
          }
          { eapply DisjList_comm, DisjList_SubList; [eassumption|].
            apply DisjList_comm, tree2Topo_minds_merss_disj.
          }
        }
        { apply MsgsCoh_deqMsgs; assumption. }
      + rewrite c_merss_l1_downTo in H2.
        apply SimExtMP_ext_outs_deqMsgs; auto.
  Qed.

  Ltac disc_MsgsCoh_by_FirstMP Hd Hf :=
    specialize (Hd _ (FirstMP_InMP Hf));
    red in Hd;
    cbv [map cohMsgs] in Hd;
    cbv [sigOf idOf valOf fst snd] in Hd;
    match type of Hf with
    | FirstMPI _ (_, ?msg) =>
      match goal with
      | [H1: msg_id ?msg = _, H2: msg_type ?msg = _ |- _] =>
        rewrite H1, H2 in Hd
      end
    end;
    disc_caseDec Hd.

  Ltac spec_constr_step_FirstMPI :=
    repeat constructor;
    repeat
      match goal with
      | [H: SimExtMP _ _ _ _ |- _] => red in H
      | [Hf: Forall _ ?l, Hin: In _ ?l |- _] =>
        rewrite Forall_forall in Hf; specialize (Hf _ Hin);
        disc_rule_conds_const; dest
      | [H: _ :: findQ ?eidx _ = findQ ?eidx ?msgs |-
         FirstMPI ?msgs (?eidx, _) ] =>
        unfold FirstMPI, FirstMP, firstMP;
        simpl; rewrite <-H; reflexivity
      | [H: findQ ?eidx _ = findQ ?eidx ?msgs |-
         FirstMPI ?msgs (?eidx, _) ] =>
        eapply findQ_eq_FirstMPI; eauto; fail
      end.

  Ltac spec_constr_step_ValidMsgs :=
    match goal with
    | [H: In _ (c_l1_indices _) |- _] =>
      clear -H; split;
      [simpl; apply SubList_cons; [|apply SubList_nil];
       apply in_map with (f:= fun cidx => _ (l1ExtOf cidx));
       assumption|
       repeat constructor; intro; dest_in]
    end.

  Ltac spec_constr_step_get cidx :=
    eapply SmInt with (ins:= [(rqUpFrom (l1ExtOf cidx), _)]);
    try reflexivity;
    [left; reflexivity
    |simpl; apply specGetRq_in_specRules, in_map; assumption
    |reflexivity
    |eassumption
    |eassumption
    |spec_constr_step_FirstMPI
    |spec_constr_step_ValidMsgs
    |solve_rule_conds_ex;
     match goal with
     | [H: msg_id ?msg = _ |- context[msg_id ?msg] ] => rewrite H
     end; reflexivity
    |spec_constr_step_ValidMsgs
    |solve_DisjList idx_dec].

  Ltac spec_constr_step_set cidx :=
    eapply SmInt with (ins:= [(rqUpFrom (l1ExtOf cidx), _)]);
    try reflexivity;
    [left; reflexivity
    |simpl; apply specSetRq_in_specRules, in_map; assumption
    |reflexivity
    |eassumption
    |eassumption
    |spec_constr_step_FirstMPI
    |spec_constr_step_ValidMsgs
    |solve_rule_conds_ex;
     match goal with
     | [H: msg_id ?msg = _ |- context[msg_id ?msg] ] => rewrite H
     end; reflexivity
    |spec_constr_step_ValidMsgs
    |solve_DisjList idx_dec].

  Ltac spec_case_get cidx :=
    eexists (RlblInt specIdx (rule_idx (specGetRq (l1ExtOf cidx))) _ _);
    eexists;
    repeat ssplit;
    [reflexivity|spec_constr_step_get cidx|].

  Ltac spec_case_set cidx :=
    eexists (RlblInt specIdx (rule_idx (specSetRq (l1ExtOf cidx))) _ _);
    eexists;
    repeat ssplit;
    [reflexivity|spec_constr_step_set cidx|].
  
  Ltac spec_case_silent :=
    idtac; exists (RlblEmpty _); eexists;
    repeat ssplit;
    [reflexivity
    |econstructor
    |].

  Ltac solve_sim_ext_mp :=
    repeat
      (try
         match goal with
         | [ |- SimExtMP _ (enqMP _ _ _) _ (enqMP _ _ _) ] =>
           apply SimExtMP_enqMP
         | [ |- SimExtMP _ (deqMP ?midx _) _ (deqMP ?midx _) ] =>
           eapply SimExtMP_outs_deqMP_child; eauto; mred; fail
         | [ |- SimExtMP _ (enqMP _ _ _) _ _ ] =>
           apply SimExtMP_impl_enqMP_indep; [solve_not_in_ext_chns; fail|]
         | [ |- SimExtMP _ (deqMP _ _) _ _ ] =>
           eapply SimExtMP_spec_deqMP_locked; eauto; [mred|reflexivity]; fail
         | [ |- SimExtMP _ (deqMP _ _) _ _ ] =>
           apply SimExtMP_impl_deqMP_indep; [solve_not_in_ext_chns; fail|]
         | [ |- SimExtMP _ _ _ (deqMP _ _) ] =>
           eapply SimExtMP_spec_deqMP_unlocked; eauto; [congruence|mred]; fail
         | [ |- SimExtMP _ (enqMsgs _ _) _ _ ] =>
           apply SimExtMP_impl_enqMsgs_indep; [solve_ext_chns_disj; fail|]
         | [ |- SimExtMP _ (deqMsgs _ _) _ _ ] =>
           apply SimExtMP_impl_deqMsgs_indep; [solve_ext_chns_disj; fail|]
         | [ |- SimExtMP _ _ (?m +[?k <- ?v]) _ ] =>
           apply SimExtMP_orqs with (orqs1:= m);
           [|apply Forall_forall; intros; mred; fail]
         | [ |- SimExtMP _ _ (_ +[_ <- addRqS _ _ _]) _] =>
           eapply SimExtMP_impl_silent_locked;
           [|eassumption|eassumption|unfold addRqS; mred]
         | [H1: ?porq@[upRq] = Some ?rqi, H2: rqi_msg ?rqi = None
            |- SimExtMP _ _ (_ +[_ <- ?porq -[upRq]]) _] =>
           eapply SimExtMP_impl_silent_unlocked; eauto; mred; fail
         end; try assumption).

  Ltac disc_rule_custom ::=
    repeat
      match goal with
      (* get simulation propositions for the current impl. state *)
      | [Hf: Forall _ (c_li_indices ?cifc ++ c_l1_indices ?cifc),
             Hin: In ?oidx (c_li_indices ?cifc)
         |- context[SimMESI {| bst_oss := _ +[?oidx <- _] |} _]] =>
        rewrite Forall_forall in Hf;
        pose proof (Hf _ (in_or_app _ _ _ (or_introl Hin)))
      | [Hf: Forall _ (c_li_indices ?cifc ++ c_l1_indices ?cifc),
             Hin: In ?oidx (tl (c_li_indices ?cifc))
         |- context[SimMESI {| bst_oss := _ +[?oidx <- _] |} _]] =>
        rewrite Forall_forall in Hf;
        pose proof (Hf _ (in_or_app _ _ _ (or_introl (tl_In _ _ Hin))))
      | [Hf: Forall _ (c_li_indices ?cifc ++ c_l1_indices ?cifc),
             Hin: In ?oidx (c_l1_indices ?cifc)
         |- context[SimMESI {| bst_oss := _ +[?oidx <- _] |} _]] =>
        rewrite Forall_forall in Hf;
        pose proof (Hf _ (in_or_app _ _ _ (or_intror Hin)))
      (* rewrite a coherent value *)
      | [H: fst ?ost = fst _ |- context[fst ?ost] ] => rewrite H in *
      (* rewrite inputs/outputs message ids *)
      | [H: msg_id ?rmsg = _ |- context[msg_id ?rmsg] ] => rewrite H
      end.
  
  (*! To solve [SimMESI] *)

  Ltac solve_ImplStateCoh :=
    idtac.
  
  Ltac solve_SpecStateCoh :=
    eapply SimStateIntro; [solve_rule_conds_ex|].
  
  Ltac solve_sim_mesi_ext_mp :=
    red; simpl; split; [|solve_sim_ext_mp].

  Ltac solve_sim_mesi :=
    solve_sim_mesi_ext_mp;
    solve_SpecStateCoh;
    solve_ImplStateCoh.

  Ltac solve_chn_not_in :=
    intro; dest_in; try discriminate; simpl in *;
    repeat
      match goal with
      | [H: rqUpFrom _ = rqUpFrom _ |- _] => inv H
      | [H: rsUpFrom _ = rsUpFrom _ |- _] => inv H
      | [H: downTo _ = downTo _ |- _] => inv H
      | [H: ?oidx = l1ExtOf ?oidx |- _] =>
        exfalso; eapply l1ExtOf_not_eq; eauto
      | [H:parentIdxOf _ ?oidx = Some ?oidx |- _] =>
        exfalso; eapply parentIdxOf_not_eq with (idx:= oidx) (pidx:= oidx); eauto
      end; auto.

  Ltac disc_MsgsP H :=
    repeat
      (first [apply MsgsP_enqMsgs_inv in H
             |apply MsgsP_enqMP_inv in H
             |apply MsgsP_other_midx_deqMsgs_inv in H; [|solve_DisjList_ex idx_dec]
             |apply MsgsP_other_midx_deqMP_inv in H; [|solve_chn_not_in; fail]
             |eapply MsgsP_other_msg_id_deqMP_inv in H;
              [|eassumption
               |unfold valOf, snd;
                match goal with
                | [Hi: msg_id ?rmsg = _, Hf: FirstMPI _ (_, ?rmsg) |- _] =>
                  rewrite Hi; solve_not_in
                end]
      ]).

  Ltac solve_ImplOStateMESI :=
    intros;
    auto; try solve_mesi; (* can be solved automatically? *)
    match goal with
    | [H: _ -> ?P |- ?P] => apply H; auto
    | [H: _ -> _ -> ?P |- ?P] => apply H; auto
    end;
    try match goal with
        | H:MsgsP ?P _ |- MsgsP ?P _ => disc_MsgsP H; assumption
        end;
    try solve_mesi.

  Ltac solve_MsgsCoh :=
    repeat
      (try match goal with
           | |- MsgsCoh _ _ (enqMP _ _ _) =>
             apply MsgsCoh_other_midx_enqMP;
             [|solve_chn_not_in; auto; fail]
           | |- MsgsCoh _ _ (enqMP _ _ _) =>
             apply MsgsCoh_other_msg_id_enqMP; [|solve_not_in]
           | |- MsgsCoh _ _ (enqMP _ _ _) =>
             apply MsgsCoh_enqMP;
             [|do 2 red; cbv [map cohMsgs]; solve_caseDec; reflexivity]
           | |- MsgsCoh _ _ (enqMsgs _ _) =>
             apply MsgsCoh_other_msg_id_enqMsgs; [|solve_DisjList_ex idx_dec]
           | |- MsgsCoh _ _ (deqMP _ _) => apply MsgsCoh_deqMP
           | |- MsgsCoh _ _ (deqMsgs _ _) => apply MsgsCoh_deqMsgs
           end; try eassumption).

  Ltac solve_NoRsI_base :=
    repeat
      match goal with
      | |- NoRsI _ _ => do 3 red; intros
      | |- MsgP _ _ =>
        red; unfold cohMsgs, map, caseDec, fst;
        repeat (find_if_inside; [simpl|auto])
      | [H: sigOf ?idm = _ |- _] =>
        let midx := fresh "midx" in
        let msg := fresh "msg" in
        destruct idm as [midx msg]; inv H
      end.

  Ltac solve_NoRsI_by_no_locks oidx :=
    repeat
      match goal with
      | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
                Hin: In oidx (c_l1_indices _),
                     Horq: ?orqs@[oidx] = Some _ |- _] =>
        specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_intror Hin)) Horq);
        simpl in Hmcfi; destruct Hmcfi
      | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
                Hin: In oidx (tl (c_li_indices _)),
                     Horq: ?orqs@[oidx] = Some _ |- _] =>
        specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_introl (tl_In _ _ Hin))) Horq);
        simpl in Hmcfi; destruct Hmcfi
      | [Hmcf: RsDownConflicts oidx _ ?msgs,
               Hinm: InMPI ?msgs (?midx, ?msg),
                     Hmt: msg_type ?msg = MRs |- _] =>
        specialize (Hmcf (midx, msg) eq_refl
                         ltac:(simpl; rewrite Hmt; reflexivity)
                                Hinm); dest; auto
      end.

  Ltac solve_NoRsI_by_rqUp oidx :=
    repeat
      match goal with
      | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
                Hin: In oidx (c_li_indices _ ++ c_l1_indices _),
                     Horq: ?orqs@[oidx] = Some _ |- _] =>
        specialize (Hmcfi oidx _ Hin Horq);
        simpl in Hmcfi; destruct Hmcfi
      | [Hmcf: RsDownConflicts oidx _ ?msgs,
               Hinm: InMPI ?msgs (?rsd, ?msg),
                     Hmt: msg_type ?msg = MRs,
                          Hfmp: FirstMPI ?msgs (?rqu, ?rmsg) |- _] =>
        specialize (Hmcf (rsd, msg) eq_refl
                         ltac:(simpl; rewrite Hmt; reflexivity)
                                Hinm);
        let Hrqu := fresh "H" in
        destruct Hmcf as [_ [Hrqu _]];
        apply Hrqu with (rqUp:= (rqu, rmsg)); auto
      | |- InMPI _ _ => red; solve_in_mp
      end.

  Ltac solve_NoRsI_by_rqDown oidx :=
    repeat
      match goal with
      | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
                Hin: In oidx (c_l1_indices _),
                     Horq: ?orqs@[oidx] = Some _ |- _] =>
        specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_intror Hin)) Horq);
        simpl in Hmcfi; destruct Hmcfi
      | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
                Hin: In oidx (tl (c_li_indices _)),
                     Horq: ?orqs@[oidx] = Some _ |- _] =>
        specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_introl (tl_In _ _ Hin))) Horq);
        simpl in Hmcfi; destruct Hmcfi
      | [Hmcf: RsDownConflicts oidx _ ?msgs,
               Hinm: InMPI ?msgs (?midx, ?msg),
                     Hmt: msg_type ?msg = MRs |- _] =>
        specialize (Hmcf (midx, msg) eq_refl
                         ltac:(simpl; rewrite Hmt; reflexivity)
                                Hinm);
        let Hrqd := fresh "H" in
        destruct Hmcf as [_ [_ [_ [Hrqd _]]]];
        eapply Hrqd; try eassumption; try reflexivity; assumption
      end.

  Ltac solve_NoRsI_by_rsDown oidx :=
    repeat
      match goal with
      | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
                Hin: In oidx (c_l1_indices _),
                     Horq: ?orqs@[oidx] = Some _ |- _] =>
        specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_intror Hin)) Horq);
        simpl in Hmcfi; destruct Hmcfi
      | [Hmcf: RsDownConflicts oidx _ ?msgs,
               Hinm: InMPI ?msgs (?midx, ?msg),
                     Hmt: msg_type ?msg = MRs,
                          Hfmp: FirstMPI ?msgs (?midx, ?rmsg) |- _] =>
        specialize (Hmcf (midx, msg) eq_refl
                         ltac:(simpl; rewrite Hmt; reflexivity)
                                Hinm);
        let Hrqd := fresh "H" in
        destruct Hmcf as [_ [_ [Hrqd _]]];
        eapply Hrqd with (rrsDown:= (midx, rmsg));
        try eassumption; try reflexivity
      | |- valOf (_, ?msg1) <> valOf (_, ?msg2) =>
        let Hx := fresh "H" in
        destruct msg1, msg2; simpl in *; intro Hx; inv Hx; discriminate
      | |- InMPI _ _ => red; solve_in_mp
      end.

  Ltac solve_NoRqI_base :=
    repeat
      match goal with
      | |- NoRqI _ _ => do 3 red; intros
      | |- MsgP _ _ =>
        red; unfold cohMsgs, map, caseDec, fst;
        repeat (find_if_inside; [simpl|auto])
      | [H: sigOf ?idm = _ |- _] =>
        let midx := fresh "midx" in
        let msg := fresh "msg" in
        destruct idm as [midx msg]; inv H
      end.

  Ltac solve_NoRqI_by_no_locks oidx :=
    repeat
      match goal with
      | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
                Hin: In oidx (c_l1_indices _),
                     Horq: ?orqs@[oidx] = Some _ |- _] =>
        specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_intror Hin)) Horq);
        simpl in Hmcfi; destruct Hmcfi
      | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
                Hin: In oidx (tl (c_li_indices _)),
                     Horq: ?orqs@[oidx] = Some _ |- _] =>
        specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_introl (tl_In _ _ Hin))) Horq);
        simpl in Hmcfi; destruct Hmcfi
      | [Hmcf: RqUpConflicts oidx _ ?msgs, Hinm: InMPI ?msgs (?midx, ?msg) |- _] =>
        specialize (Hmcf (midx, msg) eq_refl Hinm); dest; auto
      end.

  Ltac solve_NoRqI_by_rsDown oidx :=
    repeat
      match goal with
      | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
                Hin: In oidx (c_l1_indices _),
                     Horq: ?orqs@[oidx] = Some _ |- _] =>
        specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_intror Hin)) Horq);
        simpl in Hmcfi; destruct Hmcfi
      | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
                Hin: In oidx (tl (c_li_indices _)),
                     Horq: ?orqs@[oidx] = Some _ |- _] =>
        specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_introl (tl_In _ _ Hin))) Horq);
        simpl in Hmcfi; destruct Hmcfi
      | [Hmcf: RsDownConflicts oidx _ ?msgs,
               Hfmp: FirstMPI ?msgs (?down, ?msg),
                     Hmt: msg_type ?msg = MRs,
                          Hinm: InMPI ?msgs (?rqu, ?rmsg) |- _] =>
        apply FirstMP_InMP in Hfmp;
        specialize (Hmcf (down, msg) eq_refl
                         ltac:(simpl; rewrite Hmt; reflexivity)
                                Hfmp);
        let Hrqu := fresh "H" in
        destruct Hmcf as [_ [Hrqu _]];
        eapply Hrqu with (rqUp:= (rqu, rmsg));
        try eassumption; try reflexivity
      end.

  Ltac derive_footprint_info_basis oidx :=
    progress (good_footprint_get oidx);
    repeat (repeat disc_rule_conds_unit_simpl; try disc_footprints_ok).

  Ltac derive_child_chns :=
    match goal with
    | [Htn: TreeTopoNode _, H: parentIdxOf _ ?cidx = Some ?oidx
       |- context[SimMESI {| bst_oss := _ +[?oidx <- _] |} _] ] =>
      pose proof (Htn _ _ H); dest
    end;
    (* For L1 caches derive some more information about "the" child. *)
    try match goal with
        | [H1: In ?oidx (c_l1_indices _), H2: parentIdxOf _ _ = Some ?oidx |- _] =>
          apply tree2Topo_l1_child_ext in H2; [|assumption]; subst
        end.

  Ltac derive_child_idx_in cidx :=
    let idx := fresh "idx" in
    remember cidx as idx;
    try
      match goal with
      | [H: In idx (subtreeChildrenIndsOf _ _) |- _] =>
        apply subtreeChildrenIndsOf_parentIdxOf in H; [|auto; fail]
      end;
    match goal with
    | [Hin: In ?oidx (c_li_indices _), Hp: parentIdxOf _ idx = Some ?oidx
       |- context[SimMESI {| bst_oss := _ +[?oidx <- _] |} _] ] =>
      pose proof (tree2Topo_li_child_li_l1 _ _ _ Hin Hp)
    | [Hin: In ?oidx (tl (c_li_indices _)), Hp: parentIdxOf _ idx = Some ?oidx
       |- context[SimMESI {| bst_oss := _ +[?oidx <- _] |} _] ] =>
      pose proof (tree2Topo_li_child_li_l1 _ _ _ (tl_In _ _ Hin) Hp)
    end; subst.

  Ltac derive_input_msg_coherent :=
    match goal with
    | [Hcoh: MsgsCoh ?cv _ _, Hfmp: FirstMPI _ (_, ?cmsg) |- _] =>
      let Ha := fresh "H" in
      assert (msg_value cmsg = cv)
        as Ha by (disc_MsgsCoh_by_FirstMP Hcoh Hfmp; assumption);
      rewrite Ha in *
    end.

  Ltac derive_obj_coherent oidx :=
    match goal with
    | [Hcoh: _ -> _ -> fst ?ost = ?cv, Host: ?oss@[oidx] = Some ?ost |- _] =>
      let Ha := fresh "H" in
      assert (fst ost = cv) as Ha by (apply Hcoh; auto; solve_mesi);
      rewrite Ha in *
    end.

  Ltac derive_coherence_of oidx :=
    match goal with
    | [Hf: forall _, In _ ?l -> _, He: In oidx ?l |- _] =>
      pose proof (Hf _ He); disc_rule_conds_ex
    end.

  Ltac disc_getDir :=
    try match goal with
        | [H: getDir _ _ = _ |- _] =>
          first [apply getDir_M_imp in H; destruct H
                |apply getDir_E_imp in H; destruct H
                |apply getDir_S_imp in H; destruct H]
        | [H: mesiE <= getDir _ _ |- _] =>
          apply getDir_ME_imp in H; destruct H
        end.

  Ltac derive_ObjDirE oidx cidx :=
    match goal with
    | [Host: ?oss@[oidx] = Some ?ost,
             Horq: ?orqs@[oidx] = Some ?orq |- _] =>
      assert (ObjDirE orq ost cidx) by (repeat split; assumption)
    end.

  Ltac derive_ObjDirME oidx cidx :=
    match goal with
    | [Host: ?oss@[oidx] = Some ?ost,
             Horq: ?orqs@[oidx] = Some ?orq |- _] =>
      assert (ObjDirME orq ost cidx) by (repeat split; assumption)
    end.

  Ltac derive_ObjInvRq oidx :=
    match goal with
    | [H: FirstMPI ?msgs (rqUpFrom oidx, ?rmsg) |- _] =>
      assert (ObjInvRq oidx msgs)
        by (exists (rqUpFrom oidx, rmsg); split;
                   [red; simpl; solve_in_mp|unfold sigOf; simpl; congruence])
    end.

  Ltac derive_ObjRqWB_inv oidx :=
    match goal with
    | [H: FirstMPI ?msgs (rqUpFrom oidx, ?rmsg) |- _] =>
      assert (ObjRqWB oidx msgs)
        by (left; eexists; split;
            [eapply FirstMP_InMP; eassumption
            |unfold sigOf; simpl; congruence])
    end.

  Ltac derive_ObjRqWB_push oidx :=
    match goal with
    | [H: FirstMPI ?msgs (rqUpFrom oidx, ?rmsg) |- _] =>
      assert (ObjRqWB oidx msgs)
        by (right; eexists; split;
            [eapply FirstMP_InMP; eassumption
            |unfold sigOf; simpl; congruence])
    end.

  Ltac disc_InvNonWB cidx Hinv :=
    repeat
      match goal with
      | [Hp: parentIdxOf _ cidx = Some _ |- _] =>
        specialize (Hinv _ _ Hp); simpl in Hinv;
        disc_rule_conds_ex
      end.

  Ltac disc_InvWBChild cidx Hinv :=
    match goal with
    | [Hp: parentIdxOf _ cidx = Some _ |- _] =>
      specialize (Hinv _ _ Hp); simpl in Hinv;
      disc_rule_conds_ex
    end.

  Ltac disc_InvWB_inv cidx Hinv :=
    specialize (Hinv cidx); simpl in Hinv;
    disc_rule_conds_ex;
    match goal with
    | [Hcoh: CohInvRq cidx ?ost _, Ho: ObjOwned ?ost, Hfm: FirstMPI _ _ |- _] =>
      specialize (Hcoh Ho _ (FirstMP_InMP Hfm));
      unfold sigOf in Hcoh; simpl in Hcoh;
      specialize (Hcoh ltac:(congruence))
    end.

  Ltac disc_InvWB_push cidx Hinv :=
    specialize (Hinv cidx); simpl in Hinv;
    disc_rule_conds_ex;
    match goal with
    | [Hcoh: CohPushRq cidx ?ost _, Ho: ObjOwned ?ost, Hfm: FirstMPI _ _ |- _] =>
      specialize (Hcoh Ho _ (FirstMP_InMP Hfm));
      unfold sigOf in Hcoh; simpl in Hcoh;
      specialize (Hcoh ltac:(congruence))
    end.

  Ltac disc_responses_from :=
    repeat
      match goal with
      | [Hrr: RqRsDownMatch _ _ _ ?rss _, Hrss: _ = ?rss |- _] =>
        rewrite <-Hrss in Hrr
      end;
    repeat
      match goal with
      | [H: ValidMsgsIn _ ?rss |- _] => destruct H
      | [Hrr: RqRsDownMatch _ _ _ [_] _ |- _] =>
        let cidx := fresh "cidx" in
        let down := fresh "down" in
        eapply RqRsDownMatch_rs_rq in Hrr; [|left; reflexivity];
        destruct Hrr as [cidx [down ?]]; dest
      | [Hrr: RqRsDownMatch _ ?oidx _ (idsOf ?rss) _,
         Hin: In ?oidx (tl (c_li_indices _)) |- _] =>
        let Hc := fresh "H" in
        pose proof (tree2Topo_li_RqRsDownMatch_children _ _ (tl_In _ _ Hin) _ Hrr) as Hc;
        let Hic := fresh "H" in
        destruct Hc as [cinds [Hic ?]]; rewrite Hic
      | [Hrr: RqRsDownMatch _ ?oidx _ (idsOf ?rss) _,
         Hin: In ?oidx (c_li_indices _) |- _] =>
        let Hc := fresh "H" in
        pose proof (tree2Topo_li_RqRsDownMatch_children _ _ Hin _ Hrr) as Hc;
        let Hic := fresh "H" in
        destruct Hc as [cinds [Hic ?]]; rewrite Hic
      end.

  Ltac exfalso_downlock_from oidx Hinv :=
    specialize (Hinv oidx); simpl in Hinv;
    disc_rule_conds_ex;
    repeat
      match goal with
      | [Hrqi: rqi_msg _ = Some ?msg, Hmsg: msg_id ?msg = _ |- _] =>
        rewrite Hmsg in Hinv; simpl in Hinv
      | [Hdfc: DownLockFromChild _ _ _ |- _] =>
        red in Hdfc; dest; disc_rule_conds_ex
      | [Hdfp: DownLockFromParent _ _ |- _] =>
        red in Hdfp; dest; disc_rule_conds_ex; solve_midx_false
      end.

  Theorem mesi_sim_ok:
    InvSim step_m step_m (MesiInv.InvForSim topo) SimMESI impl spec.
  Proof.
    red; intros.

    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
    pose proof (upLockInv_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr)
                  (mesi_RqRsDTree Htr) H) as Hpulinv.
    pose proof (upLockInv_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr)
                  (mesi_RqRsDTree Htr)
                  (reachable_steps H (steps_singleton H2))) as Hnulinv.
    pose proof (mesi_RsDownConflicts H) as Hpmcf.
    pose proof (mesi_RsDownConflicts
                  (reachable_steps H (steps_singleton H2))) as Hnmcf.

    inv H2;
      [apply mesi_sim_silent; assumption
      |apply sim_mesi_ext_in; assumption
      |apply sim_mesi_ext_out; assumption
      |].

    destruct sst1 as [soss1 sorqs1 smsgs1].
    destruct H0; simpl in H0, H2; simpl.
    inv H0.
    red in H15; simpl in H15.
    red in H6; simpl in H6.
    destruct (soss1@[specIdx]) as [sost|] eqn:Hsost; simpl in *; [|exfalso; auto].
    destruct (sorqs1@[specIdx]) as [sorq|] eqn:Hsorq; simpl in *; [|exfalso; auto].
    subst.
    simpl in H4; destruct H4; [subst|apply in_app_or in H0; destruct H0].

    - (*! Cases for the main memory *)
      Ltac solve_ImplStateCoh_mem_me :=
        disc_rule_conds_ex;
        split; [solve_ImplOStateMESI|solve_MsgsCoh].

      Ltac solve_ImplStateCoh_mem_others lidx :=
        match goal with
        | [Hf: forall _, In _ ?l -> _, He: In lidx ?l |- _] =>
          specialize (Hf _ He); disc_rule_conds_ex
        end;
        split; [solve_ImplOStateMESI|solve_MsgsCoh].

      Ltac case_ImplStateCoh_mem_me_others lidx :=
        match goal with
        | |- ImplStateCoh _ {| bst_oss := _ +[?oidx <- _] |} =>
          red; simpl;
          apply Forall_forall;
          intros lidx ?; destruct (idx_dec lidx oidx); subst
        end.

      Ltac solve_ImplStateCoh ::=
        let lidx := fresh "lidx" in
        case_ImplStateCoh_mem_me_others lidx;
        [solve_ImplStateCoh_mem_me|solve_ImplStateCoh_mem_others lidx].

      (** Derive some properties of the root *)
      pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
      
      assert (In (rootOf (fst (tree2Topo tr 0))) (c_li_indices (snd (tree2Topo tr 0)))).
      { rewrite c_li_indices_head_rootOf by assumption.
        left; reflexivity.
      }

      assert (~ In (rootOf (fst (tree2Topo tr 0))) (c_l1_indices (snd (tree2Topo tr 0)))).
      { pose proof (tree2Topo_WfCIfc tr 0) as [? _].
        apply (DisjList_NoDup idx_dec) in H4.
        eapply DisjList_In_2; eassumption.
      }

      disc_rule_conds_ex.
      destruct H1 as [Hnrsi Hnrqi].
      unfold topo in Hnrsi, Hnrqi; simpl in Hnrsi, Hnrqi.

      assert (rsEdgeUpFrom topo (rootOf (fst (tree2Topo tr 0))) = None).
      { destruct (rsEdgeUpFrom _ _) eqn:Hrs; [|reflexivity].
        exfalso.
        apply rsEdgeUpFrom_Some with (sys:= impl) in Hrs;
          [|subst topo impl; auto].
        destruct Hrs as [rqUp [down [pidx ?]]]; dest.
        apply parentIdxOf_child_not_root in H28; [|subst topo; auto].
        auto.
      }

      (** Abstract the root. *)
      remember (rootOf (fst (tree2Topo tr 0))) as oidx; clear Heqoidx.
      disc_rule_conds_ex.

      (** Do case analysis per a rule. *)
      apply in_app_or in H5; destruct H5.

      1: { (** Rules per a child *)
        apply concat_In in H5; destruct H5 as [crls [? ?]].
        apply in_map_iff in H5; destruct H5 as [cidx [? ?]]; subst.

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        dest_in.

        { (* [liGetSImmS] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          derive_obj_coherent oidx.
          solve_sim_mesi.
          destruct (idx_dec lidx cidx); subst; solve_MsgsCoh.
        }

        { (* [liGetSImmME] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          derive_obj_coherent oidx.
          solve_sim_mesi.
          destruct (idx_dec lidx cidx); subst; solve_MsgsCoh.
        }
        
        { (* [liGetSRqUpDownME] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          derive_child_idx_in (dir_excl (fst (snd (snd (snd pos))))).
          solve_sim_mesi.
        }

        { (* [liGetMImm] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liGetMRqUpDownME] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          derive_child_idx_in (dir_excl (fst (snd (snd (snd pos))))).
          solve_sim_mesi.
        }

        { (* [liGetMRqUpDownS] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmI] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmS0] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmS1] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmE] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.

          solve_sim_mesi_ext_mp.
          solve_SpecStateCoh.
          case_ImplStateCoh_mem_me_others lidx.
          { disc_rule_conds_ex; split.
            { (* Coherence of the object *)
              intros.
              derive_coherence_of cidx.
              disc_getDir.
              derive_ObjDirE oidx cidx.
              derive_ObjInvRq cidx.
              assert (NoRsI cidx msgs)
                by (clear H39; solve_NoRsI_base; solve_NoRsI_by_rqUp cidx).
              disc_InvNonWB cidx H23.
              (* discharge [ImplOStateMESI] of [cidx] *)
              red in H23; dest.
              specialize (H37 H23 H42).
              congruence.
            }
            { solve_MsgsCoh. }
          }
          { solve_ImplStateCoh_mem_others lidx. }
        }

        { (* [liInvImmWBI] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmWBS0] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmWBS1] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmWBME] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.

          solve_sim_mesi_ext_mp.
          solve_SpecStateCoh.
          case_ImplStateCoh_mem_me_others lidx.
          { disc_rule_conds_ex; split.
            { (* Coherence of the object *)
              intros.
              derive_coherence_of cidx.
              disc_getDir.
              derive_ObjDirME oidx cidx.
              derive_ObjRqWB_inv cidx.
              clear H39.
              assert (NoRsI cidx msgs)
                by (solve_NoRsI_base; solve_NoRsI_by_rqUp cidx).
              disc_InvWBChild cidx H22.
              disc_InvWB_inv cidx H21.
              (* discharge [ImplOStateMESI] of [cidx] *)
              red in H22; dest.
              specialize (H37 H22 H39).
              congruence.
            }
            { solve_MsgsCoh. }
          }
          { solve_ImplStateCoh_mem_others lidx. }
        }

        { (* [liPushImm] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liPushImmWB0] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }
        
        { (* [liPushImmWB1] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.

          solve_sim_mesi_ext_mp.
          solve_SpecStateCoh.
          case_ImplStateCoh_mem_me_others lidx.
          { disc_rule_conds_ex; split.
            { (* Coherence of the object *)
              intros.
              derive_coherence_of cidx.
              disc_getDir.
              derive_ObjDirME oidx cidx.
              derive_ObjRqWB_push cidx.
              clear H39.
              assert (NoRsI cidx msgs)
                by (solve_NoRsI_base; solve_NoRsI_by_rqUp cidx).
              disc_InvWBChild cidx H22.
              disc_InvWB_push cidx H21.
              (* discharge [ImplOStateMESI] of [cidx] *)
              red in H22; dest.
              specialize (H37 H22 H39).
              congruence.
            }
            { solve_MsgsCoh. }
          }
          { solve_ImplStateCoh_mem_others lidx. }
        }
        
      }

      dest_in.

      { (* [liDownSRsUpDownME] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx;
          [|exfalso; subst topo; congruence].
        derive_child_chns.
        derive_child_idx_in upCIdx.
        disc_responses_from.
        derive_child_chns.
        derive_child_idx_in cidx.
        derive_coherence_of cidx.
        derive_input_msg_coherent.
        solve_sim_mesi.
        destruct (idx_dec lidx (obj_idx upCObj)); subst; solve_MsgsCoh.
      }

      { (* [liDownIRsUpDown] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx;
          [|exfalso; subst topo; congruence].
        derive_child_chns.
        derive_child_idx_in upCIdx.
        disc_responses_from.
        disc_rule_conds_ex.
        solve_sim_mesi.
      }

    - (*! Cases for Li caches *)
      Ltac solve_ImplStateCoh_li_me :=
        disc_rule_conds_ex;
        split; [solve_ImplOStateMESI|solve_MsgsCoh].

      Ltac solve_ImplStateCoh_li_others lidx :=
        match goal with
        | [Hf: forall _, In _ ?l -> _, He: In lidx ?l |- _] =>
          specialize (Hf _ He); disc_rule_conds_ex
        end;
        split; [solve_ImplOStateMESI|solve_MsgsCoh].

      Ltac case_ImplStateCoh_li_me_others lidx :=
        match goal with
        | |- ImplStateCoh _ {| bst_oss := _ +[?oidx <- _] |} =>
          red; simpl;
          apply Forall_forall;
          intros lidx ?; destruct (idx_dec lidx oidx); subst
        end.

      Ltac solve_ImplStateCoh ::=
        let lidx := fresh "lidx" in
        case_ImplStateCoh_li_me_others lidx;
        [solve_ImplStateCoh_li_me|solve_ImplStateCoh_li_others lidx].

      apply in_map_iff in H0; destruct H0 as [oidx [? ?]]; subst; simpl in *.

      (** Derive some necessary information: 1) each Li has a parent. *)
      pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
      pose proof (c_li_indices_tail_has_parent _ _ _ H4).
      destruct H0 as [pidx [? ?]].
      pose proof (Htn _ _ H6); dest.

      (** 2) The object index does not belong to [c_l1_indices]. *)
      assert (~ In oidx (c_l1_indices (snd (tree2Topo tr 0)))).
      { pose proof (tree2Topo_WfCIfc tr 0) as [? _].
        apply (DisjList_NoDup idx_dec) in H19.
        eapply DisjList_In_2; [eassumption|].
        apply tl_In; assumption.
      }

      disc_rule_conds_ex.
      (** Do case analysis per a rule. *)
      apply in_app_or in H5; destruct H5.

      1: { (** Rules per a child *)
        apply concat_In in H5; destruct H5 as [crls [? ?]].
        apply in_map_iff in H5; destruct H5 as [cidx [? ?]]; subst.

        (** 3) The child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        dest_in.

        { (* [liGetSImmS] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          assert (NoRsI oidx msgs)
            by (solve_NoRsI_base; solve_NoRsI_by_no_locks oidx).
          derive_obj_coherent oidx.
          solve_sim_mesi.
          destruct (idx_dec lidx cidx); subst; solve_MsgsCoh.
        }
        
        { (* [liGetSImmME] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          assert (NoRsI oidx msgs)
            by (solve_NoRsI_base; solve_NoRsI_by_no_locks oidx).
          derive_obj_coherent oidx.
          solve_sim_mesi.
          destruct (idx_dec lidx cidx); subst; solve_MsgsCoh.
        }
        
        { (* [liGetSRqUpUp] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liGetSRqUpDownME] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          derive_child_idx_in (dir_excl (fst (snd (snd (snd pos))))).
          solve_sim_mesi.
        }

        { (* [liGetSRqUpDownS] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          derive_child_idx_in (hd ii (dir_sharers (fst (snd (snd (snd pos)))))).
          solve_sim_mesi.
        }

        { (* [liGetMImm] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liGetMRqUpUp] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liGetMRqUpDownME] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          derive_child_idx_in (dir_excl (fst (snd (snd (snd pos))))).
          solve_sim_mesi.
        }

        { (* [liGetMRqUpDownS] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmI] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmS0] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmS1] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmE] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          assert (NoRqI oidx msgs)
            by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx).

          solve_sim_mesi_ext_mp.
          solve_SpecStateCoh.
          case_ImplStateCoh_li_me_others lidx.
          { disc_rule_conds_ex; split.
            { (* Coherence of the object *)
              intros.
              derive_coherence_of cidx.
              disc_getDir.
              derive_ObjDirE oidx cidx.
              derive_ObjInvRq cidx.
              assert (NoRsI cidx msgs)
                by (clear H45; solve_NoRsI_base; solve_NoRsI_by_rqUp cidx).
              disc_InvNonWB cidx H28.
              (* discharge [ImplOStateMESI] of [cidx] *)
              red in H28; dest.
              specialize (H43 H28 H48).
              congruence.
            }
            { solve_MsgsCoh. }
          }
          { solve_ImplStateCoh_li_others lidx. }
        }

        { (* [liInvImmWBI] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmWBS0] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmWBS1] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liInvImmWBME] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          assert (NoRqI oidx msgs)
            by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx).

          solve_sim_mesi_ext_mp.
          solve_SpecStateCoh.
          case_ImplStateCoh_li_me_others lidx.
          { disc_rule_conds_ex; split.
            { (* Coherence of the object *)
              intros.
              derive_coherence_of cidx.
              disc_getDir.
              derive_ObjDirME oidx cidx.
              derive_ObjRqWB_inv cidx.
              clear H45.
              assert (NoRsI cidx msgs)
                by (solve_NoRsI_base; solve_NoRsI_by_rqUp cidx).
              disc_InvWBChild cidx H27.
              disc_InvWB_inv cidx H26.
              (* discharge [ImplOStateMESI] of [cidx] *)
              red in H27; dest.
              specialize (H43 H27 H45).
              congruence.
            }
            { solve_MsgsCoh. }
          }
          { solve_ImplStateCoh_li_others lidx. }
        }

        { (* [liPushImm] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }

        { (* [liPushImmWB0] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          solve_sim_mesi.
        }
        
        { (* [liPushImmWB1] *)
          disc_rule_conds_ex; spec_case_silent.
          derive_child_chns.
          derive_child_idx_in cidx.
          assert (NoRqI oidx msgs)
            by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx).

          solve_sim_mesi_ext_mp.
          solve_SpecStateCoh.
          case_ImplStateCoh_li_me_others lidx.
          { disc_rule_conds_ex; split.
            { (* Coherence of the object *)
              intros.
              derive_coherence_of cidx.
              disc_getDir.
              derive_ObjDirME oidx cidx.
              derive_ObjRqWB_push cidx.
              clear H45.
              assert (NoRsI cidx msgs)
                by (solve_NoRsI_base; solve_NoRsI_by_rqUp cidx).
              disc_InvWBChild cidx H27.
              disc_InvWB_push cidx H26.
              (* discharge [ImplOStateMESI] of [cidx] *)
              red in H27; dest.
              specialize (H43 H27 H45).
              congruence.
            }
            { solve_MsgsCoh. }
          }
          { solve_ImplStateCoh_li_others lidx. }
        }
        
      }

      dest_in.

      { (* [liGetSRsDownDownS] *)
        disc_rule_conds_ex; spec_case_silent.

        derive_footprint_info_basis oidx.
        derive_child_chns.
        derive_child_idx_in cidx.
        derive_input_msg_coherent.
        disc_rule_conds_ex.
        assert (NoRqI oidx msgs)
          by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx).

        solve_sim_mesi.
        destruct (idx_dec lidx cidx); subst; solve_MsgsCoh.
      }

      { (* [liGetSRsDownDownE] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx.
        derive_child_chns.
        derive_child_idx_in cidx.
        derive_input_msg_coherent.
        disc_rule_conds_ex.
        assert (NoRqI oidx msgs)
          by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx).

        solve_sim_mesi.
        destruct (idx_dec lidx cidx); subst; solve_MsgsCoh.
      }

      { (* [liDownSRsUpDownME] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx;
          [|exfalso_downlock_from oidx H29].
        derive_child_chns.
        derive_child_idx_in upCIdx.
        disc_responses_from.
        derive_child_chns.
        derive_child_idx_in cidx.
        derive_coherence_of cidx.
        derive_input_msg_coherent.

        solve_sim_mesi.
        destruct (idx_dec lidx (obj_idx upCObj)); subst; solve_MsgsCoh.
      }

      { (* liDownSRsUpDownS] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx;
          [|exfalso_downlock_from oidx H29].
        derive_child_chns.
        derive_child_idx_in upCIdx.
        disc_responses_from.
        derive_child_chns.
        derive_child_idx_in cidx.
        derive_coherence_of cidx.
        derive_input_msg_coherent.

        solve_sim_mesi.
        destruct (idx_dec lidx (obj_idx upCObj)); subst; solve_MsgsCoh.
      }

      { (* [liDownSImm] *)
        disc_rule_conds_ex.
        spec_case_silent.
        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_rqDown oidx).
        disc_rule_conds_ex.
        solve_sim_mesi.
      }

      { (* [liDownSRqDownDownME] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_child_idx_in (dir_excl (fst (snd (snd (snd pos))))).
        solve_sim_mesi.
      }

      { (* [liDownSRqDownDownS] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_child_idx_in (hd ii (dir_sharers (fst (snd (snd (snd pos)))))).
        solve_sim_mesi.
      }

      { (* [liDownSRsUpUp] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx;
          [exfalso_downlock_from oidx H29|].
        disc_responses_from.
        derive_child_chns.
        derive_child_idx_in cidx.
        derive_coherence_of cidx.
        derive_input_msg_coherent.
        solve_sim_mesi.
      }

      { (* [liGetMRsDownDownDirI] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx.
        derive_child_chns.
        derive_child_idx_in cidx.
        disc_rule_conds_ex.
        assert (NoRqI oidx msgs)
          by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx).
        solve_sim_mesi.
      }

      { (* [liGetMRsDownRqDownDirS] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx.
        solve_sim_mesi.
      }

      { (* [liDownIRsUpDown] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx;
          [|exfalso_downlock_from oidx H29].
        derive_child_chns.
        derive_child_idx_in upCIdx.
        disc_responses_from.
        disc_rule_conds_ex.
        solve_sim_mesi.
      }

      { (* [liDownIImm] *)
        disc_rule_conds_ex.
        spec_case_silent.
        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_rqDown oidx).
        disc_rule_conds_ex.
        solve_sim_mesi.
      }

      { (* [liDownIRqDownDownDirS] *)
        disc_rule_conds_ex; spec_case_silent.
        solve_sim_mesi.
      }

      { (* [liDownIRqDownDownDirME] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_child_idx_in (dir_excl (fst (snd (snd (snd pos))))).
        solve_sim_mesi.
      }

      { (* [liDownIRsUpUp] *)
        disc_rule_conds_ex; spec_case_silent.
        derive_footprint_info_basis oidx;
          [exfalso_downlock_from oidx H29|].
        disc_responses_from.
        solve_sim_mesi.
      }

      { (* [liInvRqUpUp] *)
        disc_rule_conds_ex; spec_case_silent.
        solve_sim_mesi.
      }

      { (* [liInvRqUpUpWB] *)
        disc_rule_conds_ex; spec_case_silent.
        solve_sim_mesi.
      }

      { (* [liInvRsDownDown] *)
        disc_rule_conds_ex.
        spec_case_silent.
        derive_footprint_info_basis oidx.
        disc_rule_conds_ex.
        solve_sim_mesi.
      }

      { (* [liPushRqUpUp] *)
        disc_rule_conds_ex; spec_case_silent.
        solve_sim_mesi.
      }

      { (* [liPushRqUpUpWB] *)
        disc_rule_conds_ex; spec_case_silent.
        solve_sim_mesi.
      }

    - (*! Cases for L1 caches *)
      apply in_map_iff in H0; destruct H0 as [oidx [? ?]]; subst.

      Ltac solve_ImplStateCoh_l1_me :=
        disc_rule_conds_ex;
        split; [solve_ImplOStateMESI|solve_MsgsCoh].

      Ltac solve_ImplStateCoh_l1_others :=
        try match goal with
            | [H: MsgsCoh _ ?oidx _, Hin: In ?oidx _ |- _] => clear Hin
            end;
        match goal with
        | [Hf: forall _, In _ ?l -> _, He: In _ ?l |- _] =>
          specialize (Hf _ He); disc_rule_conds_ex
        end;
        split; [solve_ImplOStateMESI|solve_MsgsCoh].

      Ltac case_ImplStateCoh_l1_me_others :=
        red; simpl;
        match goal with
        | [H: MsgsCoh _ ?oidx _ |- Forall _ _] =>
          let lidx := fresh "lidx" in
          apply Forall_forall;
          intros lidx ?; destruct (idx_dec lidx oidx); subst
        end.
          
      Ltac solve_ImplStateCoh ::=
        case_ImplStateCoh_l1_me_others;
        [solve_ImplStateCoh_l1_me|solve_ImplStateCoh_l1_others].

      (** Derive some necessary information: each L1 has a parent. *)
      pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
      pose proof (c_l1_indices_has_parent Htr _ _ H4).
      destruct H0 as [pidx [? ?]].
      pose proof (Htn _ _ H6); dest.

      Opaque In.
      disc_rule_conds_ex.
      Transparent In.
      (** Do case analysis per a rule. *)
      dest_in.

      + (* [l1GetSImm] *)
        disc_rule_conds_ex.
        spec_case_get oidx.        
        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_no_locks oidx).
        disc_rule_conds_ex.
        solve_sim_mesi.

      + (* [l1GetSRqUpUp] *)
        disc_rule_conds_ex.
        spec_case_silent.
        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_no_locks oidx).
        disc_rule_conds_ex.
        solve_sim_mesi.

      + (* [l1GetSRsDownDownS] *)
        disc_rule_conds_ex.
        spec_case_get oidx.

        derive_footprint_info_basis oidx.
        derive_child_chns.
        derive_input_msg_coherent.
        disc_rule_conds_ex.
        assert (NoRqI oidx msgs)
          by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx).

        solve_sim_mesi.

      + (* [l1GetSRsDownDownE] *)
        disc_rule_conds_ex.
        spec_case_get oidx.

        derive_footprint_info_basis oidx.
        derive_child_chns.
        derive_input_msg_coherent.
        disc_rule_conds_ex.
        assert (NoRqI oidx msgs)
          by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx).

        solve_sim_mesi.

      + (* [l1DownSImm] *)
        disc_rule_conds_ex.
        spec_case_silent.
        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_rqDown oidx).
        disc_rule_conds_ex.
        solve_sim_mesi.

      + (* [l1GetMImmE] *)
        disc_rule_conds_ex.
        spec_case_set oidx.
        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_no_locks oidx).
        disc_rule_conds_ex.

        solve_sim_mesi_ext_mp.
        solve_SpecStateCoh.
        case_ImplStateCoh_l1_me_others.
        * mred; simpl.
          eapply ObjExcl0_ObjCoh.
          { specialize (H19 oidx); repeat (simpl in H19; mred); dest.
            assumption.
          }
          { split.
            { simpl; solve_mesi. }
            { do 2 red; simpl.
              apply MsgsP_other_midx_enqMP;
                [|intro; dest_in;
                  inv H31; eapply l1ExtOf_not_eq; eauto].
              apply MsgsP_deqMP.
              assumption.
            }
          }

        * clear H4. (* In oidx .. *)
          mred; simpl.
          assert (exists lost lorq, oss@[lidx] = Some lost /\
                                    orqs@[lidx] = Some lorq).
          { specialize (H15 _ H11).
            solve_rule_conds_ex.
          }
          destruct H4 as [lost [lorq [? ?]]]; rewrite H4, H12; simpl.
          eapply ObjInvalid_ObjCoh.
          { apply Hnmcf; [|simpl; mred].
            assumption.
          }
          { eapply InvExcl_excl_invalid; [eapply H19|..];
              try eassumption; try reflexivity; try (simpl; mred); try solve_mesi.
            do 2 red.
            apply MsgsP_other_midx_enqMP;
              [|intro; dest_in;
                inv H37; eapply l1ExtOf_not_eq; eauto].
            apply MsgsP_deqMP.
            assumption.
          }
          
      + (* [l1GetMImmM] *)
        disc_rule_conds_ex.
        spec_case_set oidx.
        assert (NoRsI oidx msgs) 
          by (solve_NoRsI_base; solve_NoRsI_by_no_locks oidx).
        disc_rule_conds_ex.
        
        solve_sim_mesi_ext_mp.
        solve_SpecStateCoh.
        case_ImplStateCoh_l1_me_others.
        * mred; simpl.
          eapply ObjExcl0_ObjCoh.
          { specialize (H19 oidx); repeat (simpl in H19; mred); dest.
            assumption.
          }
          { split.
            { simpl; solve_mesi. }
            { do 2 red; simpl.
              apply MsgsP_other_midx_enqMP;
                [|intro; dest_in;
                  inv H31; eapply l1ExtOf_not_eq; eauto].
              apply MsgsP_deqMP.
              assumption.
            }
          }

        * clear H4. (* In oidx .. *)
          mred; simpl.
          assert (exists lost lorq, oss@[lidx] = Some lost /\
                                    orqs@[lidx] = Some lorq).
          { specialize (H15 _ H11).
            solve_rule_conds_ex.
          }
          destruct H4 as [lost [lorq [? ?]]]; rewrite H4, H12; simpl.
          eapply ObjInvalid_ObjCoh.
          { apply Hnmcf; [|simpl; mred].
            assumption.
          }
          { eapply InvExcl_excl_invalid; [eapply H19|..];
              try eassumption; try reflexivity; try (simpl; mred); try solve_mesi.
            do 2 red.
            apply MsgsP_other_midx_enqMP;
              [|intro; dest_in;
                inv H37; eapply l1ExtOf_not_eq; eauto].
            apply MsgsP_deqMP.
            assumption.
          }

      + (* [l1GetMRqUpUp] *)
        disc_rule_conds_ex.
        spec_case_silent.
        solve_sim_mesi.

      + (* [l1GetMRsDownDown] *)
        disc_rule_conds_ex.
        spec_case_set oidx.

        derive_footprint_info_basis oidx.
        derive_child_chns.
        disc_rule_conds_ex.

        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_rsDown oidx).
        disc_rule_conds_ex.

        solve_sim_mesi_ext_mp.
        solve_SpecStateCoh.
        case_ImplStateCoh_l1_me_others.
        * mred; simpl.
          eapply ObjExcl0_ObjCoh.
          { specialize (H19 oidx); repeat (simpl in H19; mred); dest.
            assumption.
          }
          { split.
            { simpl; solve_mesi. }
            { do 2 red; simpl.
              apply MsgsP_other_midx_enqMP;
                [|intro; dest_in;
                  inv H43; eapply l1ExtOf_not_eq; eauto].
              apply MsgsP_deqMP.
              assumption.
            }
          }
          
        * clear H4. (* In oidx .. *)
          mred; simpl.
          assert (exists lost lorq, oss@[lidx] = Some lost /\
                                    orqs@[lidx] = Some lorq).
          { specialize (H15 _ H33).
            solve_rule_conds_ex.
          }
          destruct H4 as [lost [lorq [? ?]]]; rewrite H4, H42; simpl.
          eapply ObjInvalid_ObjCoh.
          { apply Hnmcf; [assumption|simpl; mred]. }
          { eapply InvExcl_excl_invalid; [eapply H19|..];
              try eassumption; try reflexivity; try (simpl; mred); try solve_mesi.
            do 2 red.
            apply MsgsP_other_midx_enqMP;
              [|intro; dest_in;
                inv H44; eapply l1ExtOf_not_eq; eauto].
            apply MsgsP_deqMP.
            assumption.
          }
          
      + (* [l1DownIImm] *)
        disc_rule_conds_ex.
        spec_case_silent.
        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_rqDown oidx).
        disc_rule_conds_ex.
        solve_sim_mesi.

      + (* [l1InvRqUpUp] *)
        disc_rule_conds_ex.
        spec_case_silent.
        solve_sim_mesi.
        
      + (* [l1InvRqUpUpM] *)
        disc_rule_conds_ex.
        spec_case_silent.
        assert (NoRsI oidx msgs)
          by (solve_NoRsI_base; solve_NoRsI_by_no_locks oidx).
        disc_rule_conds_ex.
        solve_sim_mesi.

      + (* [l1InvRsDownDown] *)
        disc_rule_conds_ex.
        spec_case_silent.
        derive_footprint_info_basis oidx.
        disc_rule_conds_ex.
        solve_sim_mesi.
        
  Qed.

  Theorem mesi_ok:
    (steps step_m) # (steps step_m) |-- impl ⊑ spec.
  Proof.
    apply invSim_implies_refinement
      with (ginv:= MesiInv.InvForSim topo) (sim:= SimMESI).
    - apply mesi_sim_ok.
    - apply mesi_InvForSim_ok.
    - apply mesi_sim_init.
    - apply mesi_InvForSim_init.
  Qed.

End Sim.

