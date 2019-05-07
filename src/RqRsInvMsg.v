Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section FootprintInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hitr: GoodRqRsSys dtr sys).

  Definition FootprintUpOkEx (oidx: IdxT) (rqi: RqInfo Msg) :=
    exists rqFrom rqTo rsFrom rsbTo,
      rqi.(rqi_minds_rss) = [rsFrom] /\
      rqi.(rqi_midx_rsb) = rsbTo /\
      FootprintUpOk dtr oidx rqFrom rqTo rsFrom rsbTo.

  Definition FootprintDownOkEx (oidx: IdxT) (rqi: RqInfo Msg) :=
    exists rqFrom rqTos rssFrom rsbTo,
      rqi.(rqi_minds_rss) = rssFrom /\
      rqi.(rqi_midx_rsb) = rsbTo /\
      (FootprintUpDownOk dtr sys oidx rqFrom rqTos rssFrom rsbTo \/
       FootprintDownDownOk dtr oidx rqFrom rqTos rssFrom rsbTo).

  Definition FootprintsOkORqs (orqs: ORqs Msg) :=
    forall oidx,
      orqs@[oidx] >>=[True]
          (fun orq =>
             (orq@[upRq] >>=[True] (fun rqiu => FootprintUpOkEx oidx rqiu)) /\
             (orq@[downRq] >>=[True] (fun rqid => FootprintDownOkEx oidx rqid))).

  Lemma footprints_ok_orqs_add:
    forall orqs,
      FootprintsOkORqs orqs ->
      forall oidx norq,
        norq@[upRq] >>=[True] (fun rqiu => FootprintUpOkEx oidx rqiu) ->
        norq@[downRq] >>=[True] (fun rqid => FootprintDownOkEx oidx rqid) ->
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
    intros; simpl; mred.
    specialize (Hiorqs oidx); simpl in Hiorqs.
    destruct ((sys_orqs_inits sys)@[oidx]) as [orq|]; simpl in *; auto.
    subst; mred; simpl; auto.
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
      apply footprints_ok_orqs_add; auto; try (mred; fail).
    - disc_rule_conds.
      apply footprints_ok_orqs_add; auto; try (mred; fail).
    - disc_rule_conds.
      + apply footprints_ok_orqs_add; disc_rule_conds; auto.
        do 4 eexists; repeat split; eassumption.
      + apply footprints_ok_orqs_add; disc_rule_conds; auto.
        do 4 eexists; repeat split; left; eassumption.
      + apply footprints_ok_orqs_add; disc_rule_conds; auto.
        do 4 eexists; repeat split; right; eassumption.
    - disc_rule_conds.
      + apply footprints_ok_orqs_add; disc_rule_conds; auto.
      + apply footprints_ok_orqs_add; disc_rule_conds; auto.
    - disc_rule_conds.
      apply footprints_ok_orqs_add; disc_rule_conds; auto.
      do 4 eexists; repeat split; disc_rule_conds; eauto.
  Qed.

  Lemma footprints_ok:
    InvReachable sys step_m FootprintsOk.
  Proof.
    eapply inv_reachable.
    - apply footprints_ok_init.
    - apply footprints_ok_step.
  Qed.
  
End FootprintInv.

Ltac good_footprint_get oidx :=
  match goal with
  | [Hfpok: FootprintsOk _ _ _, Ho: _@[oidx] = Some _ |- _] =>
    let H := fresh "H" in
    pose proof Hfpok as H;
    specialize (H oidx); simpl in H; mred; dest
  end.

Ltac disc_footprints_ok :=
  match goal with
  | [H: FootprintUpOkEx _ _ _ |- _] =>
    let rqFrom := fresh "rqFrom" in
    let rqTo := fresh "rqTo" in
    let rsFrom := fresh "rsFrom" in
    let rsbTo := fresh "rsbTo" in
    destruct H as [rqFrom [rqTo [rsFrom [rsbTo ?]]]]; dest
  | [H: FootprintDownOkEx _ _ _ _ |- _] =>
    let rqFrom := fresh "rqFrom" in
    let rqTos := fresh "rqTos" in
    let rssFrom := fresh "rssFrom" in
    let rsbTo := fresh "rsbTo" in
    destruct H as [rqFrom [rqTos [rssFrom [rsbTo ?]]]]; dest

  | [H: FootprintUpOk _ _ _ _ _ _ |- _] =>
    let cidx := fresh "cidx" in
    destruct H as [cidx ?]; dest
  | [H: FootprintUpDownOk _ _ _ _ _ _ _ \/
        FootprintDownDownOk _ _ _ _ _ _ |- _] => destruct H
  | [H: exists _, FootprintUpDownOk _ _ _ _ _ _ _ |- _] =>
    let rsFrom := fresh "rqFrom" in
    destruct H as [rqFrom ?]; dest
  | [H: FootprintUpDownOk _ _ _ _ _ _ _ |- _] =>
    let upCIdx := fresh "upCIdx" in
    let upCObj := fresh "upCObj" in
    destruct H as [upCIdx [upCObj ?]]; dest
  | [H: FootprintDownDownOk _ _ _ _ _ _ |- _] => red in H; dest
  end.

Section IncomingMessageInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hitr: GoodRqRsSys dtr sys).

  Definition RqUpMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    exists cidx rqUp,
      msgs = [rqUp] /\
      msg_type (valOf rqUp) = MRq /\
      parentIdxOf dtr cidx = Some oidx /\
      rqEdgeUpFrom dtr cidx = Some (idOf rqUp).

  Definition RqDownMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    exists obj rqDown,
      msgs = [rqDown] /\
      msg_type (valOf rqDown) = MRq /\
      edgeDownTo dtr oidx = Some (idOf rqDown) /\
      In obj sys.(sys_objs) /\ obj.(obj_idx) = oidx.

  Definition RsUpMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    Forall (fun msg => msg_type (valOf msg) = MRs) msgs /\
    Forall (fun rs =>
              exists cidx,
                parentIdxOf dtr cidx = Some oidx /\
                rsEdgeUpFrom dtr cidx = Some rs)
           (idsOf msgs).

  Definition RsDownMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    exists obj rsDown,
      msgs = [rsDown] /\
      msg_type (valOf rsDown) = MRs /\
      edgeDownTo dtr oidx = Some (idOf rsDown) /\
      In obj sys.(sys_objs) /\ obj.(obj_idx) = oidx.
  
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
    pose proof (footprints_ok Hiorqs Hitr H).

    inv H0.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - left.
      disc_rule_conds.
      constr_rule_conds.

    - right; left.
      disc_rule_conds.
      constr_rule_conds.

    - disc_rule_conds.
      + left; constr_rule_conds.
      + left; constr_rule_conds.
      + right; left; constr_rule_conds.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + right; right; right.
        constr_rule_conds.
      + right; right; left.
        rewrite <-H26 in H19.
        split; auto.
        clear -H19; apply Forall_forall; intros.
        eapply RqRsDownMatch_rs_rq in H19; [|eassumption].
        dest; eauto.
      + right; right; left.
        rewrite <-H26 in H4.
        split; auto.
        clear -H4; apply Forall_forall; intros.
        eapply RqRsDownMatch_rs_rq in H4; [|eassumption].
        dest; eauto.

    - right; right; right.
      disc_rule_conds.
      constr_rule_conds.
  Qed.

End IncomingMessageInv.

Section OutgoingMessageInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hitr: GoodRqRsSys dtr sys).

  Definition RqUpOutMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    exists rqUp,
      msgs = [rqUp] /\
      msg_type (valOf rqUp) = MRq /\
      rqEdgeUpFrom dtr oidx = Some (idOf rqUp).

  Definition RqDownOutMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    Forall (fun msg => msg_type (valOf msg) = MRq) msgs /\
    Forall (fun rq =>
              exists cidx,
                parentIdxOf dtr cidx = Some oidx /\
                edgeDownTo dtr cidx = Some rq)
           (idsOf msgs).

  Definition RsUpOutMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    exists rsUp,
      msgs = [rsUp] /\
      msg_type (valOf rsUp) = MRs /\
      rsEdgeUpFrom dtr oidx = Some (idOf rsUp).

  Definition RsDownOutMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    exists cidx rsDown,
      msgs = [rsDown] /\
      msg_type (valOf rsDown) = MRs /\
      parentIdxOf dtr cidx = Some oidx /\
      edgeDownTo dtr cidx = Some (idOf rsDown).
  
  Ltac disc_rule_custom ::=
    disc_footprints_ok.
  
  Lemma messages_out_cases:
    forall st1 oidx ridx rins routs st2,
      Reachable (steps step_m) sys st1 ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      RqUpOutMsgs oidx routs \/
      RqDownOutMsgs oidx routs \/
      RsUpOutMsgs oidx routs \/
      RsDownOutMsgs oidx routs.
  Proof.
    intros.

    (* Register some necessary invariants to prove this invariant. *)
    pose proof (footprints_ok Hiorqs Hitr H).

    inv H0.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - right; right; right.
      disc_rule_conds.
      constr_rule_conds.

    - right; right; left.
      disc_rule_conds.
      constr_rule_conds.

    - disc_rule_conds.
      + left; constr_rule_conds.
      + right; left.
        constr_rule_conds.
        clear -H17; apply Forall_forall; intros.
        eapply RqRsDownMatch_rq_rs in H17; [|eassumption].
        dest; eauto.
      + right; left.
        constr_rule_conds.
        clear -H3; apply Forall_forall; intros.
        eapply RqRsDownMatch_rq_rs in H3; [|eassumption].
        dest; eauto.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + right; right; right.
        constr_rule_conds.
      + right; right; right.
        constr_rule_conds.
      + right; right; left.
        constr_rule_conds.

    - right; left.
      disc_rule_conds.
      constr_rule_conds.
      clear -H17; apply Forall_forall; intros.
      eapply RqRsDownMatch_rq_rs in H17; [|eassumption].
      dest; eauto.
  Qed.

End OutgoingMessageInv.

Ltac disc_messages_in :=
  match goal with
  | [H: RqUpMsgs _ _ _ |- _] =>
    let cidx := fresh "cidx" in
    let rqUp := fresh "rqUp" in
    destruct H as [cidx [rqUp ?]]; dest; subst
  | [H: RqDownMsgs _ _ _ _ |- _] =>
    let obj := fresh "obj" in
    let rqDown := fresh "rqDown" in
    destruct H as [obj [rqDown ?]]; dest; subst
  | [H: RsUpMsgs _ _ _ |- _] => red in H; dest
  | [H: RsDownMsgs _ _ _ _ |- _] =>
    let obj := fresh "obj" in
    let rsDown := fresh "rsDown" in
    destruct H as [obj [rsDown ?]]; dest; subst
  end.

Ltac disc_messages_out :=
  match goal with
  | [H: RqUpOutMsgs _ _ _ |- _] =>
    let rqUp := fresh "rqUp" in
    destruct H as [rqUp ?]; dest; subst
  | [H: RqDownOutMsgs _ _ _ |- _] => red in H; dest
  | [H: RsUpOutMsgs _ _ _ |- _] =>
    let rsUp := fresh "rsUp" in
    destruct H as [rsUp ?]; dest; subst
  | [H: RsDownOutMsgs _ _ _ |- _] =>
    let cidx := fresh "cidx" in
    let rsDown := fresh "rsDown" in
    destruct H as [cidx [rsDown ?]]; dest; subst
  end.

Section MsgInitCases.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypothesis (Hiorqs: GoodORqsInit (initsOf sys))
             (Hrrs: RqRsSys dtr sys).

  Lemma msg_init_cases_ok:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        exists oidx,
          RqUpMsgs dtr oidx inits \/
          RqDownMsgs dtr sys oidx inits \/
          RsUpMsgs dtr oidx inits \/
          RsDownMsgs dtr sys oidx inits.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst.
    - inv_steps.
      exists oidx.
      eapply messages_in_cases; eauto.
    - inv_steps; eauto.
  Qed.

End MsgInitCases.

Section ExtRss.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypothesis (Hers: GoodExtRssSys sys).

  Definition ExtRssInvMP (msgs: MessagePool Msg) :=
    ForallQ (fun ers ersq =>
               In ers sys.(sys_merss) ->
               Forall (fun msg => msg_type msg = MRs) ersq) msgs.

  Definition ExtRssInv (st: MState oifc) :=
    ExtRssInvMP st.(bst_msgs).
    
  Lemma extRssInv_init: InvInit sys ExtRssInv.
  Proof.
    repeat red; intros.
    constructor.
  Qed.

  Lemma extRssInv_case_outs:
    forall oss orqs msgs (eouts: list (Id Msg)),
      ExtRssInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      Forall (FirstMPI msgs) eouts ->
      NoDup (idsOf eouts) ->
      ExtRssInv {| bst_oss := oss;
                   bst_orqs := orqs;
                   bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    intros.
    do 2 red in H; do 2 red; simpl in *.
    red; intros.
    specialize (H _ H2).
    destruct (in_dec eq_nat_dec midx (idsOf eouts)).
    + eapply findQ_In_NoDup_deqMsgs with (mp:= msgs) in H1; eauto.
      * destruct H1 as [hmsg ?].
        rewrite <-H1 in H.
        inv H; assumption.
      * intro Hx.
        apply in_map_iff in i.
        destruct i as [[midx' msg] [? ?]]; subst; simpl in *.
        rewrite Forall_forall in H0; specialize (H0 _ H4).
        eapply FirstMP_findQ_False in Hx; eauto.
    + rewrite findQ_not_In_deqMsgs by assumption.
      assumption.
  Qed.

  Lemma extRssInv_step: InvStep sys step_m ExtRssInv.
  Proof.
    red; induction 3; simpl; intros; subst; auto.
    - do 2 red in H0; do 2 red; simpl in *.
      red; intros.
      specialize (H0 _ H3).
      destruct H2.
      rewrite findQ_not_In_enqMsgs; [assumption|].
      eapply DisjList_In_1; [|eassumption].
      eapply DisjList_SubList; [eassumption|].
      apply sys_merqs_sys_merss_DisjList.

    - apply extRssInv_case_outs; auto.
      apply H3.

    - eapply extRssInv_case_outs in H0; [|eassumption|apply H7].
      do 2 red in H0; do 2 red; simpl in *.
      red; intros.
      specialize (H0 _ H3).
      destruct (in_dec eq_nat_dec midx (idsOf outs)).
      + apply in_map_iff in i.
        destruct i as [[midx' msg] [? ?]]; simpl in *; subst.
        rewrite findQ_In_NoDup_enqMsgs with (msg:= msg); [|apply H10|assumption].
        apply Forall_app; [assumption|].
        repeat constructor.
        pose proof Hers.
        red in H12; rewrite Forall_forall in H12; specialize (H12 _ H1).
        red in H12; rewrite Forall_forall in H12; specialize (H12 _ H2).
        red in H12; specialize (H12 _ _ _ _ _ _ H8 H9).
        specialize (H12 _ H13 H3); assumption.
      + rewrite findQ_not_In_enqMsgs by assumption.
        assumption.
  Qed.

  Lemma extRssInv_ok: InvReachable sys step_m ExtRssInv.
  Proof.
    apply inv_reachable.
    - apply extRssInv_init.
    - apply extRssInv_step.
  Qed.

End ExtRss.

Lemma msgs_ext_out_rss:
  forall {oifc} (sys: System oifc) msgs eouts,
    SubList (idsOf eouts) sys.(sys_merss) ->
    Forall (FirstMPI msgs) eouts ->
    ExtRssInvMP sys msgs ->
    Forall (fun emsg => msg_type (valOf emsg) = MRs) eouts.
Proof.
  intros.
  rewrite Forall_forall in H0.
  apply Forall_forall; intros [emidx emsg] ?.
  specialize (H0 _ H2).
  apply FirstMP_InMP in H0; simpl in H0.
  apply in_map with (f:= idOf) in H2; simpl in H2.
  apply H in H2.
  specialize (H1 _ H2).
  rewrite Forall_forall in H1; specialize (H1 _ H0).
  assumption.
Qed.

Close Scope list.
Close Scope fmap.

