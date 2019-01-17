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

  Hypothesis (Hitr: GoodRqRsSys dtr sys).

  Definition FootprintUpOkEx (oidx: IdxT) (rqi: RqInfo Msg) :=
    exists rqFrom rqTo rsFrom rsbTo,
      rqi.(rqi_minds_rss) = [rsFrom] /\
      rqi.(rqi_midx_rsb) = rsbTo /\
      FootprintUpOk dtr oidx rqFrom rqTo rsFrom rsbTo.

  Definition FootprintDownOkEx (oidx: IdxT) (rqi: RqInfo Msg) :=
    exists rqFrom rqTos rssFrom rsbTo,
      rqi.(rqi_minds_rss) = rssFrom /\
      rqi.(rqi_midx_rsb) = rsbTo /\
      (FootprintUpDownOk dtr oidx rqFrom rqTos rssFrom rsbTo \/
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
      + apply footprints_ok_orqs_add; disc_rule_conds; auto.
        * do 4 eexists; repeat split; eassumption.
        * rewrite <-H20; assumption.
      + apply footprints_ok_orqs_add; disc_rule_conds; auto.
        * rewrite <-H19; assumption.
        * do 4 eexists; repeat split.
          left; eassumption.
      + apply footprints_ok_orqs_add; disc_rule_conds; auto.
        * rewrite <-H19; assumption.
        * do 4 eexists; repeat split.
          right; eassumption.
    - disc_rule_conds.
      + apply footprints_ok_orqs_add; disc_rule_conds; auto.
        rewrite <-H15; assumption.
      + apply footprints_ok_orqs_add; disc_rule_conds; auto.
        rewrite <-H15; assumption.
    - disc_rule_conds.
      apply footprints_ok_orqs_add; disc_rule_conds; auto.
      do 4 eexists; repeat split.
      left; eassumption.
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
  | [Hfpok: FootprintsOk _ _, Ho: _@[oidx] = Some _ |- _] =>
    let H := fresh "H" in
    pose proof Hfpok as H;
    specialize (H oidx); simpl in H
  end.

Ltac disc_footprints_ok :=
  match goal with
  | [H: FootprintsOk _ _ |- _] => red in H
  | [H1: FootprintsOkORqs _ ?orqs, H2: ?orqs @[?oidx] = _ |- _] =>
    let Hf := fresh "H" in
    pose proof (H1 oidx) as Hf;
    rewrite H2 in Hf; simpl in Hf; dest;
    clear H2
  | [H: FootprintUpOkEx _ _ _ |- _] =>
    let rqFrom := fresh "rqFrom" in
    let rqTo := fresh "rqTo" in
    let rsFrom := fresh "rsFrom" in
    let rsbTo := fresh "rsbTo" in
    destruct H as [rqFrom [rqTo [rsFrom [rsbTo ?]]]]; dest
  | [H: FootprintDownOkEx _ _ _ |- _] =>
    let rqFrom := fresh "rqFrom" in
    let rqTos := fresh "rqTos" in
    let rssFrom := fresh "rssFrom" in
    let rsbTo := fresh "rsbTo" in
    destruct H as [rqFrom [rqTos [rssFrom [rsbTo ?]]]]; dest
                                                          
  | [H: FootprintUpOk _ _ _ _ _ _ |- _] =>
    let cidx := fresh "cidx" in
    destruct H as [cidx ?]; dest
  | [H: FootprintUpDownOk _ _ _ _ _ _ \/
        FootprintDownDownOk _ _ _ _ _ _ |- _] => destruct H
  | [H: exists _, FootprintUpDownOk _ _ _ _ _ _ |- _] =>
    let rsFrom := fresh "rqFrom" in
    destruct H as [rqFrom ?]; dest
  | [H: FootprintUpDownOk _ _ _ _ _ _ |- _] =>
    let upCIdx := fresh "upCIdx" in
    destruct H as [upCIdx ?]; dest
  | [H: FootprintDownDownOk _ _ _ _ _ _ |- _] => red in H; dest
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
    Forall (fun rs => exists cidx, rsEdgeUpFrom dtr cidx = Some rs)
           (idsOf msgs).

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
        rewrite H4 in H2.
        disc_rule_conds.
        solve_rule_conds.
      + right; right; left.
        rewrite H2 in H20.
        split; auto.
        clear -H20; apply Forall_forall; intros.
        eapply RqRsDownMatch_rs_In in H20; [|eassumption].
        dest; eauto.
      + right; right; left.
        rewrite H2 in H19.
        split; auto.
        clear -H19; apply Forall_forall; intros.
        eapply RqRsDownMatch_rs_In in H19; [|eassumption].
        dest; eauto.

    - right; right; right.
      disc_rule_conds.
      solve_rule_conds.
  Qed.
    
End MessageInv.

Close Scope list.
Close Scope fmap.

