Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.

Set Implicit Arguments.

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
  repeat
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
        rewrite H2 in H23.
        split; auto.
        clear -H23; apply Forall_forall; intros.
        eapply RqRsDownMatch_rs_In in H23; [|eassumption].
        dest; eauto.
      + right; right; left.
        rewrite H2 in H22.
        split; auto.
        clear -H22; apply Forall_forall; intros.
        eapply RqRsDownMatch_rs_In in H22; [|eassumption].
        dest; eauto.

    - right; right; right.
      disc_rule_conds.
      solve_rule_conds.
  Qed.
    
End MessageInv.

Section LockInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypotheses (Hrr: GoodRqRsSys dtr sys)
             (Hsd: RqRsDTree dtr sys).

  Section OnMState.
    Variables (orqs: ORqs Msg)
              (msgs: MessagePool Msg).

    Definition OUpLockedTo (oidx: IdxT) (rsbTo: IdxT) :=
      orqs@[oidx] >>=[False]
          (fun orq =>
             exists rqi,
               orq@[upRq] = Some rqi /\
               rqi.(rqi_midx_rsb) = rsbTo).

    Definition ODownLockedTo (oidx: IdxT) (rsbTo: IdxT) :=
      orqs@[oidx] >>=[False]
          (fun orq =>
             exists rqi,
               orq@[downRq] = Some rqi /\
               rqi.(rqi_midx_rsb) = rsbTo).
    
    Definition OUpLockFree (oidx: IdxT) :=
      orqs@[oidx] >>=[True] (fun orq => UpLockFreeORq orq).

    Definition ONoUpLockTo (oidx: IdxT) (rsbTo: IdxT) :=
      orqs@[oidx] >>=[True]
          (fun orq =>
             match orq@[upRq] with
             | Some rqi => rqi.(rqi_midx_rsb) <> rsbTo
             | None => True
             end).

    Definition ODownLockFree (oidx: IdxT) :=
      orqs@[oidx] >>=[True] (fun orq => DownLockFreeORq orq).
    
    Definition UpLockFreeInv (oidx: IdxT) :=
      parentIdxOf dtr oidx = None \/
      exists rqUp down pidx,
        rqEdgeUpFrom dtr oidx = Some rqUp /\
        edgeDownTo dtr oidx = Some down /\
        parentIdxOf dtr oidx = Some pidx /\
        findQ rqUp msgs = nil /\
        rssQ msgs down = nil /\
        ONoUpLockTo pidx down.
    
    Definition UpLockedInv (oidx: IdxT) :=
      exists rqUp down pidx,
        rqEdgeUpFrom dtr oidx = Some rqUp /\
        edgeDownTo dtr oidx = Some down /\
        parentIdxOf dtr oidx = Some pidx /\
        length (findQ rqUp msgs) <= 1 /\
        length (rssQ msgs down) <= 1 /\
        xor3 (length (findQ rqUp msgs) = 1)
             (length (rssQ msgs down) = 1)
             (OUpLockedTo pidx down).

    Definition DownLockFreeInv (oidx: IdxT) :=
      forall cidx,
        parentIdxOf dtr cidx = Some oidx ->
        ((edgeDownTo dtr cidx) >>=[True] (fun down => rqsQ msgs down = nil) /\
         (rsEdgeUpFrom dtr cidx) >>=[True] (fun rsUp => findQ rsUp msgs = nil)).
    
    Definition DownLockedInv (oidx: IdxT) (rqi: RqInfo Msg) :=
      Forall (fun rsUp =>
                exists down cidx,
                  edgeDownTo dtr cidx = Some down /\
                  rsEdgeUpFrom dtr cidx = Some rsUp /\
                  parentIdxOf dtr cidx = Some oidx /\
                  length (rqsQ msgs down) <= 1 /\
                  length (findQ rsUp msgs) <= 1 /\
                  xor3 (length (rqsQ msgs down) = 1)
                       (length (findQ rsUp msgs) = 1)
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
    - red.
      remember (parentIdxOf dtr oidx) as opidx.
      destruct opidx as [pidx|]; [right|left; reflexivity].
      pose proof (eq_sym Heqopidx).
      eapply parentIdxOf_Some in H0; [|eassumption].
      destruct H0 as [rqUp [rsUp [down ?]]]; dest.
      do 3 eexists; repeat split; try eassumption.
    - red; intros; split.
      + destruct (edgeDownTo dtr cidx); simpl; auto.
      + destruct (rsEdgeUpFrom dtr cidx); simpl; auto.
  Qed.

  Lemma ONoUpLockTo_not_OUpLockedTo:
    forall orqs oidx rsbTo,
      ONoUpLockTo orqs oidx rsbTo -> ~ OUpLockedTo orqs oidx rsbTo.
  Proof.
    unfold ONoUpLockTo, OUpLockedTo; intros.
    intro Hx.
    destruct (orqs@[oidx]); simpl in *; auto.
    destruct Hx as [rqi ?]; dest.
    rewrite H0 in H; elim H; assumption.
  Qed.

  Lemma not_ONoUpLockTo_OUpLockedTo:
    forall orqs oidx rsbTo,
      ~ OUpLockedTo orqs oidx rsbTo -> ONoUpLockTo orqs oidx rsbTo.
  Proof.
    unfold ONoUpLockTo, OUpLockedTo; intros.
    destruct (orqs@[oidx]); simpl in *; auto.
    destruct (o@[upRq]); auto.
    intro Hx; elim H.
    eexists; split; eauto.
  Qed.

  Lemma OUpLockedTo_orqs_preserved:
    forall orqs1 orqs2 oidx rsbTo,
      OUpLockedTo orqs1 oidx rsbTo ->
      orqs1@[oidx] = orqs2@[oidx] ->
      OUpLockedTo orqs2 oidx rsbTo.
  Proof.
    unfold OUpLockedTo; intros.
    rewrite <-H0; assumption.
  Qed.

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
    rewrite <-H0, <-H1.
    repeat split; try assumption.
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
        eapply rqrsDTree_rqEdgeUpFrom_sys_minds; eauto.
    - destruct H as [rqUp [down [pidx ?]]]; dest.
      rewrite H1.
      unfold rssQ.
      rewrite findQ_not_In_enqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
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
        eapply rqrsDTree_rqEdgeUpFrom_sys_minds; eauto.
    - destruct H as [rqUp [down [pidx ?]]]; dest.
      rewrite H1.
      unfold rssQ.
      rewrite findQ_not_In_deqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
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
    destruct H; [left; assumption|right].
    destruct H as [rqUp [down [pidx ?]]]; dest.
    rewrite H in H0.
    rewrite H2 in H1.
    exists rqUp, down, pidx; repeat split;
      try assumption; try congruence.
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
        eapply rqrsDTree_rqEdgeUpFrom_sys_minds; eauto.
    - red in H; dest.
      remember (edgeDownTo dtr oidx) as down.
      destruct down as [down|]; simpl in *; dest; auto.
      unfold rssQ.
      rewrite findQ_not_In_enqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
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
        eapply rqrsDTree_rqEdgeUpFrom_sys_minds; eauto.
    - red in H; dest.
      remember (edgeDownTo dtr oidx) as down.
      destruct down as [down|]; simpl in *; dest; auto.
      unfold rssQ.
      rewrite findQ_not_In_deqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
  Qed.

  Lemma upLockInvORq_msgs_preserved:
    forall orqs msgs1 msgs2 oidx orq,
      UpLockInvORq orqs msgs1 oidx orq ->
      (match rqEdgeUpFrom dtr oidx with
       | Some rqUp => findQ rqUp msgs1 = findQ rqUp msgs2
       | None => False
       end) ->
      (match edgeDownTo dtr oidx with
       | Some down => rssQ msgs1 down = rssQ msgs2 down
       | None => False
       end) ->
      UpLockInvORq orqs msgs2 oidx orq.
  Proof.
    unfold UpLockInvORq; intros.
    destruct (orq@[upRq]).
    - eapply upLockedInv_msgs_preserved; eauto.
    - eapply upLockFreeInv_msgs_preserved.
      + eassumption.
      + destruct (rqEdgeUpFrom dtr oidx); auto.
      + destruct (edgeDownTo dtr oidx); auto.
  Qed.

  Lemma downLockedInv_msgs_preserved:
    forall orqs msgs1 msgs2 oidx rqi,
      DownLockedInv orqs msgs1 oidx rqi ->
      (forall rsUp down cidx,
          In rsUp (rqi_minds_rss rqi) ->
          edgeDownTo dtr cidx = Some down ->
          rsEdgeUpFrom dtr cidx = Some rsUp ->
          parentIdxOf dtr cidx = Some oidx ->
          rqsQ msgs1 down = rqsQ msgs2 down /\
          findQ rsUp msgs1 = findQ rsUp msgs2) ->
      DownLockedInv orqs msgs2 oidx rqi.
  Proof.
    unfold DownLockedInv; simpl; intros.
    rewrite Forall_forall in H.
    apply Forall_forall; intros rsUp ?.
    specialize (H _ H1).
    destruct H as [down [cidx ?]]; dest.
    specialize (H0 _ _ _ H1 H H2 H3); dest.
    exists down, cidx.
    rewrite <-H0, <-H7.
    repeat split; try assumption.
  Qed.
  
  Corollary downLockedInv_enqMsgs_preserved:
    forall orqs msgs emsgs oidx rqi,
      DownLockedInv orqs msgs oidx rqi ->
      DisjList (idsOf emsgs) (sys_minds sys) ->
      DownLockedInv orqs (enqMsgs emsgs msgs) oidx rqi.
  Proof.
    intros.
    eapply downLockedInv_msgs_preserved; eauto.
    intros; split.
    - unfold rqsQ.
      rewrite findQ_not_In_enqMsgs; [reflexivity|].
      eapply DisjList_In_1; [eassumption|].
      eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
    - rewrite findQ_not_In_enqMsgs; [reflexivity|].
      eapply DisjList_In_1; [eassumption|].
      eapply rqrsDTree_rsEdgeUpFrom_sys_minds; eauto.
  Qed.

  Corollary downLockedInv_deqMsgs_preserved:
    forall orqs msgs eminds oidx rqi,
      DownLockedInv orqs msgs oidx rqi ->
      DisjList eminds (sys_minds sys) ->
      DownLockedInv orqs (deqMsgs eminds msgs) oidx rqi.
  Proof.
    intros.
    eapply downLockedInv_msgs_preserved; eauto.
    intros; split.
    - unfold rqsQ.
      rewrite findQ_not_In_deqMsgs; [reflexivity|].
      eapply DisjList_In_1; [eassumption|].
      eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
    - rewrite findQ_not_In_deqMsgs; [reflexivity|].
      eapply DisjList_In_1; [eassumption|].
      eapply rqrsDTree_rsEdgeUpFrom_sys_minds; eauto.
  Qed.

  Lemma downLockFreeInv_msgs_preserved:
    forall msgs1 msgs2 oidx,
      DownLockFreeInv msgs1 oidx ->
      (forall cidx,
          parentIdxOf dtr cidx = Some oidx ->
          (forall down,
              edgeDownTo dtr cidx = Some down ->
              rqsQ msgs1 down = rqsQ msgs2 down) /\
          (forall rsUp,
              rsEdgeUpFrom dtr cidx = Some rsUp ->
              findQ rsUp msgs1 = findQ rsUp msgs2)) ->
      DownLockFreeInv msgs2 oidx.
  Proof.
    unfold DownLockFreeInv; simpl; intros.
    specialize (H _ H1); dest.
    specialize (H0 _ H1); dest.
    split.
    - remember (edgeDownTo dtr cidx) as down.
      destruct down as [down|]; simpl in *; dest; auto.
      rewrite <-H0; auto.
    - remember (rsEdgeUpFrom dtr cidx) as rsUp.
      destruct rsUp as [rsUp|]; simpl in *; dest; auto.
      rewrite <-H3; auto.
  Qed.
  
  Corollary downLockFreeInv_enqMsgs_preserved:
    forall msgs emsgs oidx,
      DownLockFreeInv msgs oidx ->
      DisjList (idsOf emsgs) (sys_minds sys) ->
      DownLockFreeInv (enqMsgs emsgs msgs) oidx.
  Proof.
    intros.
    eapply downLockFreeInv_msgs_preserved; eauto.
    intros; split; intros.
    - unfold rqsQ.
      rewrite findQ_not_In_enqMsgs; [reflexivity|].
      eapply DisjList_In_1; [eassumption|].
      eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
    - rewrite findQ_not_In_enqMsgs; [reflexivity|].
      eapply DisjList_In_1; [eassumption|].
      eapply rqrsDTree_rsEdgeUpFrom_sys_minds; eauto.
  Qed.

  Lemma downLockFreeInv_deqMsgs_preserved:
    forall msgs eminds oidx,
      DownLockFreeInv msgs oidx ->
      DisjList eminds (sys_minds sys) ->
      DownLockFreeInv (deqMsgs eminds msgs) oidx.
  Proof.
    intros.
    eapply downLockFreeInv_msgs_preserved; eauto.
    intros; split; intros.
    - unfold rqsQ.
      rewrite findQ_not_In_deqMsgs; [reflexivity|].
      eapply DisjList_In_1; [eassumption|].
      eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
    - rewrite findQ_not_In_deqMsgs; [reflexivity|].
      eapply DisjList_In_1; [eassumption|].
      eapply rqrsDTree_rsEdgeUpFrom_sys_minds; eauto.
  Qed.

  Lemma upLockedInv_orqs_preserved:
    forall orqs1 orqs2 msgs oidx pidx,
      UpLockedInv orqs1 msgs oidx ->
      parentIdxOf dtr oidx = Some pidx ->
      orqs1@[pidx] = orqs2@[pidx] ->
      UpLockedInv orqs2 msgs oidx.
  Proof.
    unfold UpLockedInv; intros.
    destruct H as [rqUp [down [pidx' ?]]]; dest.
    rewrite H3 in H0; inv H0.
    exists rqUp, down, pidx; repeat split; try assumption.
    destruct H6.
    - xfst; try assumption.
      intro Hx; elim H7.
      red; rewrite H1; assumption.
    - xsnd; try assumption.
      intro Hx; elim H7.
      red; rewrite H1; assumption.
    - xthd; try assumption.
      red; rewrite <-H1; assumption.
  Qed.

  Corollary upLockedInv_orqs_preserved_add:
    forall orqs msgs oidx orq,
      UpLockedInv orqs msgs oidx ->
      UpLockedInv (orqs+[oidx <- orq]) msgs oidx.
  Proof.
    intros.
    destruct Hsd.
    pose proof H.
    destruct H2 as [rqUp [down [pidx ?]]]; dest.
    eapply upLockedInv_orqs_preserved; eauto.
    apply parentIdxOf_not_eq in H4; [|assumption].
    mred.
  Qed.

  Corollary upLockedInv_orqs_preserved_add_parent:
    forall orqs msgs oidx1 oidx2 orq,
      UpLockedInv orqs msgs oidx1 ->
      parentIdxOf dtr oidx1 <> Some oidx2 ->
      UpLockedInv (orqs+[oidx2 <- orq]) msgs oidx1.
  Proof.
    intros.
    destruct Hsd.
    pose proof H.
    destruct H3 as [rqUp [down [pidx ?]]]; dest.
    eapply upLockedInv_orqs_preserved; eauto.
    mred.
  Qed.

  Lemma upLockFreeInv_orqs_preserved:
    forall orqs1 orqs2 msgs oidx pidx,
      UpLockFreeInv orqs1 msgs oidx ->
      parentIdxOf dtr oidx = Some pidx ->
      orqs1@[pidx] = orqs2@[pidx] ->
      UpLockFreeInv orqs2 msgs oidx.
  Proof.
    unfold UpLockFreeInv; intros; dest.
    destruct H; [left; assumption|right].
    destruct H as [rqUp [down [pidx' ?]]]; dest.
    rewrite H3 in H0; inv H0.
    exists rqUp, down, pidx.
    repeat split; try assumption.
    red; rewrite <-H1; assumption.
  Qed.

  Lemma upLockFreeInv_orqs_preserved_add:
    forall orqs msgs oidx orq,
      UpLockFreeInv orqs msgs oidx ->
      UpLockFreeInv (orqs+[oidx <- orq]) msgs oidx.
  Proof.
    unfold UpLockFreeInv; intros; dest.
    destruct H; [left; assumption|right].
    destruct H as [rqUp [down [pidx ?]]]; dest.
    exists rqUp, down, pidx.
    repeat split; try assumption.
    red in H4; red.
    apply parentIdxOf_not_eq in H1; [|destruct Hsd; assumption].
    mred.
  Qed.

  Corollary upLockFreeInv_orqs_preserved_add_parent:
    forall orqs msgs oidx1 oidx2 orq,
      UpLockFreeInv orqs msgs oidx1 ->
      parentIdxOf dtr oidx1 <> Some oidx2 ->
      UpLockFreeInv (orqs+[oidx2 <- orq]) msgs oidx1.
  Proof.
    intros.
    destruct Hsd.
    pose proof H.
    destruct H3; [left; assumption|].
    destruct H3 as [rqUp [down [pidx ?]]]; dest.
    eapply upLockFreeInv_orqs_preserved; eauto.
    mred.
  Qed.

  Lemma upLockInvORq_orqs_preserved:
    forall orqs1 orqs2 msgs oidx pidx orq,
      UpLockInvORq orqs1 msgs oidx orq ->
      parentIdxOf dtr oidx = Some pidx ->
      orqs1@[pidx] = orqs2@[pidx] ->
      UpLockInvORq orqs2 msgs oidx orq.
  Proof.
    unfold UpLockInvORq; intros.
    destruct (orq@[upRq]).
    - eapply upLockedInv_orqs_preserved; eauto.
    - eapply upLockFreeInv_orqs_preserved; eauto.
  Qed.

  Corollary upLockInvORq_orqs_preserved_add:
    forall orqs msgs oidx norq orq,
      UpLockInvORq orqs msgs oidx orq ->
      UpLockInvORq orqs+[oidx <- norq] msgs oidx orq.
  Proof.
    unfold UpLockInvORq; intros.
    destruct (orq@[upRq]).
    - apply upLockedInv_orqs_preserved_add; auto.
    - apply upLockFreeInv_orqs_preserved_add; auto.
  Qed.

  Corollary upLockInvORq_orqs_preserved_add_parent:
    forall orqs msgs oidx1 oidx2 norq orq,
      UpLockInvORq orqs msgs oidx1 orq ->
      parentIdxOf dtr oidx1 <> Some oidx2 ->
      UpLockInvORq (orqs+[oidx2 <- norq]) msgs oidx1 orq.
  Proof.
    unfold UpLockInvORq; intros.
    destruct (orq@[upRq]).
    - apply upLockedInv_orqs_preserved_add_parent; auto.
    - apply upLockFreeInv_orqs_preserved_add_parent; auto.
  Qed.
  
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

  Section InternalStep.
    Variables (oss: OStates oifc) (orqs: ORqs Msg) (msgs: MessagePool Msg)
              (obj: Object oifc) (rule: Rule oifc)
              (post: OState oifc) (porq: ORq Msg) (mins: list (Id Msg))
              (nost: OState oifc) (norq: ORq Msg) (mouts: list (Id Msg)).

    Hypotheses
      (Hfpok: FootprintsOk
                dtr {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |})
      (HobjIn: In obj (sys_objs sys))
      (HruleIn: In rule (obj_rules obj))
      (Hporq: orqs@[obj_idx obj] = Some porq)
      (Hpost: oss@[obj_idx obj] = Some post)
      (HminsF: Forall (FirstMPI msgs) mins)
      (HminsV: ValidMsgsIn sys mins)
      (Hprec: rule_precond rule post porq mins)
      (Htrs: rule_trs rule post porq mins = (nost, norq, mouts))
      (HmoutsV: ValidMsgsOut sys mouts)
      (Hmdisj: DisjList (idsOf mins) (idsOf mouts)).

    Lemma deqMP_rq_filter_rs_eq:
      forall midx msg,
        msg_type msg = MRq ->
        FirstMPI msgs (midx, msg) ->
        filter (fun msg => msg_type msg ==n MRs)
               (findQ midx msgs) =
        filter (fun msg => msg_type msg ==n MRs)
               (findQ midx (deqMP midx msgs)).
    Proof.
      intros.
      unfold FirstMPI, FirstMP, firstMP in H0.
      unfold deqMP, idOf in *; simpl in *.
      destruct (findQ midx msgs); [discriminate|].
      simpl in H0; inv H0.
      unfold findQ; mred; simpl.
      rewrite H; simpl.
      reflexivity.
    Qed.

    Lemma deqMP_rs_filter_rq_eq:
      forall midx msg,
        msg_type msg = MRs ->
        FirstMPI msgs (midx, msg) ->
        filter (fun msg => msg_type msg ==n MRq)
               (findQ midx msgs) =
        filter (fun msg => msg_type msg ==n MRq)
               (findQ midx (deqMP midx msgs)).
    Proof.
      intros.
      unfold FirstMPI, FirstMP, firstMP in H0.
      unfold deqMP, idOf in *; simpl in *.
      destruct (findQ midx msgs); [discriminate|].
      simpl in H0; inv H0.
      unfold findQ; mred; simpl.
      rewrite H; simpl.
      reflexivity.
    Qed.

    Ltac disc_rule_custom ::=
      match goal with
      | [H: FootprintUpOkEx _ _ _ |- _] =>
        let rqFrom := fresh "rqFrom" in
        let rqTo := fresh "rqTo" in
        let rsFrom := fresh "rsFrom" in
        let rsbTo := fresh "rsbTo" in
        destruct H as [rqFrom [rqTo [rsFrom [rsbTo ?]]]]; dest
      | [H: FootprintUpOk _ _ _ _ _ _ |- _] =>
        let cidx := fresh "cidx" in
        destruct H as [cidx ?]; dest

      | [H: FootprintDownOkEx _ _ _ |- _] =>
        let rqFrom := fresh "rqFrom" in
        let rqTos := fresh "rqTos" in
        let rssFrom := fresh "rssFrom" in
        let rsbTo := fresh "rsbTo" in
        destruct H as [rqFrom [rqTos [rssFrom [rsbTo ?]]]]; dest
      | [H: FootprintUpDownOk _ _ _ _ _ _ \/
            FootprintDownDownOk _ _ _ _ _ _ |- _] => destruct H
      | [H: exists _, FootprintUpDownOk _ _ _ _ _ _ |- _] =>
        let rqFrom := fresh "rqFrom" in
        destruct H as [rqFrom ?]
      | [H: FootprintUpDownOk _ _ _ _ _ _ |- _] =>
        let upCIdx := fresh "upCIdx" in
        destruct H as [upCIdx ?]; dest
      | [H: FootprintDownDownOk _ _ _ _ _ _ |- _] => red in H; dest
      end.

    Lemma upLockInvORq_step_int_me:
      UpLockInvORq orqs msgs (obj_idx obj) porq ->
      In (obj_idx obj) (map (@obj_idx _) (sys_objs sys)) ->
      GoodRqRsRule dtr (obj_idx obj) rule ->
      UpLockInvORq (orqs+[obj_idx obj <- norq])
                   (enqMsgs mouts (deqMsgs (idsOf mins) msgs))
                   (obj_idx obj) norq.
    Proof.
      intros.
      destruct Hsd.
      red in H; red.
      good_rqrs_rule_cases rule.

      - (** case [ImmDownRule] *)
        disc_rule_conds.
        apply upLockFreeInv_orqs_preserved_add.
        eapply upLockFreeInv_msgs_preserved; eauto.
        + remember (rqEdgeUpFrom dtr (obj_idx obj)) as orqUp.
          destruct orqUp as [rqUp|]; auto.
          solve_q.
        + remember (edgeDownTo dtr (obj_idx obj)) as odown.
          destruct odown as [down|]; auto.
          solve_q.

      - (** case [ImmUpRule] *)
        disc_rule_conds.
        destruct (porq@[upRq]).
        + apply upLockedInv_orqs_preserved_add.
          eapply upLockedInv_msgs_preserved; eauto.
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
          * disc_rule_conds.
            solve_q.
            eapply deqMP_rq_filter_rs_eq; eauto.
        + apply upLockFreeInv_orqs_preserved_add.
          eapply upLockFreeInv_msgs_preserved; eauto.
          * remember (rqEdgeUpFrom dtr (obj_idx obj)) as orqUp.
            destruct orqUp as [rqUp|]; auto.
            solve_q.
          * disc_rule_conds.
            solve_q.
            eapply deqMP_rq_filter_rs_eq; eauto.

      - (** case [RqFwdRule] *)
        disc_rule_conds.
        + (** case [RqUpUp]; setting an uplock. *)
          apply upLockedInv_orqs_preserved_add.
          red in H.
          pose proof (rqEdgeUpFrom_Some Hsd _ H6).
          destruct H14 as [rsUp [down [pidx ?]]]; dest.
          disc_rule_conds.
          destruct H; [discriminate|].
          destruct H as [rqUp [down' [pidx' ?]]]; dest.
          disc_rule_conds.
          do 3 eexists; repeat split; try eassumption.
          * solve_q.
            rewrite H19; simpl; omega.
          * solve_q.
            unfold rssQ in H20; rewrite H20.
            simpl; omega.
          * xfst.
            { solve_q.
              rewrite H19; reflexivity.
            }
            { solve_q.
              unfold rssQ in H20; rewrite H20; auto.
            }
            { apply ONoUpLockTo_not_OUpLockedTo; assumption. }

        + (** case [RqUpDown]; setting a downlock. *)
          rewrite <-H11.
          remember (porq@[upRq]) as orqiu; destruct orqiu as [rqiu|].
          * apply upLockedInv_orqs_preserved_add.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              rewrite H.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }

          * apply upLockFreeInv_orqs_preserved_add.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr (obj_idx obj)) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr (obj_idx obj)) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }

        + (** case [RqDownDown]; setting a downlock *)
          rewrite <-H11.
          remember (porq@[upRq]) as orqiu; destruct orqiu as [rqiu|].
          * apply upLockedInv_orqs_preserved_add.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { red in H; destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
            { red in H; destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
              eapply deqMP_rq_filter_rs_eq; eauto.
            }

          * apply upLockFreeInv_orqs_preserved_add.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr (obj_idx obj)) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr (obj_idx obj)) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
                eapply deqMP_rq_filter_rs_eq; eauto.
              }
            }

      - (** case [RsBackRule] *)
        good_footprint_get (obj_idx obj).
        disc_rule_conds.
        + (** case [FootprintReleasingUp]; releasing the uplock. *)
          apply upLockFreeInv_orqs_preserved_add.
          destruct i as [rsDown rsbm]; simpl in *.
          destruct H as [rqUp [down [pidx ?]]]; dest.
          rewrite H4 in H6.
          disc_rule_conds.
          eapply xor3_inv_2 with (B:= length (rssQ msgs (fst i)) = 1) in H21;
            [dest|eapply rssQ_length_one; eauto].
          remember (rqi_midx_rsb rqi) as rsbTo; clear HeqrsbTo.
          destruct i as [rsFrom rsm]; simpl in *.
          right.
          exists rqTo, rsFrom, pidx.
          repeat split; try assumption.
          * solve_q.
            apply length_zero_iff_nil; omega.
          * solve_q.
            apply findQ_In_deqMP_FirstMP in H11; simpl in H11.
            unfold rssQ in H20; rewrite <-H11 in H20.
            simpl in H20; rewrite H13 in H20; simpl in H20.
            apply length_zero_iff_nil; omega.
          * apply not_ONoUpLockTo_OUpLockedTo; auto.
          
        + (** case [FootprintReleasingDown]-1 *)
          rewrite <-H8.
          destruct i as [rsDown rsbm]; simpl in *.
          remember (porq@[upRq]) as orqiu; destruct orqiu as [rqiu|].
          * apply upLockedInv_orqs_preserved_add.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              rewrite <-H6.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              rewrite <-H6.
              solve_q.
            }              
          * apply upLockFreeInv_orqs_preserved_add.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr (obj_idx obj)) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                rewrite <-H6.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr (obj_idx obj)) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                rewrite <-H6.
                solve_q.
              }
            }

        + (** case [FootprintReleasingDown]-2 *)
          rewrite <-H8.
          destruct i as [rsDown rsbm]; simpl in *.
          remember (porq@[upRq]) as orqiu; destruct orqiu as [rqiu|].
          * apply upLockedInv_orqs_preserved_add.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              rewrite <-H6.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              rewrite <-H6.
              solve_q.
            }
          * apply upLockFreeInv_orqs_preserved_add.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr (obj_idx obj)) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                rewrite <-H6.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr (obj_idx obj)) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                rewrite <-H6.
                solve_q.
              } 
            }

      - (** case [RsDownRqDownRule] *)
        disc_rule_conds.
        destruct i as [rsDown rsm]; simpl in *.
        apply upLockFreeInv_orqs_preserved_add.
        destruct H as [rqUp [down [pidx ?]]]; dest.
        disc_rule_conds.
        eapply xor3_inv_2 with (B:= length (rssQ msgs rsDown) = 1) in H21;
          [dest|eapply rssQ_length_one; eauto].
        red; right.
        exists rqUp, rsDown, pidx; repeat split; try assumption.
        + solve_q.
          apply length_zero_iff_nil; omega.
        + solve_q.
          apply findQ_In_deqMP_FirstMP in H14; simpl in H14.
          unfold rssQ in H20; rewrite <-H14 in H20.
          simpl in H20; rewrite H15 in H20; simpl in H20.
          apply length_zero_iff_nil; omega.
        + apply not_ONoUpLockTo_OUpLockedTo; auto.
    Qed.

    Lemma upLockInvORq_step_int_parent:
      forall oidx,
        UpLockInvORq orqs msgs oidx ((orqs@[oidx]) >>=[[]] (fun orq => orq)) ->
        In oidx (map (@obj_idx _) (sys_objs sys)) ->
        GoodRqRsRule dtr (obj_idx obj) rule ->
        parentIdxOf dtr oidx = Some (obj_idx obj) ->
        UpLockInvORq (orqs+[obj_idx obj <- norq])
                     (enqMsgs mouts (deqMsgs (idsOf mins) msgs)) oidx
                     ((orqs@[ oidx]) >>=[[]] (fun orq => orq)).
    Proof.
      intros.
      destruct Hsd.
      red in H; red.
      good_rqrs_rule_cases rule.

      - (** case [ImmDownRule] *)
        remember (orqs@[oidx] >>=[[]] (fun orq => orq)) as oorq.
        remember (oorq@[upRq]) as orqiu.
        destruct orqiu as [rqiu|].
        + admit.
        + exfalso; admit.

      - (** case [ImmUpRule] *)
        find_if_inside.
        + disc_rule_conds.
          eapply upLockedInv_orqs_preserved with (orqs1:= orqs);
            [|eassumption|mred].
          apply upLockedInv_msgs_preserved with (msgs1:= msgs);
            [assumption| |].
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
        + disc_rule_conds.
          eapply upLockFreeInv_orqs_preserved with (orqs1:= orqs);
            [|eassumption|mred].
          apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
            [assumption| |].
          * destruct H.
            { remember (rqEdgeUpFrom dtr oidx) as orqUp.
              destruct orqUp; auto.
              eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * destruct H.
            { remember (edgeDownTo dtr oidx) as odown.
              destruct odown; auto.
              eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }

      - (** case [RqFwdRule] *)
        admit.

      - (** case [RsBackRule] *)
        admit.

      - (** case [RsDownRqDownRule] *)
        admit.

    Admitted.

    Lemma upLockInvORq_step_int_other:
      forall oidx orq,
        UpLockInvORq orqs msgs oidx orq ->
        In oidx (map (@obj_idx _) (sys_objs sys)) ->
        GoodRqRsRule dtr (obj_idx obj) rule ->
        obj_idx obj <> oidx ->
        parentIdxOf dtr oidx <> Some (obj_idx obj) ->
        UpLockInvORq (orqs+[obj_idx obj <- norq])
                     (enqMsgs mouts (deqMsgs (idsOf mins) msgs)) oidx
                     orq.
    Proof.
      intros.
      destruct Hsd.
      red in H; red.
      good_rqrs_rule_cases rule.

      - (** case [ImmDownRule] *)
        find_if_inside.
        + apply upLockedInv_orqs_preserved_add_parent; auto.
          apply upLockedInv_msgs_preserved with (msgs1:= msgs);
            [assumption| |].
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
        + apply upLockFreeInv_orqs_preserved_add_parent; auto.
          apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
            [assumption| |].
          * destruct H.
            { remember (rqEdgeUpFrom dtr oidx) as orqUp.
              destruct orqUp; auto.
              eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * destruct H.
            { remember (edgeDownTo dtr oidx) as odown.
              destruct odown; auto.
              eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }

      - (** case [ImmUpRule] *)
        find_if_inside.
        + apply upLockedInv_orqs_preserved_add_parent; auto.
          apply upLockedInv_msgs_preserved with (msgs1:= msgs);
            [assumption| |].
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
        + apply upLockFreeInv_orqs_preserved_add_parent; auto.
          apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
            [assumption| |].
          * destruct H.
            { remember (rqEdgeUpFrom dtr oidx) as orqUp.
              destruct orqUp; auto.
              eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * destruct H.
            { remember (edgeDownTo dtr oidx) as odown.
              destruct odown; auto.
              eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
        
      - (** case [RqFwdRule] *)
        disc_rule_conds.

        + find_if_inside.
          * apply upLockedInv_orqs_preserved_add_parent; auto.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * apply upLockFreeInv_orqs_preserved_add_parent; auto.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr oidx) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }

        + find_if_inside.
          * apply upLockedInv_orqs_preserved_add_parent; auto.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * apply upLockFreeInv_orqs_preserved_add_parent; auto.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr oidx) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }

        + find_if_inside.
          * apply upLockedInv_orqs_preserved_add_parent; auto.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * apply upLockFreeInv_orqs_preserved_add_parent; auto.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr oidx) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }

      - (** case [RsBackRule] *)
        good_footprint_get (obj_idx obj).
        disc_rule_conds.

        + rewrite H6 in H8.
          destruct i as [midx msg]; simpl in *.
          find_if_inside.
          * apply upLockedInv_orqs_preserved_add_parent; auto.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * apply upLockFreeInv_orqs_preserved_add_parent; auto.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr oidx) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }

        + rewrite H8 in H15.
          destruct i as [midx msg]; simpl in *.
          find_if_inside.
          * apply upLockedInv_orqs_preserved_add_parent; auto.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * apply upLockFreeInv_orqs_preserved_add_parent; auto.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr oidx) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }

        + rewrite H8 in H14.
          destruct i as [midx msg]; simpl in *.
          find_if_inside.
          * apply upLockedInv_orqs_preserved_add_parent; auto.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * apply upLockFreeInv_orqs_preserved_add_parent; auto.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr oidx) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }

      - (** case [RsDownRqDownRule] *)
        disc_rule_conds.
        find_if_inside.
        + apply upLockedInv_orqs_preserved_add_parent; auto.
          apply upLockedInv_msgs_preserved with (msgs1:= msgs);
            [assumption| |].
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
        + apply upLockFreeInv_orqs_preserved_add_parent; auto.
          apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
            [assumption| |].
          * destruct H.
            { remember (rqEdgeUpFrom dtr oidx) as orqUp.
              destruct orqUp; auto.
              eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * destruct H.
            { remember (edgeDownTo dtr oidx) as odown.
              destruct odown; auto.
              eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
    Qed.
    
    Lemma downLockInvORq_step_int_me:
      DownLockInvORq orqs msgs (obj_idx obj) porq ->
      In (obj_idx obj) (map (@obj_idx _) (sys_objs sys)) ->
      GoodRqRsRule dtr (obj_idx obj) rule ->
      DownLockInvORq (orqs+[obj_idx obj <- norq])
                     (enqMsgs mouts (deqMsgs (idsOf mins) msgs))
                     (obj_idx obj) norq.
    Proof.
    Admitted.

    Lemma downLockInvORq_step_int_other:
      forall oidx,
        DownLockInvORq orqs msgs oidx ((orqs@[oidx]) >>=[[]] (fun orq => orq)) ->
        In oidx (map (@obj_idx _) (sys_objs sys)) ->
        GoodRqRsRule dtr (obj_idx obj) rule ->
        obj_idx obj <> oidx ->
        DownLockInvORq (orqs+[obj_idx obj <- norq])
                     (enqMsgs mouts (deqMsgs (idsOf mins) msgs)) oidx
                     ((orqs@[ oidx]) >>=[[]] (fun orq => orq)).
    Proof.
    Admitted.

    Lemma lockInv_step_int:
      LockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      LockInv {| bst_oss := (oss) +[ obj_idx obj <- nost];
                 bst_orqs := (orqs) +[ obj_idx obj <- norq];
                 bst_msgs := enqMsgs mouts (deqMsgs (idsOf mins) msgs) |}.
    Proof.
      intros.
      do 2 red; simpl; intros.
      good_rqrs_rule_get rule.
      specialize (H _ H0); simpl in H; dest; split.

      - (** Proving invariants about uplocks *)
        M.cmp (obj_idx obj) oidx; mred; simpl in *.
        + (** case [oidx = obj_idx obj] *)
          apply upLockInvORq_step_int_me; assumption.
        + (** case [oidx <> obj_idx obj] *)
          remember (parentIdxOf dtr oidx) as opidx.
          destruct opidx as [pidx|].
          * destruct (eq_nat_dec (obj_idx obj) pidx); subst.
            { apply upLockInvORq_step_int_parent; auto. }
            { apply upLockInvORq_step_int_other; auto.
              rewrite <-Heqopidx.
              intro Hx; elim n0; inv Hx; reflexivity.
            }
          * apply upLockInvORq_step_int_other; auto.
            rewrite <-Heqopidx; discriminate.

      - (** Proving invariants about downlocks *)
        M.cmp (obj_idx obj) oidx; mred; simpl in *.
        + (** case [oidx = obj_idx obj] *)
          apply downLockInvORq_step_int_me; assumption.
        + (** case [oidx <> obj_idx obj] *)
          apply downLockInvORq_step_int_other; assumption.
    Qed.

  End InternalStep.

  Lemma lockInv_step:
    InvStep sys step_m LockInv.
  Proof.
    red; intros.
    inv H1.
    - auto.
    - apply lockInv_step_ext_in; auto.
    - apply lockInv_step_ext_out; auto.
    - eapply lockInv_step_int; eauto.
      eapply footprints_ok; eassumption.
  Qed.

  Lemma lockInv_ok:
    InvReachable sys step_m LockInv.
  Proof.
    apply inv_reachable.
    - apply lockInv_init.
    - apply lockInv_step.
  Qed.
  
End LockInv.

Ltac good_locking_get obj :=
  match goal with
  | [Hlock: LockInv _ ?sys _, Ho: In obj (sys_objs ?sys) |- _] =>
    let H := fresh "H" in
    pose proof Hlock as H;
    specialize (H (obj_idx obj)); simpl in H;
    specialize (H (in_map _ _ _ Ho)); dest
  end.

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

