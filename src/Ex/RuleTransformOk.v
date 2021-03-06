Require Import Bool Vector List String Peano_dec Lia.
Require Import Common FMap HVector IndexSupport Syntax Semantics StepM Invariant Simulation.
Require Import Topology RqRsTopo.
Require Import RqRsLang.

Import PropMonadNotations.

Require Import Ex.Template Ex.RuleTransform.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Section RssHolderOk.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).
  Context `{dv:DecValue} `{oifc: OStateIfc}.

  Local Notation topo := (fst (tree2Topo tr 0)).
  Local Notation cifc := (snd (tree2Topo tr 0)).

  Variables (impl spec: System).

  Hypotheses (Htierq: sys_merqs impl = c_merqs cifc)
             (Htiint: sys_minds impl = c_minds cifc)
             (Htiers: sys_merss impl = c_merss cifc)
             (Hiserq: sys_merqs impl = sys_merqs spec)
             (Hisint: sys_minds impl = sys_minds spec)
             (Hisers: sys_merss impl = sys_merss spec).

  (** Required invariants *)

  Definition RssWf (oidx: IdxT) (rss: list (IdxT * option Msg)) :=
    SubList (map fst rss) (sys_minds impl) /\
    NoDup (map fst rss) /\
    Forall (fun iom =>
              exists cidx,
                parentIdxOf topo cidx = Some oidx /\
                rsUpFrom cidx = fst iom) rss /\
    Forall (fun iom =>
              match snd iom with
              | Some rs => rs.(msg_type) = MRs
              | None => True
              end) rss.

  Definition RssWfORq (oidx: IdxT) (orq: ORq Msg) :=
    orq@[downRq] >>=[True]
       (fun rqid =>
          RssWf oidx rqid.(rqi_rss) /\
          (rqid.(rqi_midx_rsb)
                  >>=[True] (fun rsb =>
                               forall roidx,
                                 roidx <> oidx -> rsb <> rsUpFrom roidx))).

  Definition RssWfInv (st: State) :=
    forall oidx, (st_orqs st)@[oidx] >>=[True] (fun orq => RssWfORq oidx orq).

  Definition UpLockRssORq (oidx: IdxT) (orq: ORq Msg) :=
    orq@[upRq] >>=[True]
       (fun rqiu => exists oidx, map fst rqiu.(rqi_rss) = [downTo oidx]).

  Definition UpLockRssInv (st: State) :=
    forall oidx, (st_orqs st)@[oidx] >>=[True] (fun orq => UpLockRssORq oidx orq).

  (** End of the invariants *)

  Definition RssORqEquiv (orq1 orq2: ORq Msg) :=
    orq1@[upRq] = orq2@[upRq] /\
    (orq1@[downRq] = None -> orq2@[downRq] = None) /\
    (forall rqid1,
        orq1@[downRq] = Some rqid1 ->
        exists rqid2,
          orq2@[downRq] = Some rqid2 /\
          rqid1.(rqi_msg) = rqid2.(rqi_msg) /\
          map fst rqid1.(rqi_rss) = map fst rqid2.(rqi_rss) /\
          rqid1.(rqi_midx_rsb) = rqid2.(rqi_midx_rsb)).

  Definition NoRsUpInputs (mins: list (Id Msg)) :=
    forall idm,
      In idm mins ->
      (exists oidx, idOf idm = rqUpFrom oidx \/ idOf idm = downTo oidx).

  Definition RssEquivPrec (prec: OPrec) :=
    forall ost orq1 mins,
      prec ost orq1 mins ->
      (NoRsUpInputs mins \/ MsgsFromORq upRq ost orq1 mins) /\
      (forall orq2, RssORqEquiv orq1 orq2 -> prec ost orq2 mins).

  Definition UpLockDownTo (orq1 orq2: ORq Msg) :=
    match orq2@[upRq] with
    | Some rqiu2 =>
      match orq1@[upRq] with
      | Some rqiu1 => rqiu1 = rqiu2
      | None => exists oidx, map fst rqiu2.(rqi_rss) = [downTo oidx]
      end
    | None => True
    end.

  Definition NoRssChange (orq1 orq2: ORq Msg) :=
    match orq1@[downRq], orq2@[downRq] with
    | Some rqid1, Some rqid2 => rqid1.(rqi_rss) = rqid2.(rqi_rss)
    | Some rqid1, None => Forall (fun rs => snd rs = None) rqid1.(rqi_rss)
    | None, Some rqid2 => Forall (fun rs => snd rs = None) rqid2.(rqi_rss)
    | None, None => True
    end.

  Definition RssEquivTrs (prec: OPrec) (trs: OTrs) :=
    forall ost orq1 mins nost norq1 mouts,
      prec ost orq1 mins ->
      trs ost orq1 mins = (nost, norq1, mouts) ->
      UpLockDownTo orq1 norq1 /\
      NoRssChange orq1 norq1 /\
      (forall orq2,
          RssORqEquiv orq1 orq2 ->
          exists norq2,
            trs ost orq2 mins = (nost, norq2, mouts) /\
            RssORqEquiv norq1 norq2).

  Definition RssEquivRule (rule: Rule) :=
    RssEquivPrec (rule_precond rule) /\
    RssEquivTrs (rule_precond rule) (rule_trs rule).

  Definition ImplRulesR (oidx: IdxT) (irules srules: list Rule) :=
    forall rule,
      In rule irules ->
      (RssEquivRule rule /\ In rule srules) \/
      (exists ridx msgId rqId prec trs,
          rule = rsRelease ridx~>1 msgId rqId prec trs /\
          In (rsUpRule ridx msgId rqId prec trs) srules) \/
      (exists ridx msgId rqId prec trs,
          rule = rsReleaseOne ridx~>1 msgId rqId prec trs /\
          In (rsUpRuleOne ridx msgId rqId prec trs) srules) \/
      (exists ridx msgId rqId cidx,
          parentIdxOf topo cidx = Some oidx /\
          rule = rsTakeOne ridx msgId rqId cidx).

  Definition ImplRules :=
    forall iobj,
      In iobj impl.(sys_objs) ->
      exists sobj,
        In sobj spec.(sys_objs) /\
        iobj.(obj_idx) = sobj.(obj_idx) /\
        ImplRulesR iobj.(obj_idx) iobj.(obj_rules) sobj.(obj_rules).

  Hypotheses (Hir: ImplRules).

  Definition implORqsInit: ORqs Msg :=
    initORqs (cifc.(c_li_indices) ++ cifc.(c_l1_indices)).

  Hypotheses (Hsi: impl.(sys_oss_inits) = spec.(sys_oss_inits))
             (Hoii: impl.(sys_orqs_inits) = implORqsInit)
             (Hosi: spec.(sys_orqs_inits) = implORqsInit).

  Section UpLockRssInv.

    Lemma UpLockRssInv_init: InvInit impl UpLockRssInv.
    Proof.
      repeat red; intros.
      simpl; rewrite Hoii.
      unfold implORqsInit; intros.
      destruct (in_dec idx_dec oidx (c_li_indices cifc ++ c_l1_indices cifc)).
      - rewrite initORqs_value by assumption; red; mred.
      - rewrite initORqs_None by assumption; auto.
    Qed.

    Lemma UpLockRssInv_step: InvStep impl step_m UpLockRssInv.
    Proof.
      red; intros.
      inv H1; [assumption..|].

      red in H0; simpl in H0.
      red; simpl; intros.
      mred; simpl; [|auto].
      specialize (H0 (obj_idx obj)).
      rewrite H6 in H0; simpl in H0.

      move Hir at bottom.
      pose proof (Hir _ H2) as [sobj [HsoIn [Hoi Hrr]]].
      specialize (Hrr _ H3).
      destruct Hrr as [|[|[|]]].

      - (*! Normal rules *)
        dest; red in H1; dest.
        specialize (H13 _ _ _ _ _ _ H9 H10); dest.
        red in H13; red in H0; red.
        destruct (norq@[upRq]) as [nrqiu|]; simpl in *; [|auto].
        destruct (porq@[upRq]) as [prqiu|]; simpl in *.
        + subst; assumption.
        + assumption.

      - (*! [RsRelease] *)
        destruct H1 as [ridx [msgId [rqId [prec [trs [? ?]]]]]]; subst rule.
        disc_rule_conds_ex.
        red; mred.

      - (*! [RsReleaseOne] *)
        destruct H1 as [ridx [msgId [rqId [prec [trs [? ?]]]]]]; subst rule.
        disc_rule_conds_ex.
        red; mred.

      - (*! [RsTakeOne] *)
        destruct H1 as [ridx [msgId [rqId [cidx [? ?]]]]]; subst rule.
        disc_rule_conds_ex.
        red; unfold addRs; mred.
        simpl; mred.
    Qed.

  End UpLockRssInv.

  Section RssWfImp.
    Hypothesis (Hgss: GoodRqRsSys topo spec)
               (Hers: GoodExtRssSys spec).

    Lemma RssWfInv_init: InvInit impl RssWfInv.
    Proof.
      repeat red; intros.
      simpl; rewrite Hoii.
      unfold implORqsInit; intros.
      destruct (in_dec idx_dec oidx (c_li_indices cifc ++ c_l1_indices cifc)).
      - rewrite initORqs_value by assumption; red; mred.
      - rewrite initORqs_None by assumption; auto.
    Qed.

    Lemma putRs_In_index:
      forall rmidx ors nrmidx nors rss,
        In (rmidx, ors) (putRs nrmidx nors rss) ->
        exists ors', In (rmidx, ors') rss.
    Proof.
      induction rss as [|[irmidx rs] rss]; simpl; intros; [exfalso; auto|].
      destruct (idx_dec nrmidx irmidx); subst.
      - inv H; eauto.
        inv H0; eauto.
      - inv H; eauto.
        specialize (IHrss H0); dest; eauto.
    Qed.

    Lemma RssWf_putRs:
      forall oidx rss,
        RssWf oidx rss ->
        forall cidx,
          parentIdxOf topo cidx = Some oidx ->
          forall rmsg,
            msg_type rmsg = MRs ->
            RssWf oidx (putRs (rsUpFrom cidx) rmsg rss).
    Proof.
      unfold RssWf; intros; dest.
      assert (map fst (putRs (rsUpFrom cidx) rmsg rss) = map fst rss) as Heq.
      { clear.
        induction rss as [|[rmidx rs] rss]; simpl in *; [reflexivity|].
        destruct (idx_dec (rsUpFrom cidx) rmidx); subst; simpl in *; [reflexivity|].
        congruence.
      }
      rewrite Heq.

      repeat split; try assumption.
      - rewrite Forall_forall in H3.
        apply Forall_forall; intros [rmidx ors] ?.
        apply putRs_In_index in H5; destruct H5 as [oors ?].
        specialize (H3 _ H5); eauto.
      - rewrite Forall_forall in H4.
        apply Forall_forall; intros [rmidx ors] ?; simpl.
        clear -H1 H4 H5.
        induction rss as [|[irmidx rs] rss]; simpl in *; [exfalso; auto|].
        destruct (idx_dec (rsUpFrom cidx) irmidx); subst.
        + inv H5.
          * inv H; assumption.
          * specialize (H4 (rmidx, ors)); simpl in H4.
            apply H4; auto.
        + inv H5.
          * inv H.
            specialize (H4 (rmidx, ors)); simpl in H4.
            apply H4; auto.
          * apply IHrss; auto.
            intros; apply H4; auto.
    Qed.

    Lemma RssWfORq_addRs:
      forall oidx porq,
        RssWfORq oidx porq ->
        forall cidx,
          parentIdxOf topo cidx = Some oidx ->
          forall rmsg,
            msg_type rmsg = MRs ->
            RssWfORq oidx (addRs porq (rsUpFrom cidx) rmsg).
    Proof.
      intros.
      red in H.
      red; unfold addRs.
      destruct porq@[downRq] as [rqid|] eqn:Hrqid; simpl;
        [|rewrite Hrqid; simpl; auto].
      mred; simpl in *; dest.
      split; [|assumption].
      apply RssWf_putRs; auto.
    Qed.

    Lemma rqDown_not_in_merss:
      forall rqs,
        ValidMsgsOut impl rqs ->
        Forall (fun idm => msg_type (valOf idm) = MRq) rqs ->
        (forall mout, In mout rqs ->
                      In (idOf mout) (sys_merss impl) ->
                      msg_type (valOf mout) = MRs) ->
        SubList (idsOf rqs) (sys_minds impl).
    Proof.
      intros; destruct H.
      red; intros midx ?.
      pose proof (H _ H3).
      apply in_map_iff in H3; destruct H3 as [[rmidx rq] ?]; dest; simpl in *; subst.
      rewrite Forall_forall in H0; specialize (H0 _ H5).
      specialize (H1 _ H5); simpl in *.
      apply in_app_or in H4; destruct H4; [assumption|].
      specialize (H1 H3).
      rewrite H0 in H1; discriminate.
    Qed.

    Lemma RqRsDownMatch_RssWf_SubList:
      forall oidx rqTos rssFrom P,
        SubList rqTos (sys_minds impl) ->
        RqRsDownMatch topo oidx rqTos rssFrom P ->
        SubList (map fst rssFrom) (sys_minds impl).
    Proof.
      intros.
      red; intros rsFrom ?.
      eapply RqRsDownMatch_rs_rq in H0; [|eassumption].
      destruct H0 as [cidx [down ?]]; dest.
      rewrite Htiint; rewrite Htiint in H.
      apply H in H5.
      apply tree2Topo_down_obj in H3; [|assumption].
      apply tree2Topo_obj_chns_minds_SubList in H3.
      apply rsEdgeUpFrom_rsUpFrom in H4; subst.
      apply H3; simpl; tauto.
    Qed.

    Lemma combine_nth_fst:
      forall {A} (l1: list A) {B} (l2: list B),
        List.length l1 = List.length l2 ->
        forall i d,
          fst (nth i (combine l1 l2) d) = nth i l1 (fst d).
    Proof.
      induction l1; simpl; intros; [destruct i; reflexivity|].
      destruct l2 as [|b l2]; [discriminate|].
      simpl in *.
      destruct i; [reflexivity|auto].
    Qed.

    Lemma combine_nth_snd:
      forall {A} (l1: list A) {B} (l2: list B),
        List.length l1 = List.length l2 ->
        forall i d,
          snd (nth i (combine l1 l2) d) = nth i l2 (snd d).
    Proof.
      induction l1; simpl; intros.
      - destruct l2; [|discriminate].
        simpl; destruct i; reflexivity.
      - destruct l2 as [|b l2]; [discriminate|].
        simpl in *.
        destruct i; [reflexivity|auto].
    Qed.

    Lemma RqRsDownMatch_RssWf_NoDup:
      forall oidx rqTos rssFrom P,
        NoDup rqTos ->
        RqRsDownMatch topo oidx rqTos rssFrom P ->
        NoDup (map fst rssFrom).
    Proof.
      unfold RqRsDownMatch; intros; dest.
      rewrite NoDup_nth_error in H.
      apply NoDup_nth_error; intros.

      assert (j < List.length (map fst rssFrom)).
      { destruct (Compare_dec.le_lt_dec (List.length (map fst rssFrom)) j); [|assumption].
        apply nth_error_None in l.
        rewrite l in H4.
        apply nth_error_None in H4.
        lia.
      }

      rewrite map_length in H3, H5.
      rewrite Forall_nth in H2.
      rewrite combine_length, H1, PeanoNat.Nat.min_id in H2.
      pose proof (H2 _ (ii, (ii, None)) H3); destruct H6 as [icidx ?].
      pose proof (H2 _ (ii, (ii, None)) H5); destruct H7 as [jcidx ?].
      dest.
      rewrite combine_nth_fst in H9, H13 by assumption.
      rewrite combine_nth_snd in H10, H11, H14, H15 by assumption.
      simpl in *.

      rewrite <-map_length with (f:= fst) in H3, H5.
      destruct (nth_error (map fst rssFrom) i) as [irsf|] eqn:Hirsf;
        [|exfalso; apply nth_error_None in Hirsf; lia].
      apply nth_error_nth with (d:= ii) in Hirsf.
      change ii with (fst (ii, (@None Msg))) in Hirsf; rewrite map_nth in Hirsf.
      rewrite Hirsf in H15.
      apply eq_sym, nth_error_nth with (d:= ii) in H4.
      change ii with (fst (ii, (@None Msg))) in H4; rewrite map_nth in H4.
      rewrite H4 in H11.

      assert (icidx = jcidx); subst.
      { apply rsEdgeUpFrom_rsUpFrom in H15.
        apply rsEdgeUpFrom_rsUpFrom in H11.
        rewrite H15 in H11.
        inv H11; reflexivity.
      }

      apply H; [rewrite H1; rewrite map_length in H3; assumption|].
      rewrite nth_error_nth' with (d:= ii)
        by (rewrite H1; rewrite map_length in H3; assumption).
      rewrite nth_error_nth' with (d:= ii)
        by (rewrite H1; rewrite map_length in H5; assumption).
      congruence.
    Qed.

    Lemma RqRsDownMatch_RssWf_child_None:
      forall oidx rqTos rssFrom P,
        RqRsDownMatch topo oidx rqTos rssFrom P ->
        Forall (fun iom =>
                  exists cidx,
                    parentIdxOf topo cidx = Some oidx /\
                    rsUpFrom cidx = fst iom) rssFrom /\
        Forall (fun iom =>
                  match snd iom with
                  | Some rs => msg_type rs = MRs
                  | None => True
                  end) rssFrom.
    Proof.
      unfold RqRsDownMatch; intros; dest.
      clear -H0 H1; split.
      - apply Forall_forall.
        intros [rmidx ors] ?.
        eapply In_nth with (d:= (ii, None)) in H.
        destruct H as [n [? ?]].
        rewrite Forall_nth in H1.
        rewrite combine_length, H0, PeanoNat.Nat.min_id in H1.
        specialize (H1 _ (ii, (ii, None)) H); destruct H1 as [cidx ?]; dest.
        rewrite combine_nth_snd in H6 by assumption.
        simpl in *; rewrite H2 in H6; simpl in *.
        exists cidx; split; [assumption|].
        apply rsEdgeUpFrom_rsUpFrom in H6; auto.
      - apply Forall_forall.
        intros [rmidx ors] ?.
        eapply In_nth with (d:= (ii, None)) in H.
        destruct H as [n [? ?]].
        rewrite Forall_nth in H1.
        rewrite combine_length, H0, PeanoNat.Nat.min_id in H1.
        specialize (H1 _ (ii, (ii, None)) H); destruct H1 as [cidx ?]; dest.
        rewrite combine_nth_snd in H5 by assumption.
        simpl in *; rewrite H2 in H5; simpl in *.
        subst; auto.
    Qed.

    Lemma RssWfORq_downRq_equiv:
      forall oidx orq1,
        RssWfORq oidx orq1 ->
        forall orq2,
          orq1@[downRq] = orq2@[downRq] ->
          RssWfORq oidx orq2.
    Proof.
      unfold RssWfORq; intros; rewrite <-H0; assumption.
    Qed.

    Lemma RssWfInv_step: InvStep impl step_m RssWfInv.
    Proof.
      red; intros.
      inv H1; [assumption..|].

      red in H0; simpl in H0.
      red; simpl; intros.
      mred; simpl; [|auto].
      specialize (H0 (obj_idx obj)).
      rewrite H6 in H0; simpl in H0.

      move Hir at bottom.
      pose proof (Hir _ H2) as [sobj [HsoIn [Hoi Hrr]]].
      specialize (Hrr _ H3).
      destruct Hrr as [|[|[|]]].

      - (*! Normal rules *)
        dest.
        good_rqrs_rule_get rule.
        good_rqrs_rule_cases rule.
        1-2: try (disc_rule_conds; fail).

        + (** [RqFwdRule] *)
          disc_rule_conds.
          * eapply RssWfORq_downRq_equiv; [eassumption|]; findeq.
          * eapply RssWfORq_downRq_equiv; [eassumption|]; findeq.
          * pose proof Hers as Her.
            red in Her; rewrite Forall_forall in Her; specialize (Her _ HsoIn).
            red in Her; rewrite Forall_forall in Her; specialize (Her _ H4).
            red in Her; specialize (Her _ _ _ _ _ _ H9 H10).
            red; mred; simpl; split; [|rewrite H38; simpl; auto].
            red in H35; red.
            repeat split.
            { eapply RqRsDownMatch_RssWf_SubList; eauto.
              eapply rqDown_not_in_merss; auto.
              rewrite Hisers; assumption.
            }
            { eapply RqRsDownMatch_RssWf_NoDup; [apply H11|eassumption]. }
            { eapply RqRsDownMatch_RssWf_child_None; rewrite Hoi; eassumption. }
            { eapply RqRsDownMatch_RssWf_child_None; eassumption. }

          * pose proof Hers as Her.
            red in Her; rewrite Forall_forall in Her; specialize (Her _ HsoIn).
            red in Her; rewrite Forall_forall in Her; specialize (Her _ H4).
            red in Her; specialize (Her _ _ _ _ _ _ H9 H10).
            red in H35; destruct H35 as [upCIdx [upCObj ?]]; dest.
            red; mred; simpl; split.
            { repeat split.
              { eapply RqRsDownMatch_RssWf_SubList; eauto.
                eapply rqDown_not_in_merss; auto.
                rewrite Hisers; assumption.
              }
              { eapply RqRsDownMatch_RssWf_NoDup; [apply H11|eassumption]. }
              { eapply RqRsDownMatch_RssWf_child_None; rewrite Hoi; eassumption. }
              { eapply RqRsDownMatch_RssWf_child_None; eassumption. }
            }
            { rewrite H38; simpl.
              apply edgeDownTo_downTo in H20; subst.
              intros; discriminate.
            }

          * pose proof Hers as Her.
            red in Her; rewrite Forall_forall in Her; specialize (Her _ HsoIn).
            red in Her; rewrite Forall_forall in Her; specialize (Her _ H4).
            red in Her; specialize (Her _ _ _ _ _ _ H9 H10).
            red in H33; dest.
            red; mred; simpl; split.
            { repeat split.
              { eapply RqRsDownMatch_RssWf_SubList; eauto.
                eapply rqDown_not_in_merss; auto.
                rewrite Hisers; assumption.
              }
              { eapply RqRsDownMatch_RssWf_NoDup; [apply H11|eassumption]. }
              { eapply RqRsDownMatch_RssWf_child_None; rewrite Hoi; eassumption. }
              { eapply RqRsDownMatch_RssWf_child_None; eassumption. }
            }
            { rewrite H38; simpl.
              apply rsEdgeUpFrom_rsUpFrom in H13; subst.
              intros; intro Hx; elim H7; inv Hx; auto.
            }

        + (** [RsBackRule] *)
          disc_rule_conds.
          * eapply RssWfORq_downRq_equiv; [eassumption|]; findeq.
          * eapply RssWfORq_downRq_equiv; [eassumption|]; findeq.
          * red; mred.
          * red; mred.

        + (** [RsDownRqDownRule] *)
          disc_rule_conds.
          pose proof Hers as Her.
          red in Her; rewrite Forall_forall in Her; specialize (Her _ HsoIn).
          red in Her; rewrite Forall_forall in Her; specialize (Her _ H4).
          red in Her; specialize (Her _ _ _ _ _ _ H9 H10).
          red in H21; destruct H21 as [upCIdx [upCObj ?]]; dest.
          red; mred; simpl; split.
          { repeat split.
            { eapply RqRsDownMatch_RssWf_SubList; eauto.
              eapply rqDown_not_in_merss; auto.
              rewrite Hisers; assumption.
            }
            { eapply RqRsDownMatch_RssWf_NoDup; [apply H11|eassumption]. }
            { eapply RqRsDownMatch_RssWf_child_None; rewrite Hoi; eassumption. }
            { eapply RqRsDownMatch_RssWf_child_None; eassumption. }
          }
          { rewrite H32; simpl.
            apply edgeDownTo_downTo in H19; subst.
            intros; discriminate.
          }

      - (*! [RsRelease] *)
        destruct H1 as [ridx [msgId [rqId [prec [trs [? ?]]]]]]; subst rule.
        disc_rule_conds_ex.
        red; mred.

      - (*! [RsReleaseOne] *)
        destruct H1 as [ridx [msgId [rqId [prec [trs [? ?]]]]]]; subst rule.
        disc_rule_conds_ex.
        red; mred.

      - (*! [RsTakeOne] *)
        destruct H1 as [ridx [msgId [rqId [cidx [? ?]]]]]; subst rule.
        disc_rule_conds_ex.
        apply RssWfORq_addRs; auto.
    Qed.

    Lemma good_rqrs_sys_implies_RssWf:
      InvReachable impl step_m RssWfInv.
    Proof.
      eapply inv_reachable.
      - typeclasses eauto.
      - apply RssWfInv_init.
      - apply RssWfInv_step.
    Qed.

  End RssWfImp.

  Section SimRssMP.

    Fixpoint findRs (midx: IdxT) (rss: list (IdxT * option Msg)): option Msg :=
      match rss with
      | nil => None
      | (rmidx, rmsg) :: rss' =>
        if idx_dec rmidx midx then rmsg else findRs midx rss'
      end.

    Definition SimRssMP (iorqs: ORqs Msg)
               (imsgs: MessagePool Msg) (smsgs: MessagePool Msg) :=
      forall midx,
        (forall oidx,
            midx = rqUpFrom oidx ->
            (* rqEdgeUpFrom topo oidx = Some midx -> *)
            findQ midx imsgs = findQ midx smsgs) /\
        (forall oidx,
            midx = downTo oidx ->
            (* edgeDownTo topo oidx = Some midx -> *)
            findQ midx imsgs = findQ midx smsgs) /\
        (forall oidx,
            midx = rsUpFrom oidx ->
            (* rsEdgeUpFrom topo oidx = Some midx -> *)
            forall pidx,
              In pidx (c_li_indices cifc ++ c_l1_indices cifc) ->
              parentIdxOf topo oidx = Some pidx ->
              ((iorqs@[pidx])
                 >>= (fun porq =>
                        porq@[downRq]
                            >>= (fun rqid =>
                                   findRs midx (rqi_rss rqid))))
                ::> (findQ midx imsgs) = findQ midx smsgs).

  End SimRssMP.

  Section SimRssORqs.

    Definition SimRssORqs (orqs1 orqs2: ORqs Msg) :=
      Forall
        (fun oidx =>
           (forall orq1,
               orqs1@[oidx] = Some orq1 ->
               exists orq2,
                 orqs2@[oidx] = Some orq2 /\
                 RssORqEquiv orq1 orq2))
        (c_li_indices cifc ++ c_l1_indices cifc).

  End SimRssORqs.

  Local Definition sim (ist: State) (sst: State): Prop :=
    st_oss ist = st_oss sst /\
    SimRssORqs (st_orqs ist) (st_orqs sst) /\
    SimRssMP (st_orqs ist) (st_msgs ist) (st_msgs sst).

  Lemma rss_holder_rss_sim_init: sim (initsOf impl) (initsOf spec).
  Proof.
    red; repeat ssplit.
    - assumption.
    - red; apply Forall_forall; intros oidx ?.
      simpl; rewrite Hoii, Hosi.
      unfold implORqsInit; intros.
      rewrite initORqs_value in H0 by assumption.
      inv H0.
      exists [].
      rewrite initORqs_value by assumption.
      repeat split.
      mred.
    - red; simpl; intros; repeat split.
      simpl; rewrite Hoii; intros.
      unfold implORqsInit; rewrite initORqs_value by assumption.
      simpl; mred.
  Qed.

  Lemma rss_holder_rss_sim_silent:
    forall ist sst1,
      sim ist sst1 ->
      exists slbl sst2,
        getLabel RlblEmpty = getLabel slbl /\
        step_m spec sst1 slbl sst2 /\ sim ist sst2.
  Proof.
    simpl; intros.
    exists RlblEmpty; eexists.
    repeat ssplit; eauto.
    constructor.
  Qed.

  Hypotheses (Hierqs: impl.(sys_merqs) = cifc.(c_merqs))
             (Hserqs: spec.(sys_merqs) = cifc.(c_merqs))
             (Hierss: impl.(sys_merss) = cifc.(c_merss))
             (Hserss: spec.(sys_merss) = cifc.(c_merss))
             (Himinds: impl.(sys_minds) = cifc.(c_minds))
             (Hsminds: spec.(sys_minds) = cifc.(c_minds))
             (Hoinds: map obj_idx (sys_objs impl) =
                      c_li_indices cifc ++ c_l1_indices cifc).

  Lemma findQ_enqMsgs_eq:
    forall midx (msgs1 msgs2: MessagePool Msg),
      findQ midx msgs1 = findQ midx msgs2 ->
      forall nmsgs,
        findQ midx (enqMsgs nmsgs msgs1) = findQ midx (enqMsgs nmsgs msgs2).
  Proof.
    intros.
    generalize dependent msgs1.
    generalize dependent msgs2.
    induction nmsgs as [|[nmidx nmsg] ?]; simpl; intros; [assumption|].
    apply IHnmsgs.
    destruct (idx_dec midx nmidx); subst.
    - rewrite !findQ_In_enqMP; congruence.
    - rewrite !findQ_not_In_enqMP by assumption; assumption.
  Qed.

  Lemma rsUpFrom_not_In_c_merqs:
    forall oidx, ~ In (rsUpFrom oidx) (c_merqs cifc).
  Proof.
    intros.
    unfold implORqsInit in *.
    rewrite c_merqs_l1_rqUpFrom.
    intro Hx.
    apply in_map_iff in Hx; dest.
    discriminate.
  Qed.

  Lemma rsUpFrom_not_In_c_merss:
    forall oidx, ~ In (rsUpFrom oidx) (c_merss cifc).
  Proof.
    intros.
    unfold implORqsInit in *.
    rewrite c_merss_l1_downTo.
    intro Hx.
    apply in_map_iff in Hx; dest.
    discriminate.
  Qed.

  Lemma SimRssMP_enqMsgs:
    forall iorqs imsgs smsgs,
      SimRssMP iorqs imsgs smsgs ->
      forall nmsgs,
        SimRssMP iorqs (enqMsgs nmsgs imsgs) (enqMsgs nmsgs smsgs).
  Proof.
    unfold SimRssMP; intros.
    specialize (H midx); dest.
    repeat split; intros.
    - specialize (H _ H2); apply findQ_enqMsgs_eq; auto.
    - specialize (H0 _ H2); apply findQ_enqMsgs_eq; auto.
    - specialize (H1 _ H2 _ H3 H4).
      destruct iorqs@[pidx] as [porq|]; simpl in *;
        [destruct porq@[downRq] as [rqid|]; simpl in *|].
      2-3: apply findQ_enqMsgs_eq; assumption.
      clear -H1.
      generalize dependent imsgs.
      generalize dependent smsgs.
      induction nmsgs as [|[nmidx nmsg] nmsgs]; simpl; intros; [assumption|].
      apply IHnmsgs.
      destruct (idx_dec midx nmidx); subst.
      + rewrite !findQ_In_enqMP.
        destruct (findRs _ _); simpl in *.
        * rewrite app_comm_cons; congruence.
        * congruence.
      + rewrite !findQ_not_In_enqMP by assumption.
        assumption.
  Qed.

  Lemma SimRssMP_enqMP:
    forall iorqs imsgs smsgs,
      SimRssMP iorqs imsgs smsgs ->
      forall midx msg,
        SimRssMP iorqs (enqMP midx msg imsgs) (enqMP midx msg smsgs).
  Proof.
    intros.
    eapply SimRssMP_enqMsgs with (nmsgs := [(_, _)]) in H.
    simpl in H; eassumption.
  Qed.

  Lemma SimRssMP_deqMsgs:
    forall iorqs imsgs smsgs,
      SimRssMP iorqs imsgs smsgs ->
      forall rmsgs,
        NoRsUpInputs rmsgs ->
        SimRssMP iorqs (deqMsgs (idsOf rmsgs) imsgs) (deqMsgs (idsOf rmsgs) smsgs).
  Proof.
    red; intros.
    specialize (H midx); dest.
    repeat split.
    + intros; specialize (H _ H3).
      apply findQ_deqMsgs_eq; assumption.
    + intros; specialize (H1 _ H3).
      apply findQ_deqMsgs_eq; assumption.
    + intros; specialize (H2 _ H3 _ H4 H5).
      destruct iorqs@[pidx] as [porq|]; simpl in *;
        [destruct porq@[downRq] as [rqid|]; simpl in *|].
      2-3: apply findQ_deqMsgs_eq; assumption.
      rewrite !findQ_not_In_deqMsgs
        by (intro Hx; subst;
            apply in_map_iff with (f:= idOf) in Hx; dest;
            specialize (H0 _ H6); dest;
            destruct H0; rewrite H0 in H3; discriminate).
      assumption.
  Qed.

  Lemma SimRssMP_NoRsUpInputs_first:
    forall mins,
      NoRsUpInputs mins ->
      forall imsgs,
        Forall (FirstMPI imsgs) mins ->
        forall iorqs smsgs,
          SimRssMP iorqs imsgs smsgs ->
          Forall (FirstMPI smsgs) mins.
  Proof.
    intros.
    rewrite Forall_forall in H0.
    apply Forall_forall; intros [midx msg] ?.
    specialize (H0 _ H2).
    eapply findQ_eq_FirstMPI; [eassumption|].
    specialize (H1 midx); dest.
    specialize (H _ H2); simpl in H.
    destruct H as [oidx [|]]; subst; eauto.
  Qed.

  Lemma findRs_rss_None:
    forall rss,
      Forall (fun rs => snd rs = None) rss ->
      forall midx, findRs midx rss = None.
  Proof.
    induction rss as [|[rmidx rs] rss]; simpl; intros; [reflexivity|].
    inv H; simpl in *; subst.
    destruct (idx_dec rmidx midx); auto.
  Qed.

  Lemma findRs_rs:
    forall rss,
      NoDup (map fst rss) ->
      forall nmidx ors,
        In (nmidx, ors) rss ->
        findRs nmidx rss = ors.
  Proof.
    induction rss as [|[rmidx rs]]; simpl; intros; [exfalso; auto|].
    destruct H0.
    - inv H0; destruct (idx_dec nmidx nmidx); [reflexivity|exfalso; auto].
    - destruct (idx_dec rmidx nmidx); subst.
      + exfalso.
        inv H; apply in_map with (f:= fst) in H0; auto.
      + inv H; auto.
  Qed.

  Lemma SimRssMP_ORqs_change_silent:
    forall iorqs imsgs smsgs,
      SimRssMP iorqs imsgs smsgs ->
      forall oidx porq,
        iorqs@[oidx] = Some porq ->
        forall norq,
          NoRssChange porq norq ->
          SimRssMP iorqs+[oidx <- norq] imsgs smsgs.
  Proof.
    unfold SimRssMP; intros.
    specialize (H midx); dest.
    repeat split.
    - intros; specialize (H _ H4); assumption.
    - intros; specialize (H2 _ H4); assumption.
    - intros; specialize (H3 _ H4 _ H5 H6).
      mred; simpl in *.
      red in H1.
      destruct porq@[downRq] as [prqid|];
        destruct norq@[downRq] as [nrqid|]; simpl in *.
      + congruence.
      + rewrite findRs_rss_None in H3 by assumption.
        assumption.
      + rewrite findRs_rss_None by assumption.
        assumption.
      + assumption.
  Qed.

  Lemma rss_holder_rss_sim_ext_in:
    forall oss orqs msgs sst1,
      sim {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} sst1 ->
      forall eins,
        eins <> nil -> ValidMsgsExtIn impl eins ->
        exists slbl sst2,
          getLabel (RlblIns eins) = getLabel slbl /\
          step_m spec sst1 slbl sst2 /\
          sim {| st_oss := oss;
                 st_orqs := orqs;
                 st_msgs := enqMsgs eins msgs |} sst2.
  Proof.
    destruct sst1 as [soss1 sorqs1 smsgs1]; simpl; intros.
    red in H; simpl in *; dest; subst.
    exists (RlblIns eins); eexists.
    repeat ssplit.
    - reflexivity.
    - eapply SmIns; eauto.
      red in H1; red; congruence.
    - red; repeat ssplit; simpl; [reflexivity|assumption|].
      apply SimRssMP_enqMsgs; assumption.
  Qed.

  Lemma rss_holder_rss_sim_ext_out:
    forall oss orqs msgs sst1,
      sim {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} sst1 ->
      forall eouts: list (Id Msg),
        eouts <> nil ->
        Forall (FirstMPI msgs) eouts ->
        ValidMsgsExtOut impl eouts ->
        exists slbl sst2,
          getLabel (RlblOuts eouts) = getLabel slbl /\
          step_m spec sst1 slbl sst2 /\
          sim {| st_oss := oss;
                 st_orqs := orqs;
                 st_msgs := deqMsgs (idsOf eouts) msgs |} sst2.
  Proof.
    destruct sst1 as [soss1 sorqs1 smsgs1]; simpl; intros.
    red in H; simpl in *; dest; subst.
    assert (NoRsUpInputs eouts) as Hnrs.
    { red; intros.
      apply in_map with (f:= idOf) in H; apply H2 in H; simpl in H.
      rewrite Hierss in H.
      rewrite c_merss_l1_downTo in H.
      apply in_map_iff in H; dest; subst.
      eauto.
    }
    exists (RlblOuts eouts); eexists.
    repeat ssplit.
    - reflexivity.
    - eapply SmOuts with (msgs0:= smsgs1); eauto.
      + eapply SimRssMP_NoRsUpInputs_first; try eassumption.
      + destruct H2.
        split; [|assumption].
        rewrite Hierss in H.
        rewrite Hserss.
        assumption.
    - red; repeat ssplit; simpl; [reflexivity|assumption|].
      apply SimRssMP_deqMsgs; assumption.
  Qed.

  Lemma SimRssORqs_next_ord:
    forall orqs1 orqs2,
      SimRssORqs orqs1 orqs2 ->
      forall orq1 orq2,
        RssORqEquiv orq1 orq2 ->
        forall oidx,
          SimRssORqs (orqs1 +[oidx <- orq1]) (orqs2 +[oidx <- orq2]).
  Proof.
    unfold SimRssORqs; intros.
    apply Forall_forall; intros.
    rewrite Forall_forall in H.
    specialize (H _ H1).
    destruct (idx_dec oidx x); subst.
    all: mred; eauto.
  Qed.

  Lemma RssFullWithId_spec:
    forall oidx orq,
      RssWfORq oidx orq ->
      forall msgId ost mins,
        RssFullWithId msgId ost orq mins ->
        exists rqid,
          orq@[downRq] = Some rqid /\
          exists rss,
            rqid.(rqi_rss) = map (fun idm => (idOf idm, Some (valOf idm))) rss /\
            Forall (fun idm => msg_id (valOf idm) = msgId) rss /\
            ValidMsgsIn impl rss /\
            rss = getRss orq.
  Proof.
    unfold RssFullWithId, getRss; intros.
    red in H.
    destruct orq@[downRq] as [rqid|]; simpl in *; [dest|exfalso; auto].
    clear H1; red in H; dest.
    exists rqid; repeat split.
    clear -H H0 H1 H2; induction (rqi_rss rqid) as [|[rmidx rs] rss].
    - exists nil; repeat split; [constructor|apply SubList_nil|constructor].
    - simpl in *.
      apply SubList_cons_inv in H; dest.
      inv H0; inv H1; inv H2.
      simpl in *; destruct rs as [rs|]; [|exfalso; auto].
      specialize (IHrss H3 H8 H9 H7).
      destruct IHrss as [prss [? [? [? ?]]]]; subst.
      eexists ((rmidx, rs) :: _); simpl.
      repeat split.
      + constructor; [reflexivity|assumption].
      + simpl; apply SubList_cons; [|apply H2].
        apply in_or_app; left; auto.
      + red; simpl; constructor.
        * clear -H5; intro Hx; elim H5; clear H5.
          induction prss as [|[prmidx prs]]; simpl; intros; [elim Hx|].
          simpl in Hx; destruct Hx; subst; auto.
        * apply H2.
      + congruence.
  Qed.

  Lemma RssFullOne_spec:
    forall oidx orq,
      RssWfORq oidx orq ->
      forall msgId ost mins,
        RssFullOne msgId ost orq mins ->
        exists rqid,
          orq@[downRq] = Some rqid /\
          exists rs,
            rqid.(rqi_rss) = [(idOf rs, Some (valOf rs))] /\
            msg_id (valOf rs) = msgId /\
            ValidMsgsIn impl [rs] /\
            [rs] = getRss orq.
  Proof.
    unfold RssFullOne, getRss; intros.
    red in H.
    destruct orq@[downRq] as [rqid|]; simpl in *; [dest|exfalso; auto].
    clear H2; red in H; dest.
    exists rqid; repeat split.
    destruct (rqi_rss rqid) as [|[rmidx rs] rss]; [discriminate|].
    destruct rss; [|discriminate].
    clear H0 H2.
    inv H1; inv H3; inv H4; clear H6 H7 H8. (* [Forall ..] *)
    apply SubList_cons_inv in H; dest; clear H0.
    simpl in *; destruct rs as [rs|]; [|exfalso; auto].
    eexists (rmidx, rs); simpl.
    repeat split; try assumption.
    - simpl; apply SubList_cons; [|apply SubList_nil].
      apply in_or_app; left; auto.
    - repeat constructor; intro Hx; auto.
  Qed.

  Lemma RssORqEquiv_addRs:
    forall orq1 orq2,
      RssORqEquiv orq1 orq2 ->
      forall midx rs,
        RssORqEquiv (addRs orq1 midx rs) orq2.
  Proof.
    unfold RssORqEquiv; intros; dest.
    repeat split.
    - unfold addRs.
      destruct orq1@[downRq] as [rqid1|]; simpl in *; [mred|assumption].
    - unfold addRs.
      destruct orq1@[downRq] as [rqid1|] eqn:Hrqid1; simpl in *; mred.
    - unfold addRs; intros.
      destruct orq1@[downRq] as [prqid1|] eqn:Hprqid1; simpl in *; [|mred].
      mred; simpl.
      specialize (H1 _ eq_refl).
      destruct H1 as [rqid2 ?]; dest.
      exists rqid2; repeat split; try assumption.
      rewrite <-H3.
      clear; induction (rqi_rss prqid1) as [|[rmidx irs]]; [reflexivity|].
      simpl; destruct (idx_dec midx rmidx).
      all: simpl; congruence.
  Qed.

  Lemma SimRssORqs_addRs:
    forall orqs1 orqs2,
      SimRssORqs orqs1 orqs2 ->
      forall roidx porq midx rs,
        orqs1@[roidx] = Some porq ->
        SimRssORqs (orqs1+[roidx <- addRs porq midx rs]) orqs2.
  Proof.
    unfold SimRssORqs; intros.
    rewrite Forall_forall in H.
    apply Forall_forall; intros oidx ? ? ?.
    specialize (H _ H1).
    destruct (idx_dec oidx roidx); subst; mred; [|eauto; fail].
    specialize (H _ eq_refl); destruct H as [orq2 [? ?]].
    exists orq2; split; [assumption|].
    apply RssORqEquiv_addRs; assumption.
  Qed.

  Lemma findRs_putRs_eq:
    forall midx rs rss,
      In (midx, None) rss ->
      findRs midx (putRs midx rs rss) = Some rs.
  Proof.
    induction rss as [|[rmidx irs]]; simpl; intros; [exfalso; auto|].
    destruct H; subst; simpl in *.
    - inv H.
      destruct (idx_dec midx midx); [|exfalso; auto].
      simpl; destruct (idx_dec midx midx); [|exfalso; auto].
      reflexivity.
    - destruct (idx_dec midx rmidx); subst.
      + simpl; destruct (idx_dec rmidx rmidx); [reflexivity|exfalso; auto].
      + simpl; destruct (idx_dec rmidx midx); [exfalso; auto|].
        apply IHrss; assumption.
  Qed.

  Lemma findRs_putRs_neq:
    forall midx amidx,
      midx <> amidx ->
      forall rs rss,
        findRs midx (putRs amidx rs rss) = findRs midx rss.
  Proof.
    induction rss as [|[rmidx irs]]; simpl; intros; [reflexivity|].
    destruct (idx_dec amidx rmidx); subst; simpl.
    - destruct (idx_dec rmidx midx); subst; [exfalso; auto|reflexivity].
    - destruct (idx_dec rmidx midx); subst; [reflexivity|assumption].
  Qed.

  Lemma SimRssMP_addRs:
    forall iorqs imsgs smsgs,
      SimRssMP iorqs imsgs smsgs ->
      forall oidx porq,
        iorqs@[oidx] = Some porq ->
        forall rqid,
          porq@[downRq] = Some rqid ->
          RssWf oidx (rqi_rss rqid) ->
          forall cidx,
            parentIdxOf topo cidx = Some oidx ->
            In (rsUpFrom cidx, None) (rqi_rss rqid) ->
            forall rs,
              FirstMP imsgs (rsUpFrom cidx) rs ->
              SimRssMP (iorqs +[oidx <- addRs porq (rsUpFrom cidx) rs])
                       (deqMP (rsUpFrom cidx) imsgs) smsgs.
  Proof.
    unfold SimRssMP; intros.
    specialize (H midx); dest.
    repeat split; intros.
    1-2: rewrite findQ_not_In_deqMP by (intro Hx; rewrite Hx in H8; discriminate); eauto.

    clear H H6.
    subst midx.
    specialize (H7 _ eq_refl _ H9 H10).
    destruct (idx_dec oidx pidx); subst; mred;
      [|rewrite findQ_not_In_deqMP by (intro Hx; inv Hx; congruence);
        assumption].

    simpl; unfold addRs.
    rewrite H1; simpl; mred; simpl.
    destruct (idx_dec oidx0 cidx); subst.
    - rewrite findRs_putRs_eq by assumption.
      simpl; rewrite findQ_In_deqMP_FirstMP by assumption.
      erewrite findRs_rs in H7; [|apply H2|eassumption].
      assumption.
    - rewrite findRs_putRs_neq by (intro Hx; inv Hx; auto).
      rewrite findQ_not_In_deqMP  by (intro Hx; inv Hx; auto).
      assumption.
  Qed.

  Lemma SimRssMP_rss_full_first:
    forall iorqs imsgs smsgs,
      SimRssMP iorqs imsgs smsgs ->
      forall oidx orq rqid,
        In oidx (c_li_indices cifc ++ c_l1_indices cifc) ->
        iorqs@[oidx] = Some orq ->
        orq@[downRq] = Some rqid ->
        NoDup (map fst (rqi_rss rqid)) ->
        Forall (fun iom =>
                  exists cidx,
                    parentIdxOf topo cidx = Some oidx /\
                    rsUpFrom cidx = fst iom) (rqi_rss rqid) ->
        forall rss,
          rqi_rss rqid = map (fun idm => (idOf idm, Some (valOf idm))) rss ->
          Forall (FirstMPI smsgs) rss.
  Proof.
    unfold SimRssMP; intros.
    apply Forall_forall; intros [rmidx rs] ?.
    assert (In (rmidx, Some rs) (rqi_rss rqid))
      by (rewrite H5; apply in_map_iff; eexists (_, _); simpl; eauto).

    rewrite Forall_forall in H4; specialize (H4 _ H7).
    destruct H4 as [cidx ?]; simpl in H4; dest; subst.
    specialize (H (rsUpFrom cidx)); dest.
    clear H H8.
    specialize (H9 _ eq_refl _ H0 H4).
    rewrite H1 in H9; simpl in H9.
    rewrite H2 in H9; simpl in H9.

    erewrite findRs_rs in H9 by eassumption.
    simpl in H9.
    unfold FirstMPI, FirstMP, firstMP.
    simpl; rewrite <-H9.
    reflexivity.
  Qed.

  Lemma RssORqEquiv_removeRq:
    forall orq1 orq2,
      RssORqEquiv orq1 orq2 ->
      RssORqEquiv (removeRq orq1 downRq) (removeRq orq2 downRq).
  Proof.
    unfold RssORqEquiv, removeRq; intros; dest.
    repeat split; mred.
  Qed.

  Lemma SimRssORqs_removeRq:
    forall orqs1 orqs2,
      SimRssORqs orqs1 orqs2 ->
      forall roidx porq1 porq2,
        orqs1@[roidx] = Some porq1 ->
        orqs2@[roidx] = Some porq2 ->
        SimRssORqs (orqs1+[roidx <- removeRq porq1 downRq])
                   (orqs2+[roidx <- removeRq porq2 downRq]).
  Proof.
    unfold SimRssORqs, removeRq; intros.
    rewrite Forall_forall in H.
    apply Forall_forall; intros oidx ? ? ?.
    specialize (H _ H2).
    destruct (idx_dec oidx roidx); subst; mred; [|eauto; fail].
    specialize (H _ eq_refl); destruct H as [orq2 [? ?]].
    inv H.
    eexists; split; [reflexivity|].
    apply RssORqEquiv_removeRq; assumption.
  Qed.

  Lemma SimRssMP_removeRq:
    forall iorqs imsgs smsgs,
      SimRssMP iorqs imsgs smsgs ->
      forall roidx,
        (* In roidx (c_li_indices cifc ++ c_l1_indices cifc) -> *)
        forall porq,
          iorqs@[roidx] = Some porq ->
          forall rqid,
            porq@[downRq] = Some rqid ->
            NoDup (idsOf (getRss porq)) ->
            rqi_rss rqid = map (fun idm => (idOf idm, Some (valOf idm))) (getRss porq) ->
            Forall
              (fun iom =>
                 exists cidx : IdxT,
                   parentIdxOf topo cidx = Some roidx /\
                   rsUpFrom cidx = fst iom) (rqi_rss rqid) ->
            SimRssMP (iorqs +[roidx <- removeRq porq downRq])
                     imsgs (deqMsgs (idsOf (getRss porq)) smsgs).
  Proof.
    unfold SimRssMP, removeRq; intros.
    specialize (H midx); dest.

    repeat split.
    - clear H5 H6.
      intros; subst; specialize (H _ eq_refl).
      rewrite findQ_not_In_deqMsgs; [assumption|].
      unfold getRss; rewrite H1; simpl.
      clear -H4.
      induction (rqi_rss rqid) as [|[rmidx rs]]; simpl in *; [auto|].
      destruct rs as [rs|]; simpl in *.
      + intro Hx; destruct Hx; subst.
        * inv H4; simpl in *; dest; inv H0.
        * inv H4; elim (IHl H3); assumption.
      + inv H4; auto.
    - clear H H6.
      intros; subst; specialize (H5 _ eq_refl).
      rewrite findQ_not_In_deqMsgs; [assumption|].
      unfold getRss; rewrite H1; simpl.
      clear -H4.
      induction (rqi_rss rqid) as [|[rmidx rs]]; simpl in *; [auto|].
      destruct rs as [rs|]; simpl in *.
      + intro Hx; destruct Hx; subst.
        * inv H4; simpl in *; dest; inv H0.
        * inv H4; elim (IHl H3); assumption.
      + inv H4; auto.

    - clear H H5.
      intros; subst; specialize (H6 _ eq_refl _ H5 H7).
      destruct (idx_dec roidx pidx); subst; repeat (simpl in *; mred).
      + destruct (in_dec idx_dec (rsUpFrom oidx) (idsOf (getRss porq))).
        * assert (exists rs, findRs (rsUpFrom oidx) (rqi_rss rqid) = Some rs).
          { unfold getRss in i, H3; rewrite H1 in i, H3; simpl in *.
            clear -i H3.
            induction (rqi_rss rqid) as [|[rmidx rs]]; simpl in *; [exfalso; auto|].
            destruct rs as [rs|]; simpl in *.
            { destruct i; subst.
              { destruct (idx_dec _ _); [eauto|exfalso; auto]. }
              { inv H3.
                specialize (IHl H1 H); destruct IHl as [irs ?].
                rewrite <-H1.
                destruct (idx_dec _ _); eauto.
              }
            }
            { exfalso; destruct (retRss l); discriminate. }
          }
          destruct H as [rs ?].
          rewrite H in H6; simpl in H6.

          apply findQ_In_NoDup_deqMsgs with (mp:= smsgs) in i;
            [|eassumption|rewrite <-H6; discriminate]; dest.
          rewrite <-H8 in H6; congruence.

        * assert (findRs (rsUpFrom oidx) (rqi_rss rqid) = None).
          { unfold getRss in n, H3; rewrite H1 in n, H3; simpl in *.
            clear -n.
            induction (rqi_rss rqid) as [|[rmidx rs]]; simpl in *; [reflexivity|].
            destruct rs as [rs|]; simpl in *.
            { destruct (idx_dec _ _); subst; [elim n; left; reflexivity|].
              destruct (in_dec idx_dec (rsUpFrom oidx) (idsOf (retRss l))).
              { elim n; right; assumption. }
              { auto. }
            }
            { destruct (idx_dec _ _); [reflexivity|auto]. }
          }
          rewrite H in H6; simpl in H6.

          rewrite findQ_not_In_deqMsgs by assumption.
          assumption.

      + rewrite H6.
        rewrite findQ_not_In_deqMsgs; [reflexivity|].
        unfold getRss; rewrite H1; simpl.
        clear -H4 H7 n.
        induction (rqi_rss rqid) as [|[rmidx rs]]; simpl in *; [auto|].
        destruct rs as [rs|]; simpl in *.
        * intro Hx; destruct Hx; subst.
          { inv H4; simpl in *; dest.
            inv H0; congruence.
          }
          { inv H4; elim (IHl H3); assumption. }
        * inv H4; auto.
  Qed.

  Ltac disc_SimRssORqs obj :=
    match goal with
    | [H: SimRssORqs ?orqs _ |- _] =>
      let Hs := fresh "H" in
      pose proof H as Hs;
      red in Hs; rewrite <-Hoinds in Hs;
      rewrite Forall_forall in Hs;
      specialize (Hs (obj_idx obj) ltac:(apply in_map; assumption));
      match goal with
      | [Horq: orqs@[obj_idx obj] = Some _ |- _] =>
        specialize (Hs _ Horq);
        let sorq := fresh "sorq" in
        destruct Hs as [sorq ?]; dest
      end
    end.

  Ltac disc_RssWfInv obj :=
    match goal with
    | [H: RssWfInv {| st_orqs := ?orqs |}, Horq: ?orqs@[obj_idx obj] = Some _ |- _] =>
      let Hi := fresh "Hi" in
      pose proof (H (obj_idx obj)) as Hi;
      simpl in Hi; rewrite Horq in Hi; simpl in Hi
    end.

  Ltac disc_RssWfORq obj :=
    match goal with
    | [H: RssWfORq (obj_idx obj) ?orq, Horq: ?orq@[downRq] = Some _ |- _] =>
      let Hwfo := fresh "Hwfo" in
      let Hrsb := fresh "Hrsb" in
      red in H; rewrite Horq in H; destruct H as [Hwfo Hrsb]
    end.

  Ltac disc_RssORqEquiv :=
    match goal with
    | [He: RssORqEquiv ?orq1 ?orq2 |- _] =>
      let Hul := fresh "Hul" in
      let Hdln := fresh "Hdln" in
      let Hdls := fresh "Hdls" in
      destruct He as [Hul [Hdln Hdls]];
      try match goal with
          | [Ho: orq1@[downRq] = Some _ |- _] =>
            specialize (Hdls _ Ho);
            let srqid := fresh "srqid" in
            destruct Hdls as [srqid ?]; dest
          end
    end.

  Lemma UpLockRssORq_MsgsFromORq_NoRsUpInputs:
    forall oidx porq,
      UpLockRssORq oidx porq ->
      forall post ins,
        MsgsFromORq upRq post porq ins ->
        NoRsUpInputs ins.
  Proof.
    intros.
    red in H, H0.
    destruct (porq@[upRq]) as [prqiu|]; [|exfalso; auto].
    simpl in *; dest.
    rewrite H in H0.
    red; intros [rmidx rmsg] ?.
    apply in_map with (f:= idOf) in H1.
    setoid_rewrite H0 in H1.
    dest_in; simpl in *; subst.
    eauto.
  Qed.

  Theorem rss_holder_rss_sim_ok:
    InvSim step_m step_m (fun st => UpLockRssInv st /\ RssWfInv st) sim impl spec.
  Proof.
    red; intros.
    destruct H1 as [Hul Hwf]. (* [UpLockRssInv ist1 /\ RssWfInv ist1] *)
    clear H3. (* for [ist2] *)

    inv H2;
      [apply rss_holder_rss_sim_silent; assumption
      |apply rss_holder_rss_sim_ext_in; assumption
      |apply rss_holder_rss_sim_ext_out; assumption
      |].

    destruct sst1 as [soss1 sorqs1 smsgs1].
    red in H0; simpl in H0; dest; subst.

    move Hir at bottom.
    pose proof (Hir _ H1) as [sobj [HsoIn [Hoi Hrr]]].
    specialize (Hrr _ H3).
    destruct Hrr as [|[|[|]]].

    - (*! Normal rules *)
      dest.
      disc_SimRssORqs obj.

      (* Discharge [RssEquivRule] to get the transition for the spec. *)
      pose proof H10.
      apply H0 in H16; [|assumption]; dest.
      specialize (H18 _ H15).
      destruct H18 as [sorq2 [? ?]].

      assert (NoRsUpInputs ins) as Hins.
      { red in H0; dest.
        specialize (H0 _ _ _ H9); dest.
        destruct H0; [assumption|].
        red in Hul; simpl in Hul.
        specialize (Hul (obj_idx obj)); rewrite H6 in Hul; simpl in Hul.
        eapply UpLockRssORq_MsgsFromORq_NoRsUpInputs; eauto.
      }

      do 2 eexists.
      repeat ssplit; [reflexivity|..].

      + econstructor.
        1-4: eassumption.
        { exact H14. }
        { eapply SimRssMP_NoRsUpInputs_first; eauto. }
        { destruct H8; split; [|assumption].
          rewrite Hsminds, Hserqs.
          rewrite Himinds, Hierqs in H8.
          assumption.
        }
        { eapply H0; eassumption. }
        { eassumption. }
        { destruct H11; split; [|assumption].
          rewrite Hsminds, Hserss.
          rewrite Himinds, Hierss in H11.
          assumption.
        }
        { assumption. }
        { reflexivity. }
        { reflexivity. }

      + red; simpl; repeat ssplit; [reflexivity|..].
        * apply SimRssORqs_next_ord; auto.
        * apply SimRssMP_enqMsgs.
          apply SimRssMP_deqMsgs; [|assumption].
          eapply SimRssMP_ORqs_change_silent; eassumption.

    - (*! [RsRelease] *)
      destruct H0 as [ridx [msgId [rqId [prec [trs [? ?]]]]]]; subst rule.
      disc_SimRssORqs obj.
      disc_RssWfInv obj.

      (* Discharge precondition and transition *)
      disc_rule_conds_ex.
      destruct ins; [clear H7 H8 H9 H12|discriminate].
      eapply RssFullWithId_spec in H17; [|eassumption].
      destruct H17 as [rqid [? [rss [? [? [? ?]]]]]]; subst rss.
      disc_RssWfORq obj.
      disc_rule_conds_ex.
      disc_RssORqEquiv.

      eexists (RlblInt _ _ _ _); eexists.
      repeat ssplit; [simpl; reflexivity|..].

      + econstructor.
        * eassumption.
        * eassumption.
        * reflexivity.
        * rewrite <-Hoi; eassumption.
        * rewrite <-Hoi; eassumption.
        * red in Hwfo; dest.
          eapply SimRssMP_rss_full_first; eauto.
          { rewrite <-Hoinds.
            apply in_map_iff; eauto.
          }
          { congruence. }
          { congruence. }
        * destruct H12; split; [|assumption].
          rewrite Hierqs, Himinds in H12.
          rewrite Hserqs, Hsminds; assumption.
        * repeat split.
          { red; rewrite H7; simpl.
            rewrite <-H15, H8.
            rewrite map_map; reflexivity.
          }
          { assumption. }
          { red; rewrite H7; simpl.
            rewrite <-H14, Hmsg; simpl; split; [assumption|reflexivity].
          }
          { red; rewrite H7; simpl.
            rewrite <-H17, Hidx; simpl; auto.
          }
          { red; red in Hwfo; dest.
            apply Forall_forall; intros [rmidx rs] ?; simpl.
            apply in_map with (f:= fun idm => (idOf idm, Some (valOf idm))) in H23; simpl in H23.
            rewrite Forall_forall in H22; specialize (H22 _ H23).
            assumption.
          }
          { assumption. }

        * simpl; unfold TrsMTrs, getDownLockMsg, getDownLockIdxBack; simpl.
          rewrite H7; simpl.
          rewrite <-H14, Hmsg, <-H17, Hidx; simpl.
          reflexivity.
        * destruct H11.
          split; [|assumption].
          rewrite Himinds, Hierss in H11.
          rewrite Hsminds, Hserss; assumption.
        * red in Hwfo; dest.
          simpl; clear -H21 Hrsb.
          apply (DisjList_false_spec idx_dec).
          intros midx; intros; dest_in.
          rewrite Forall_forall in H21.
          apply in_map_iff in H; destruct H as [[rmidx rs] [? ?]]; simpl in *; subst.
          apply in_map with (f:= fun idm => (idOf idm, Some (valOf idm))) in H0.
          specialize (H21 _ H0).
          destruct H21 as [cidx [? ?]]; simpl in *; subst.
          elim (Hrsb cidx).
          { eapply parentIdxOf_not_eq; [|eassumption].
            apply tree2Topo_WfDTree.
          }
          { reflexivity. }
        * reflexivity.
        * reflexivity.

      + red; simpl; repeat ssplit; [congruence|..].
        * rewrite <-Hoi.
          apply SimRssORqs_removeRq; [assumption|assumption|congruence].
        * eapply SimRssMP_enqMP.
          eapply SimRssMP_removeRq; eauto.
          { apply H12. }
          { rewrite H8; apply Hwfo. }

    - (*! [RsReleaseOne] *)
      destruct H0 as [ridx [msgId [rqId [prec [trs [? ?]]]]]]; subst rule.
      disc_SimRssORqs obj.
      disc_RssWfInv obj.

      (* Discharge precondition and transition *)
      disc_rule_conds_ex.
      destruct ins; [clear H7 H8 H9 H12|discriminate].
      eapply RssFullOne_spec in H17; [|eassumption].
      destruct H17 as [rqid [? [rs [? [? [? ?]]]]]].
      disc_RssWfORq obj.
      disc_rule_conds_ex.
      disc_RssORqEquiv.

      eexists (RlblInt _ _ _ _); eexists.
      repeat ssplit; [simpl; reflexivity|..].

      + econstructor.
        * eassumption.
        * eassumption.
        * reflexivity.
        * rewrite <-Hoi; eassumption.
        * rewrite <-Hoi; eassumption.
        * red in Hwfo; dest.
          eapply SimRssMP_rss_full_first; eauto.
          { rewrite <-Hoinds.
            apply in_map_iff; eauto.
          }
          { congruence. }
          { congruence. }
          { instantiate (1:= [rs]); assumption. }
        * destruct H12; split; [|assumption].
          rewrite Hierqs, Himinds in H12.
          rewrite Hserqs, Hsminds; assumption.
        * repeat split.
          { red; rewrite H7; simpl.
            rewrite <-H14, H8.
            reflexivity.
          }
          { red; rewrite H7; simpl.
            rewrite <-H9, Hmsg; simpl; split; [assumption|reflexivity].
          }
          { red; rewrite H7; simpl.
            rewrite <-H17, Hidx; simpl; auto.
          }
          { red; red in Hwfo; dest.
            repeat constructor.
            inv H22; assumption.
          }
          { assumption. }

        * simpl; unfold TrsMTrs, getDownLockMsg, getDownLockIdxBack; simpl.
          rewrite H7; simpl.
          rewrite <-H9, Hmsg, <-H17, Hidx; simpl.
          reflexivity.
        * destruct H11.
          split; [|assumption].
          rewrite Himinds, Hierss in H11.
          rewrite Hsminds, Hserss; assumption.
        * red in Hwfo; dest.
          simpl.
          apply (DisjList_false_spec idx_dec).
          intros midx; intros; dest_in.
          inv H21; simpl in *; dest.
          apply Hrsb with (roidx:= x); [|auto].
          eapply parentIdxOf_not_eq; [|eassumption].
          apply tree2Topo_WfDTree.
        * reflexivity.
        * reflexivity.

      + red; simpl; repeat ssplit.
        * rewrite <-H15; simpl; congruence.
        * rewrite <-Hoi.
          apply SimRssORqs_removeRq; [assumption|assumption|congruence].
        * rewrite <-H15; simpl.
          eapply SimRssMP_enqMP.
          replace (deqMP (fst rs) smsgs1) with (deqMsgs (idsOf (getRss porq)) smsgs1)
            by (rewrite <-H15; reflexivity).
          eapply SimRssMP_removeRq; eauto.
          { rewrite <-H15; repeat constructor; auto. }
          { rewrite <-H15, H8; reflexivity. }
          { rewrite H8; apply Hwfo. }

    - (*! [RsTakeOne] *)
      destruct H0 as [ridx [msgId [rqId [cidx [? ?]]]]]; subst rule.
      disc_SimRssORqs obj.
      disc_rule_conds_ex.
      disc_RssWfInv obj.
      disc_RssWfORq obj.

      exists RlblEmpty; eexists.
      repeat ssplit; [reflexivity|constructor|].
      red; simpl; repeat ssplit; [meq|..].
      + apply SimRssORqs_addRs; auto.
      + red in H18; rewrite Hrqi in H18; simpl in H18.
        eapply SimRssMP_addRs; try eassumption.
  Qed.

  Theorem rss_holder_ok_inv:
    InvReachable impl step_m RssWfInv ->
    (steps step_m) # (steps step_m) |-- impl ⊑ spec.
  Proof.
    intros.
    eapply invRSim_implies_refinement with (sim:= sim).
    - instantiate (1:= fun st => UpLockRssInv st /\ RssWfInv st).
      red; intros; split.
      + eapply inv_reachable; [..|eassumption].
        * typeclasses eauto.
        * apply UpLockRssInv_init.
        * apply UpLockRssInv_step.
      + apply H; assumption.
    - apply rss_holder_rss_sim_init.
    - apply rss_holder_rss_sim_ok.
  Qed.

  Theorem rss_holder_ok:
    GoodRqRsSys topo spec ->
    GoodExtRssSys spec ->
    (steps step_m) # (steps step_m) |-- impl ⊑ spec.
  Proof.
    intros.
    apply rss_holder_ok_inv.
    apply good_rqrs_sys_implies_RssWf; assumption.
  Qed.

End RssHolderOk.

Section RssEquivRule.
  Context `{dv:DecValue} `{oifc: OStateIfc}.

  Lemma UpLockDownTo_refl:
    forall orq1 orq2,
      orq1@[upRq] = orq2@[upRq] ->
      UpLockDownTo orq1 orq2.
  Proof.
    unfold UpLockDownTo; intros.
    rewrite H.
    destruct orq2@[upRq]; auto.
  Qed.
  Local Hint Extern 4 (UpLockDownTo _ _) => (apply UpLockDownTo_refl; auto).

  Lemma NoRssChange_refl:
    forall orq1 orq2,
      orq1@[downRq] = orq2@[downRq] ->
      NoRssChange orq1 orq2.
  Proof.
    unfold NoRssChange; intros.
    rewrite H.
    destruct (orq2@[downRq]); auto.
  Qed.
  Local Hint Extern 4 (NoRssChange _ _) => (apply NoRssChange_refl; auto).

  Definition RssORqEquivPrec (prec: OPrec) :=
    forall ost orq1 mins,
      prec ost orq1 mins ->
      forall orq2, RssORqEquiv orq1 orq2 -> prec ost orq2 mins.

  Lemma immRule_RssEquivRule:
    forall ridx prec trs,
      RssORqEquivPrec prec ->
      RssEquivRule (immRule ridx prec trs).
  Proof.
    intros.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split.
      + left; red in H0; red; intros.
        destruct mins; [exfalso; auto|discriminate].
      + intros; repeat ssplit; try eassumption.
        * repeat red in H1; repeat red.
          red in H4; dest; congruence.
        * apply H4; assumption.
        * eapply H; eauto.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      inv H1; repeat split; auto.
      intros; eauto.
  Qed.

  Lemma immUpRule_RssEquivRule:
    forall ridx msgId oidx prec trs,
      RssORqEquivPrec prec ->
      RssEquivRule (immUpRule ridx msgId oidx prec trs).
  Proof.
    intros.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split.
      + left; red in H0; red; intros.
        destruct mins as [|[rmidx rmsg] ?]; [discriminate|].
        destruct mins; [|discriminate].
        inv H0; dest_in; simpl; eauto.
      + intros; repeat ssplit; try assumption.
        * apply H5; assumption.
        * eapply H; eauto.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      all: inv H1; eauto; fail.
  Qed.

  Lemma immDownRule_RssEquivRule:
    forall ridx msgId cidx prec trs,
      RssORqEquivPrec prec ->
      RssEquivRule (immDownRule ridx msgId cidx prec trs).
  Proof.
    intros.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split.
      + left; red in H0; red; intros.
        destruct mins as [|[rmidx rmsg] ?]; [discriminate|].
        destruct mins; [|discriminate].
        inv H0; dest_in; simpl; eauto.
      + intros; repeat ssplit; try assumption.
        * repeat red in H3; repeat red.
          red in H6; dest; congruence.
        * apply H6; assumption.
        * eapply H; eauto.
    - red; simpl; unfold TrsMTrs; simpl; intros.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      all: inv H1; eauto; fail.
  Qed.

  Lemma rqUpUpRule_RssEquivRule:
    forall ridx msgId cidx oidx prec trs,
      RssEquivRule (rqUpUpRule ridx msgId cidx oidx prec trs).
  Proof.
    intros.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split.
      + left; red in H; red; intros.
        destruct mins as [|[rmidx rmsg] ?]; [discriminate|].
        destruct mins; [|discriminate].
        inv H; dest_in; simpl; eauto.
      + intros; repeat ssplit; try assumption.
        repeat red in H2; repeat red.
        red in H4; dest; congruence.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      + inv H0; repeat split.
        * repeat red in H3; red.
          unfold addRq; mred; simpl; eauto.
        * red; unfold addRq; mred.
          apply NoRssChange_refl; auto.
        * intros; eexists; split; [reflexivity|].
          red in H0; dest.
          red; repeat split.
          all: unfold addRq; mred.
      + inv H0; eauto.
  Qed.

  Lemma rqUpUpRuleS_RssEquivRule:
    forall ridx oidx prec trs,
      RssEquivRule (rqUpUpRuleS ridx oidx prec trs).
  Proof.
    intros.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split.
      + left; red in H; red; intros.
        destruct mins; [exfalso; auto|discriminate].
      + intros; repeat ssplit; try assumption.
        repeat red in H2; repeat red.
        red in H3; dest; congruence.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      inv H0; repeat split.
      + repeat red in H2; red.
        unfold addRqS; mred; simpl; eauto.
      + red; unfold addRqS; mred.
        apply NoRssChange_refl; auto.
      + intros; eexists; split; [reflexivity|].
        red in H0; dest.
        red; repeat split.
        all: unfold addRqS; mred.
  Qed.

  Lemma rqUpDownRule_RssEquivRule:
    forall ridx msgId cidx oidx prec trs,
      RssEquivRule (rqUpDownRule ridx msgId cidx oidx prec trs).
  Proof.
    intros.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split.
      + left; red in H; red; intros.
        destruct mins as [|[rmidx rmsg] ?]; [discriminate|].
        destruct mins; [|discriminate].
        inv H; dest_in; simpl; eauto.
      + intros; repeat ssplit; try assumption.
        repeat red in H2; repeat red.
        apply H4; assumption.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      + inv H0; repeat split.
        * red; unfold addRq; mred.
          apply UpLockDownTo_refl; reflexivity.
        * repeat red in H3.
          red; unfold addRq; mred; simpl.
          apply Forall_forall; intros.
          apply in_map_iff in H0; dest; subst; reflexivity.
        * intros; eexists; split; [reflexivity|].
          red in H0; dest.
          red; repeat split.
          all: unfold addRq; mred.
          eauto.
      + inv H0; eauto.
  Qed.

  Lemma rqUpDownRuleS_RssEquivRule:
    forall ridx prec trs,
      RssEquivRule (rqUpDownRuleS ridx prec trs).
  Proof.
    intros.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split.
      + left; red in H; red; intros.
        destruct mins; [exfalso; auto|discriminate].
      + intros; repeat ssplit; try assumption.
        repeat red in H2; repeat red.
        apply H3; assumption.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      inv H0; repeat split.
      + red; unfold addRqS; mred.
        apply UpLockDownTo_refl; reflexivity.
      + repeat red in H2.
        red; unfold addRqS; mred; simpl.
        apply Forall_forall; intros.
        apply in_map_iff in H0; dest; subst; reflexivity.
      + intros; eexists; split; [reflexivity|].
        red in H0; dest.
        red; repeat split.
        all: unfold addRqS; mred.
        eauto.
  Qed.

  Lemma rqDownDownRule_RssEquivRule:
    forall ridx msgId oidx prec trs,
      RssEquivRule (rqDownDownRule ridx msgId oidx prec trs).
  Proof.
    intros.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split.
      + left; red in H; red; intros.
        destruct mins as [|[rmidx rmsg] ?]; [discriminate|].
        destruct mins; [|discriminate].
        inv H; dest_in; simpl; eauto.
      + intros; repeat ssplit; try assumption.
        repeat red in H2; repeat red.
        apply H4; assumption.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      destruct (getFirstMsg mins) as [fmsg|]; simpl in *.
      + inv H0; repeat split.
        * red; unfold addRq; mred.
          apply UpLockDownTo_refl; reflexivity.
        * repeat red in H3.
          red; unfold addRq; mred; simpl.
          apply Forall_forall; intros.
          apply in_map_iff in H0; dest; subst; reflexivity.
        * intros; eexists; split; [reflexivity|].
          red in H0; dest.
          red; repeat split.
          all: unfold addRq; mred.
          eauto.
      + inv H0; eauto.
  Qed.

  Ltac destruct_bind :=
    match goal with
    | |- context [bind ?o ?c] => destruct o
    | H: context [bind ?o ?c] |- _ => destruct o
    end.

  Lemma rsDownDownRule_RssEquivRule:
    forall ridx msgId rqId prec trs,
      RssORqEquivPrec prec ->
      RssEquivRule (rsDownDownRule ridx msgId rqId prec trs).
  Proof.
    intros.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split; [right; assumption|].
      intros; red in H7; dest.
      repeat ssplit; try assumption.
      + red in H0; red; congruence.
      + red in H2; red; congruence.
      + red in H3; red; congruence.
      + apply H8; assumption.
      + eapply H; eauto; repeat split; assumption.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      repeat ssplit.
      + do 3 (destruct_bind; simpl in *; [|inv H1; eauto]).
        inv H1; red; unfold removeRq; mred.
      + do 3 (destruct_bind; simpl in *; [|inv H1; eauto]).
        inv H1; red; unfold removeRq; mred.
        apply NoRssChange_refl; reflexivity.
      + intros; unfold getUpLockMsg, getUpLockIdxBack in *.
        rewrite <-(proj1 H8).
        do 3 (destruct_bind; simpl in *; [|inv H1; eauto]).
        inv H1.
        eexists; split; [reflexivity|].
        red in H8; dest.
        red; repeat split.
        all: try (unfold removeRq; mred; fail).
  Qed.

  Lemma rsDownDownRuleS_RssEquivRule:
    forall ridx msgId prec trs,
      RssORqEquivPrec prec ->
      RssEquivRule (rsDownDownRuleS ridx msgId prec trs).
  Proof.
    intros.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split; [right; assumption|].
      intros; red in H6; dest.
      repeat ssplit; try assumption.
      + red in H0; red; congruence.
      + red in H2; red; congruence.
      + apply H7; assumption.
      + eapply H; eauto; repeat split; assumption.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      repeat ssplit.
      + destruct_bind; simpl in *; [|inv H1; eauto].
        inv H1; red; unfold removeRq; mred.
      + destruct_bind; simpl in *; [|inv H1; eauto].
        inv H1; red; unfold removeRq; mred.
        apply NoRssChange_refl; reflexivity.
      + destruct_bind; simpl in *; [|inv H1; eauto].
        inv H1.
        eexists; split; [reflexivity|].
        red in H1; dest.
        red; repeat split.
        all: try (unfold removeRq; mred; fail).
  Qed.

  Lemma rsDownRqDownRule_RssEquivRule:
    forall ridx msgId oidx rqId prec trs,
      RssORqEquivPrec prec ->
      RssEquivRule (rsDownRqDownRule ridx msgId oidx rqId prec trs).
  Proof.
    intros.
    red; split.
    - red; simpl; unfold OPrecAnd; intros; dest; split; [right; assumption|].
      intros; red in H7; dest.
      repeat ssplit; try assumption.
      + red in H0; red; congruence.
      + red in H2; red; congruence.
      + red in H3; red; congruence.
      + apply H8; assumption.
      + eapply H; eauto; repeat split; assumption.
    - red; simpl; unfold OPrecAnd, TrsMTrs; simpl; intros; dest.
      repeat ssplit.
      + do 2 (destruct_bind; simpl in *; [|inv H1; eauto]).
        inv H1; red; unfold addRq, removeRq; mred.
      + do 2 (destruct_bind; simpl in *; [|inv H1; eauto]).
        inv H1; red; unfold addRq, removeRq; mred.
        repeat red in H6; rewrite H6.
        simpl; apply Forall_forall; intros.
        apply in_map_iff in H1; dest; subst; reflexivity.
      + intros; unfold getUpLockMsg, getUpLockIdxBack in *.
        rewrite <-(proj1 H8).
        do 2 (destruct_bind; simpl in *; [|inv H1; eauto]).
        inv H1.
        eexists; split; [reflexivity|].
        red in H8; dest.
        red; repeat split.
        all: try (unfold addRq, removeRq; mred; fail).
        unfold addRq, removeRq; mred.
        intros; inv H10; simpl; eauto.
  Qed.

End RssEquivRule.
