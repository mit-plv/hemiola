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

Lemma concat_map_In:
  forall {A} (a: A) l,
    In a l ->
    forall {B} (f: A -> B) (g: A -> list B),
      (forall a, In (f a) (g a)) ->
      In (f a) (List.concat (map g l)).
Proof.
  induction l; simpl; intros; auto.
  destruct H; subst.
  - apply in_or_app; left; auto.
  - apply in_or_app; right; auto.
Qed.

Section RssHolderOk.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).
  Context `{dv:DecValue} `{oifc: OStateIfc}.

  Local Notation topo := (fst (tree2Topo tr 0)).
  Local Notation cifc := (snd (tree2Topo tr 0)).

  Variables (impl spec: System).

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

  Definition RssEquivPrec (prec: OPrec) :=
    forall ost orq1 mins,
      prec ost orq1 mins ->
      forall orq2,
        RssORqEquiv orq1 orq2 -> prec ost orq2 mins.

  Definition RssEquivTrs (trs: OTrs) :=
    forall ost orq1 mins nost norq1 mouts,
      trs ost orq1 mins = (nost, norq1, mouts) ->
      forall orq2,
        RssORqEquiv orq1 orq2 ->
        exists norq2,
          trs ost orq2 mins = (nost, norq2, mouts) /\
          RssORqEquiv norq1 norq2.

  Definition NoRsUpInputs (mins: list (Id Msg)) :=
    forall idm,
      In idm mins ->
      (exists oidx, idOf idm = rqUpFrom oidx \/ idOf idm = downTo oidx).

  Definition NoRsUpInputsPrec (prec: OPrec) :=
    forall ost orq mins, prec ost orq mins -> NoRsUpInputs mins.

  Definition NoRssChange (orq1 orq2: ORq Msg) :=
    match orq1@[downRq], orq2@[downRq] with
    | Some rqid1, Some rqid2 => rqid1.(rqi_rss) = rqid2.(rqi_rss)
    | Some rqid1, None => Forall (fun rs => snd rs = None) rqid1.(rqi_rss)
    | None, Some rqid2 => Forall (fun rs => snd rs = None) rqid2.(rqi_rss)
    | None, None => True
    end.

  Definition NoRssChangeTrs (trs: OTrs) :=
    forall ost orq mins nost norq mouts,
      trs ost orq mins = (nost, norq, mouts) ->
      NoRssChange orq norq.

  Definition RssEquivRule (rule: Rule) :=
    RssEquivPrec (rule_precond rule) /\ RssEquivTrs (rule_trs rule) /\
    NoRsUpInputsPrec (rule_precond rule) /\
    NoRssChangeTrs (rule_trs rule).

  Definition ImplRulesR (oidx: IdxT) (rule: Rule) :=
    (RssEquivRule rule) \/
    (exists ridx msgId rqId prec trs, rule = rsRelease ridx msgId rqId prec trs) \/
    (exists ridx msgId rqId cidx,
        parentIdxOf topo cidx = Some oidx /\
        rule = rsTakeOne ridx msgId rqId cidx).

  Definition ImplRules :=
    forall iobj,
      In iobj impl.(sys_objs) ->
      (forall rule, In rule iobj.(obj_rules) -> ImplRulesR iobj.(obj_idx) rule) /\
      (forall ridx1 msgId1 cidx1 ridx2 msgId2 cidx2 rqId,
          In (rsTakeOne ridx1 msgId1 rqId cidx1) iobj.(obj_rules) ->
          In (rsTakeOne ridx2 msgId2 rqId cidx2) iobj.(obj_rules) ->
          msgId1 = msgId2).

  Definition SpecRulesInR (oidx: IdxT) (irules srules: list Rule) :=
    (forall rule, In rule irules -> RssEquivRule rule -> In rule srules) /\
    (forall ridx msgId rqId prec trs,
        In (rsRelease ridx msgId rqId prec trs) irules ->
        In (rsUpRule ridx~>1 msgId rqId prec trs) srules).

  Definition SpecRulesIn :=
    forall iobj,
      In iobj impl.(sys_objs) ->
      exists sobj,
        In sobj spec.(sys_objs) /\
        iobj.(obj_idx) = sobj.(obj_idx) /\
        SpecRulesInR iobj.(obj_idx) iobj.(obj_rules) sobj.(obj_rules).

  Hypotheses (Hir: ImplRules) (Hsr: SpecRulesIn).

  Definition implORqsInit: ORqs Msg :=
    initORqs (cifc.(c_li_indices) ++ cifc.(c_l1_indices)).

  Hypotheses (Hsi: impl.(sys_oss_inits) = spec.(sys_oss_inits))
             (Hoii: impl.(sys_orqs_inits) = implORqsInit)
             (Hosi: spec.(sys_orqs_inits) = implORqsInit).

  Section RssWfImp.
    Hypothesis (Hgss: GoodRqRsSys topo spec).

    Lemma RssWfInv_init: InvInit impl RssWfInv.
    Proof.
      repeat red; intros.
      simpl; rewrite Hoii.
      unfold implORqsInit; intros.
      destruct (in_dec idx_dec oidx (c_li_indices cifc ++ c_l1_indices cifc)).
      - rewrite initORqs_value by assumption.
        red; mred.
      - rewrite initORqs_None by assumption.
        auto.
    Qed.

    Lemma RssWfInv_ext_in:
      forall oss orqs msgs,
        RssWfInv {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
        forall eins,
          eins <> nil ->
          ValidMsgsExtIn impl eins ->
          RssWfInv {| st_oss := oss; st_orqs := orqs; st_msgs := enqMsgs eins msgs |}.
    Proof.
    Admitted.

    Lemma RssWfInv_ext_out:
      forall oss orqs msgs,
        RssWfInv {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
        forall eouts,
          eouts <> nil ->
          Forall (FirstMPI msgs) eouts ->
          ValidMsgsExtOut impl eouts ->
          RssWfInv {| st_oss := oss; st_orqs := orqs; st_msgs := deqMsgs (idsOf eouts) msgs |}.
    Proof.
    Admitted.

    Lemma RssWf_putRs:
      forall oidx rss,
        RssWf oidx rss ->
        forall cidx rmsg,
          parentIdxOf topo cidx = Some oidx ->
          RssWf oidx (putRs (rsUpFrom cidx) rmsg rss).
    Proof.
      induction rss; simpl; intros; auto.
      destruct a as [midx omsg]; simpl in *.
      destruct (idx_dec (rsUpFrom cidx) midx); subst.
    Admitted.

    Lemma RssWfORq_addRs:
      forall oidx porq,
        RssWfORq oidx porq ->
        forall cidx rmsg,
          parentIdxOf topo cidx = Some oidx ->
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

    Lemma RssWfInv_step: InvStep impl step_m RssWfInv.
    Proof.
      red; intros.

      inv H1;
        [assumption
        |apply RssWfInv_ext_in; assumption
        |apply RssWfInv_ext_out; assumption
        |].

      red in H0; simpl in H0.

      red; simpl; intros.
      mred; simpl; [|auto].
      specialize (H0 (obj_idx obj)).
      rewrite H6 in H0; simpl in H0.

      move Hsr at bottom.
      pose proof (Hsr _ H2) as [sobj [HsoIn [Hsoi Hsrr]]].
      destruct Hsrr as [Hsrr1 Hsrr2].
      specialize (Hsrr1 _ H3).

      pose proof (Hir _ H2) as [Hirr Hrst].
      specialize (Hirr _ H3).
      destruct Hirr as [|[|]].

      - (*! Normal rules *)
        admit.

      - (*! [RsRelease] *)
        clear Hrst Hsrr1.
        destruct H1 as [ridx [msgId [rqId [prec [trs ?]]]]]; subst rule.
        specialize (Hsrr2 _ _ _ _ _ H3).
        disc_rule_conds_ex.
        red; mred.

      - (*! [RsTakeOne] *)
        clear Hrst Hsrr1 Hsrr2 Hrst.
        destruct H1 as [ridx [msgId [rqId [cidx ?]]]]; dest; subst rule.
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

  Lemma mesi_rss_sim_init: sim (initsOf impl) (initsOf spec).
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

  Lemma mesi_rss_sim_silent:
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

  Lemma mesi_rss_sim_ext_in:
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

  Lemma mesi_rss_sim_ext_out:
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

  Theorem mesi_rss_sim_ok:
    InvSim step_m step_m RssWfInv sim impl spec.
  Proof.
    red; intros.
    rename H1 into Hwf. (* [RssWfInv ist1] *)
    clear H3. (* [RssWfInv ist2] *)

    inv H2;
      [apply mesi_rss_sim_silent; assumption
      |apply mesi_rss_sim_ext_in; assumption
      |apply mesi_rss_sim_ext_out; assumption
      |].

    destruct sst1 as [soss1 sorqs1 smsgs1].
    red in H0; simpl in H0; dest; subst.

    move Hsr at bottom.
    pose proof (Hsr _ H1) as [sobj [HsoIn [Hsoi Hsrr]]].
    destruct Hsrr as [Hsrr1 Hsrr2].
    specialize (Hsrr1 rule).

    pose proof (Hir _ H1) as [Hirr Hrst].
    specialize (Hirr _ H3).
    destruct Hirr as [|[|]].

    - (*! Normal rules *)
      clear Hrst Hsrr2.
      specialize (Hsrr1 H3 H0).

      disc_SimRssORqs obj.

      (* Discharge [RssEquivRule] to get the transition for the spec. *)
      pose proof H10.
      apply (proj1 (proj2 H0)) in H15.
      specialize (H15 _ H14).
      destruct H15 as [sorq2 [? ?]].

      do 2 eexists.
      repeat ssplit; [reflexivity|..].

      + econstructor.
        1-4: eassumption.
        { exact H13. }
        { eapply SimRssMP_NoRsUpInputs_first; eauto.
          apply H0 in H9; assumption.
        }
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
          apply SimRssMP_deqMsgs; [|apply H0 in H9; assumption].
          eapply SimRssMP_ORqs_change_silent; try eassumption.
          apply H0 in H10; assumption.

    - (*! [RsRelease] *)
      clear Hrst Hsrr1.
      destruct H0 as [ridx [msgId [rqId [prec [trs ?]]]]]; subst rule.
      specialize (Hsrr2 _ _ _ _ _ H3).

      disc_SimRssORqs obj.
      disc_RssWfInv obj.

      (* Discharge precondition and transition *)
      disc_rule_conds_ex.
      destruct ins; [clear H7 H8 H9 H12|discriminate].
      eapply RssFullWithId_spec in H16; [|eassumption].
      destruct H16 as [rqid [? [rss [? [? [? ?]]]]]]; subst rss.
      disc_RssWfORq obj.
      disc_rule_conds_ex.
      disc_RssORqEquiv.

      eexists (RlblInt _ _ _ _); eexists.
      repeat ssplit; [simpl; reflexivity|..].

      + econstructor.
        * eassumption.
        * eassumption.
        * reflexivity.
        * rewrite <-Hsoi; eassumption.
        * rewrite <-Hsoi; eassumption.
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
            rewrite <-H14, H8.
            rewrite map_map; reflexivity.
          }
          { assumption. }
          { red; rewrite H7; simpl.
            rewrite <-H13, Hmsg; simpl; split; [assumption|reflexivity].
          }
          { red; rewrite H7; simpl.
            rewrite <-H16, Hidx; simpl; auto.
          }
          { red; red in Hwfo; dest.
            apply Forall_forall; intros [rmidx rs] ?; simpl.
            apply in_map with (f:= fun idm => (idOf idm, Some (valOf idm))) in H22; simpl in H22.
            rewrite Forall_forall in H21; specialize (H21 _ H22).
            assumption.
          }
          { assumption. }

        * simpl; unfold TrsMTrs, getDownLockMsg, getDownLockIdxBack; simpl.
          rewrite H7; simpl.
          rewrite <-H13, Hmsg, <-H16, Hidx; simpl.
          reflexivity.
        * destruct H11.
          split; [|assumption].
          rewrite Himinds, Hierss in H11.
          rewrite Hsminds, Hserss; assumption.
        * red in Hwfo; dest.
          simpl; clear -H20 Hrsb.
          apply (DisjList_false_spec idx_dec).
          intros midx; intros; dest_in.
          rewrite Forall_forall in H20.
          apply in_map_iff in H; destruct H as [[rmidx rs] [? ?]]; simpl in *; subst.
          apply in_map with (f:= fun idm => (idOf idm, Some (valOf idm))) in H0.
          specialize (H20 _ H0).
          destruct H20 as [cidx [? ?]]; simpl in *; subst.
          elim (Hrsb cidx).
          { eapply parentIdxOf_not_eq; [|eassumption].
            apply tree2Topo_WfDTree.
          }
          { reflexivity. }
        * reflexivity.
        * reflexivity.

      + red; simpl; repeat ssplit; [congruence|..].
        * rewrite <-Hsoi.
          apply SimRssORqs_removeRq; [assumption|assumption|congruence].
        * eapply SimRssMP_enqMP.
          eapply SimRssMP_removeRq; eauto.
          { apply H12. }
          { rewrite H8; apply Hwfo. }

    - (*! [RsTakeOne] *)
      clear Hrst Hsrr1 Hsrr2 Hrst.
      destruct H0 as [ridx [msgId [rqId [cidx ?]]]]; dest; subst rule.
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

  Hypothesis (HwfInv: InvReachable impl step_m RssWfInv).
  Theorem mesi_ok:
    (steps step_m) # (steps step_m) |-- impl ⊑ spec.
  Proof.
    eapply invRSim_implies_refinement with (sim:= sim).
    - eassumption.
    - apply mesi_rss_sim_init.
    - apply mesi_rss_sim_ok.
  Qed.

End RssHolderOk.
