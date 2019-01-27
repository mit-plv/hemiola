Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvMsg.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section DownLockInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypotheses (Hrr: GoodRqRsSys dtr sys)
             (Hsd: RqRsDTree dtr sys).

  Section OnMState.
    Variables (orqs: ORqs Msg)
              (msgs: MessagePool Msg).

    Definition ODownLockedTo (oidx: IdxT) (rsbTo: IdxT) :=
      orqs@[oidx] >>=[False]
          (fun orq =>
             exists rqi,
               orq@[downRq] = Some rqi /\
               rqi.(rqi_midx_rsb) = rsbTo).
    
    Definition ODownLockFree (oidx: IdxT) :=
      orqs@[oidx] >>=[True] (fun orq => DownLockFreeORq orq).

    Definition ONoDownLockTo (oidx: IdxT) (rsbTo: IdxT) :=
      orqs@[oidx] >>=[True]
          (fun orq =>
             match orq@[downRq] with
             | Some rqi => rqi.(rqi_midx_rsb) <> rsbTo
             | None => True
             end).

    Definition DownLockFreeChildInv (cidx: IdxT) (down rsUp: IdxT) :=
      rqsQ msgs down = nil /\
      findQ rsUp msgs = nil /\
      ONoDownLockTo cidx rsUp.
    
    Definition DownLockedChildInv (cidx: IdxT) (down rsUp: IdxT) :=
      length (rqsQ msgs down) <= 1 /\
      length (findQ rsUp msgs) <= 1 /\
      xor3 (length (rqsQ msgs down) = 1)
           (length (findQ rsUp msgs) = 1)
           (ODownLockedTo cidx rsUp).
    
    Definition DownLockFreeInv (oidx: IdxT) :=
      forall cidx,
        parentIdxOf dtr cidx = Some oidx ->
        exists down rsUp,
          edgeDownTo dtr cidx = Some down /\ 
          rsEdgeUpFrom dtr cidx = Some rsUp /\
          DownLockFreeChildInv cidx down rsUp.
    
    Definition DownLockedInv (oidx: IdxT) (rqi: RqInfo Msg) :=
      forall cidx,
        parentIdxOf dtr cidx = Some oidx ->
        exists down rsUp,
          edgeDownTo dtr cidx = Some down /\ 
          rsEdgeUpFrom dtr cidx = Some rsUp /\
          if in_dec eq_nat_dec rsUp rqi.(rqi_minds_rss)
          then DownLockedChildInv cidx down rsUp
          else DownLockFreeChildInv cidx down rsUp.

    Definition DownLockInvORq (oidx: IdxT) (orq: ORq Msg) :=
      match orq@[downRq] with
      | Some downRqi => DownLockedInv oidx downRqi
      | None => DownLockFreeInv oidx
      end.

    Definition DownLockInvMO :=
      forall oidx,
        In oidx (map (@obj_idx _) sys.(sys_objs)) ->
        let orq := orqs@[oidx] >>=[[]] (fun orq => orq) in
        DownLockInvORq oidx orq.

  End OnMState.
  
  Definition DownLockInv (st: MState oifc) :=
    DownLockInvMO st.(bst_orqs) st.(bst_msgs).

  Lemma downLockInv_init:
    InvInit sys DownLockInv.
  Proof.
    intros; do 3 red; cbn.
    intros; cbn.
    red; intros.
    eapply parentIdxOf_Some in H0; [|eassumption].
    destruct H0 as [rqUp [rsUp [down ?]]]; dest.
    exists down, rsUp; repeat split; assumption.
  Qed.

  Lemma downLockFreeChildInv_msgs_preserved:
    forall orqs msgs1 msgs2 cidx down rsUp,
      edgeDownTo dtr cidx = Some down ->
      rsEdgeUpFrom dtr cidx = Some rsUp ->
      DownLockFreeChildInv orqs msgs1 cidx down rsUp ->
      rqsQ msgs1 down = rqsQ msgs2 down ->
      findQ rsUp msgs1 = findQ rsUp msgs2 ->
      DownLockFreeChildInv orqs msgs2 cidx down rsUp.
  Proof.
    unfold DownLockFreeChildInv; intros.
    dest; rewrite <-H2, <-H3.
    split; [|split]; assumption.
  Qed.
    
  Lemma downLockedChildInv_msgs_preserved:
    forall orqs msgs1 msgs2 cidx down rsUp,
      edgeDownTo dtr cidx = Some down ->
      rsEdgeUpFrom dtr cidx = Some rsUp ->
      DownLockedChildInv orqs msgs1 cidx down rsUp ->
      rqsQ msgs1 down = rqsQ msgs2 down ->
      findQ rsUp msgs1 = findQ rsUp msgs2 ->
      DownLockedChildInv orqs msgs2 cidx down rsUp.
  Proof.
    unfold DownLockedChildInv; intros.
    dest; rewrite <-H2, <-H3.
    split; [|split]; assumption.
  Qed.

  Lemma downLockFreeInv_msgs_preserved:
    forall orqs msgs1 msgs2 oidx,
      DownLockFreeInv orqs msgs1 oidx ->
      (forall cidx down rsUp,
          parentIdxOf dtr cidx = Some oidx ->
          edgeDownTo dtr cidx = Some down ->
          rsEdgeUpFrom dtr cidx = Some rsUp ->
          rqsQ msgs1 down = rqsQ msgs2 down /\
          findQ rsUp msgs1 = findQ rsUp msgs2) ->
      DownLockFreeInv orqs msgs2 oidx.
  Proof.
    unfold DownLockFreeInv; simpl; intros.
    specialize (H _ H1).
    destruct H as [down [rsUp ?]]; dest.
    exists down, rsUp.
    split; [|split]; try assumption.
    specialize (H0 _ _ _ H1 H H2); dest.
    eapply downLockFreeChildInv_msgs_preserved; eauto.
  Qed.
  
  Corollary downLockFreeInv_disj_enqMsgs_preserved:
    forall orqs msgs emsgs oidx,
      DownLockFreeInv orqs msgs oidx ->
      DisjList (idsOf emsgs) (sys_minds sys) ->
      DownLockFreeInv orqs (enqMsgs emsgs msgs) oidx.
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

  Lemma downLockFreeInv_disj_deqMsgs_preserved:
    forall orqs msgs eminds oidx,
      DownLockFreeInv orqs msgs oidx ->
      DisjList eminds (sys_minds sys) ->
      DownLockFreeInv orqs (deqMsgs eminds msgs) oidx.
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
  
  Lemma downLockedInv_msgs_preserved:
    forall orqs msgs1 msgs2 oidx rqi,
      DownLockedInv orqs msgs1 oidx rqi ->
      (forall rsUp down cidx,
          parentIdxOf dtr cidx = Some oidx ->
          edgeDownTo dtr cidx = Some down ->
          rsEdgeUpFrom dtr cidx = Some rsUp ->
          rqsQ msgs1 down = rqsQ msgs2 down /\
          findQ rsUp msgs1 = findQ rsUp msgs2) ->
      DownLockedInv orqs msgs2 oidx rqi.
  Proof.
    unfold DownLockedInv; simpl; intros.
    specialize (H _ H1).
    destruct H as [down [rsUp ?]]; dest.
    specialize (H0 _ _ _ H1 H H2); dest.
    exists down, rsUp.
    split; [|split]; try assumption.
    find_if_inside.
    - eapply downLockedChildInv_msgs_preserved; eauto.
    - eapply downLockFreeChildInv_msgs_preserved; eauto.
  Qed.
  
  Corollary downLockedInv_disj_enqMsgs_preserved:
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

  Corollary downLockedInv_disj_deqMsgs_preserved:
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

  Lemma downLockedChildInv_orqs_preserved_self_update:
    forall orqs msgs cidx down rsUp oidx orq,
      parentIdxOf dtr cidx = Some oidx ->
      DownLockedChildInv orqs msgs cidx down rsUp ->
      DownLockedChildInv (orqs+[oidx <- orq]) msgs cidx down rsUp.
  Proof.
    intros; destruct Hsd.
    red in H0; dest.
    repeat split; try assumption.
    unfold ODownLockedTo in *.
    apply parentIdxOf_not_eq in H; [|assumption].
    mred.
  Qed.
    
  Lemma downLockFreeChildInv_orqs_preserved_self_update:
    forall orqs msgs cidx down rsUp oidx orq,
      parentIdxOf dtr cidx = Some oidx ->
      DownLockFreeChildInv orqs msgs cidx down rsUp ->
      DownLockFreeChildInv (orqs+[oidx <- orq]) msgs cidx down rsUp.
  Proof.
    intros; destruct Hsd.
    red in H0; dest.
    repeat split; try assumption.
    unfold ONoDownLockTo in *.
    apply parentIdxOf_not_eq in H; [|assumption].
    mred.
  Qed.

  Lemma downLockedInv_orqs_preserved_self_update:
    forall orqs msgs oidx orq rqid,
      DownLockedInv orqs msgs oidx rqid ->
      DownLockedInv (orqs+[oidx <- orq]) msgs oidx rqid.
  Proof.
    intros.
    red in H; red; intros.
    specialize (H _ H0).
    destruct H as [down [rsUp ?]]; dest.
    exists down, rsUp.
    repeat split; try assumption.
    find_if_inside.
    - apply downLockedChildInv_orqs_preserved_self_update; auto.
    - apply downLockFreeChildInv_orqs_preserved_self_update; auto.
  Qed.

  Lemma downLockFreeInv_orqs_preserved_self_update:
    forall orqs msgs oidx orq,
      DownLockFreeInv orqs msgs oidx ->
      DownLockFreeInv (orqs+[oidx <- orq]) msgs oidx.
  Proof.
    intros.
    red in H; red; intros.
    specialize (H _ H0).
    destruct H as [down [rsUp ?]]; dest.
    exists down, rsUp.
    split; [|split]; try assumption.
    apply downLockFreeChildInv_orqs_preserved_self_update; auto.
  Qed.

  Lemma downLockedChildInv_requested:
    forall oidx cidx down rsUp porq P orqs msgs mouts rqi,
      parentIdxOf dtr cidx = Some oidx ->
      edgeDownTo dtr cidx = Some down ->
      rsEdgeUpFrom dtr cidx = Some rsUp ->
      DownLockFreeChildInv orqs msgs cidx down rsUp ->
      In rsUp (rqi_minds_rss rqi) ->      
      NoDup (idsOf mouts) ->
      Forall (fun idm => msg_type (valOf idm) = MRq) mouts ->
      RqRsDownMatch dtr oidx (idsOf mouts) (rqi_minds_rss rqi) P ->
      DownLockedChildInv (orqs +[oidx <- porq +[ downRq <- rqi]])
                         (enqMsgs mouts msgs) cidx down rsUp.
  Proof.
    intros; destruct Hsd.
    red in H2; dest; red.

    assert (length (rqsQ (enqMsgs mouts msgs) down) = 1).
    { eapply RqRsDownMatch_rq_rs in H6; eauto.
      apply H6 in H3.
      apply in_map_iff in H3.
      destruct H3 as [[midx msg] ?]; dest; simpl in *; subst.
      rewrite Forall_forall in H5.
      specialize (H5 _ H11); simpl in H5.
      unfold rqsQ.
      erewrite findQ_In_NoDup_enqMsgs; eauto.
      rewrite filter_app; simpl.
      rewrite H5; simpl.
      unfold rqsQ in H2; rewrite H2.
      reflexivity.
    }

    assert (length (findQ rsUp (enqMsgs mouts msgs)) = 0).
    { solve_q; rewrite H9; reflexivity. }

    rewrite H11, H12.
    repeat split; try omega.
    xfst; [reflexivity|discriminate|].

    apply parentIdxOf_not_eq in H; [|assumption].
    intro Hx; red in H10, Hx.
    mred.
    destruct (orqs@[cidx]) as [corq|]; auto.
    simpl in H10, Hx.
    destruct Hx as [crqi [? ?]].
    rewrite H13 in H10; auto.
  Qed.

  Lemma downLockedInv_requested:
    forall orqs msgs oidx mouts P rqi porq,
      DownLockFreeInv orqs msgs oidx ->
      RqRsDownMatch dtr oidx (idsOf mouts) (rqi_minds_rss rqi) P ->
      NoDup (idsOf mouts) ->
      Forall (fun idm : Id Msg => msg_type (valOf idm) = MRq) mouts ->
      DownLockedInv (orqs +[oidx <- porq +[downRq <- rqi]])
                    (enqMsgs mouts msgs) oidx rqi.
  Proof.
    intros.
    red in H; red; intros.
    specialize (H _ H3).
    destruct H as [down [rsUp ?]]; dest.
    exists down, rsUp.
    repeat split; try assumption.
    find_if_inside.
    * eapply downLockedChildInv_requested; try eassumption.
    * eapply downLockFreeChildInv_orqs_preserved_self_update; [assumption|].
      eapply downLockFreeChildInv_msgs_preserved;
        try eassumption; solve_q.
  Qed.

  Lemma downLockFreeChildInv_responded:
    forall orqs msgs oidx rqi mins rqTos P porq,
      DownLockedInv orqs msgs oidx rqi ->
      NoDup (idsOf mins) ->
      Forall (FirstMPI msgs) mins ->
      Forall (fun idm => msg_type (valOf idm) = MRs) mins ->
      RqRsDownMatch dtr oidx rqTos (idsOf mins) P ->
      idsOf mins = rqi.(rqi_minds_rss) ->
      DownLockFreeInv (orqs +[oidx <- porq -[downRq]])
                      (deqMsgs (idsOf mins) msgs) oidx.
  Proof.
    intros.
    apply downLockFreeInv_orqs_preserved_self_update.

    red in H; red; intros.
    specialize (H _ H5).
    destruct H as [down [rsUp ?]]; dest.
    exists down, rsUp.
    split; [|split]; try assumption.

    find_if_inside.
    - red in H7; dest.
      rewrite <-H4 in i; apply in_map_iff in i.
      destruct i as [[rsUp' rsum] [? ?]]; simpl in *; subst.
      pose proof H1.
      rewrite Forall_forall in H10.
      specialize (H10 _ H11).
      assert (length (findQ rsUp msgs) = 1) by (eapply findQ_length_one; eauto).
      eapply xor3_inv_2 with (B:= length (findQ rsUp msgs) = 1) in H9;
        [dest|assumption].
      red; split; [|split].
      { rewrite rqsQ_deqMsgs_rss; try assumption.
        destruct (rqsQ msgs down); [reflexivity|simpl in *; omega].
      }
      { apply in_map with (f:= idOf) in H11; simpl in H11.
        assert (findQ rsUp msgs <> nil) by (destruct (findQ rsUp msgs); discriminate).
        eapply findQ_In_NoDup_deqMsgs in H14; try eassumption.
        destruct H14 as [dmsg ?].
        rewrite <-H14 in H12.
        destruct (findQ rsUp (deqMsgs _ _)); [reflexivity|discriminate].
      }
      { unfold ODownLockedTo in H13.
        red; destruct (orqs@[cidx]) as [corq|]; simpl in *; auto.
        destruct (corq@[downRq]) as [crqi|]; auto.
        intro Hx; elim H13; eauto.
      }
    - eapply downLockFreeChildInv_msgs_preserved; try eassumption.
      + solve_q.
      + rewrite findQ_not_In_deqMsgs; auto.
        rewrite H4; assumption.
  Qed.
  
  Lemma downLockInv_step_ext_in:
    forall oss orqs msgs eins,
      DownLockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      eins <> nil ->
      ValidMsgsExtIn sys eins ->
      DownLockInv {| bst_oss := oss;
                     bst_orqs := orqs;
                     bst_msgs := enqMsgs eins msgs |}.
  Proof.
    unfold DownLockInv; simpl; intros.
    red; intros.
    specialize (H oidx H2).
    destruct H1.
    assert (DisjList (idsOf eins) (sys_minds sys)).
    { eapply DisjList_SubList; eauto.
      apply DisjList_comm.
      apply sys_minds_sys_merqs_DisjList.
    }
    destruct (orqs@[oidx]) as [orq|]; simpl in *; dest.
    - red in H; red.
      remember (orq@[downRq]) as orqi.
      destruct orqi as [rqi|].
      + apply downLockedInv_disj_enqMsgs_preserved; assumption.
      + apply downLockFreeInv_disj_enqMsgs_preserved; assumption.
    - red in H; simpl in H.
      red in H3; simpl in H3.
      red; simpl.
      apply downLockFreeInv_disj_enqMsgs_preserved; assumption.
  Qed.

  Lemma downLockInv_step_ext_out:
    forall oss orqs msgs eouts,
      DownLockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      eouts <> nil ->
      Forall (FirstMPI msgs) eouts ->
      ValidMsgsExtOut sys eouts ->
      DownLockInv {| bst_oss := oss;
                     bst_orqs := orqs;
                     bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    unfold DownLockInv; simpl; intros.
    red; intros.
    specialize (H oidx H3).
    destruct H2.
    assert (DisjList (idsOf eouts) (sys_minds sys)).
    { eapply DisjList_SubList; eauto.
      apply DisjList_comm.
      apply sys_minds_sys_merss_DisjList.
    }
    destruct (orqs@[oidx]) as [orq|]; simpl in *; dest.
    - red in H; red.
      remember (orq@[downRq]) as orqi.
      destruct orqi as [rqi|].
      + apply downLockedInv_disj_deqMsgs_preserved; assumption.
      + apply downLockFreeInv_disj_deqMsgs_preserved; assumption.
    - red in H; simpl in H.
      red in H4; simpl in H4.
      red; simpl.
      apply downLockFreeInv_disj_deqMsgs_preserved; assumption.
  Qed.

  Section InternalStep.
    Variables (oss: OStates oifc) (orqs: ORqs Msg) (msgs: MessagePool Msg)
              (obj: Object oifc) (rule: Rule oifc)
              (post: OState oifc) (porq: ORq Msg) (mins: list (Id Msg))
              (nost: OState oifc) (norq: ORq Msg) (mouts: list (Id Msg)).

    Hypotheses
      (Hfpok: FootprintsOk
                dtr sys {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |})
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

    Ltac disc_rule_custom ::=
      match goal with
      | [H: FootprintUpOkEx _ _ _ /\ _ |- _] => destruct H
      | [H: _ /\ FootprintDownOkEx _ _ _ _ |- _] => destruct H
      | [H: FootprintUpOkEx _ _ _ |- _] =>
        let rqFrom := fresh "rqFrom" in
        let rqTo := fresh "rqTo" in
        let rsFrom := fresh "rsFrom" in
        let rsbTo := fresh "rsbTo" in
        destruct H as [rqFrom [rqTo [rsFrom [rsbTo ?]]]]; dest
      | [H: FootprintUpOk _ _ _ _ _ _ |- _] =>
        let cidx := fresh "cidx" in
        destruct H as [cidx ?]; dest

      | [H: FootprintDownOkEx _ _ _ _ |- _] =>
        let rqFrom := fresh "rqFrom" in
        let rqTos := fresh "rqTos" in
        let rssFrom := fresh "rssFrom" in
        let rsbTo := fresh "rsbTo" in
        destruct H as [rqFrom [rqTos [rssFrom [rsbTo ?]]]]; dest
      | [H: FootprintUpDownOk _ _ _ _ _ _ _ \/
            FootprintDownDownOk _ _ _ _ _ _ |- _] => destruct H
      | [H: exists _, FootprintUpDownOk _ _ _ _ _ _ _ |- _] =>
        let rqFrom := fresh "rqFrom" in
        destruct H as [rqFrom ?]
      | [H: FootprintUpDownOk _ _ _ _ _ _ _ |- _] =>
        let upCIdx := fresh "upCIdx" in
        let upCObj := fresh "upCObj" in
        destruct H as [upCIdx [upCObj ?]]; dest
      | [H: FootprintDownDownOk _ _ _ _ _ _ |- _] => red in H; dest
      end.

    Lemma downLockInvORq_step_int_me:
      DownLockInvORq orqs msgs (obj_idx obj) porq ->
      In (obj_idx obj) (map (@obj_idx _) (sys_objs sys)) ->
      GoodRqRsRule dtr sys (obj_idx obj) rule ->
      DownLockInvORq (orqs+[obj_idx obj <- norq])
                     (enqMsgs mouts (deqMsgs (idsOf mins) msgs))
                     (obj_idx obj) norq.
    Proof.
      intros.
      destruct Hsd.
      red in H; red.
      good_rqrs_rule_cases rule.

      - (** case [ImmDownRule] *)
        disc_rule_conds.
        apply downLockFreeInv_orqs_preserved_self_update.
        eapply downLockFreeInv_msgs_preserved; eauto.
        intros; split; intros.
        + rewrite rqsQ_enqMP_rs by assumption.
          solve_q.
        + solve_q.

      - (** case [ImmUpRule] *)
        disc_rule_conds.
        apply downLockFreeInv_orqs_preserved_self_update.
        eapply downLockFreeInv_msgs_preserved; eauto.
        intros; split; intros; solve_q.

      - (** case [RqFwdRule] *)
        disc_rule_conds.
        + (** case [RqUpUp] *)
          destruct (porq@[downRq]) as [rqid|].
          * apply downLockedInv_orqs_preserved_self_update.
            eapply downLockedInv_msgs_preserved; eauto.
            intros; split; intros; solve_q.
          * apply downLockFreeInv_orqs_preserved_self_update.
            eapply downLockFreeInv_msgs_preserved; eauto.
            intros; split; intros; solve_q.
        + (** case [RqUpDown] *)
          destruct HmoutsV.
          eapply downLockedInv_requested; eauto.
          eapply downLockFreeInv_msgs_preserved; [eassumption|].
          intros; split; solve_q.
        + (** case [RqDownDown] *)
          destruct HmoutsV.
          eapply downLockedInv_requested; eauto.
          eapply downLockFreeInv_msgs_preserved; [eassumption|].
          intros; split; solve_q.

      - (** case [RsBackRule] *)
        good_footprint_get (obj_idx obj).
        disc_rule_conds.
        + (** case [RsDownDown] *)
          apply downLockFreeInv_orqs_preserved_self_update.
          eapply downLockFreeInv_msgs_preserved; eauto.
          intros; split; intros.
          * rewrite rqsQ_enqMP_rs by assumption.
            solve_q.
          * solve_q.
        + (** case [RsUp(Down)] *)
          eapply downLockFreeInv_msgs_preserved.
          * destruct HminsV.
            rewrite <-H17 in H11.
            eapply downLockFreeChildInv_responded; eauto.
          * intros; split.
            { rewrite rqsQ_enqMP_rs; [reflexivity|assumption]. }
            { solve_q. }
        + (** case [RsUp(Up)] *)
          eapply downLockFreeInv_msgs_preserved.
          * destruct HminsV.
            rewrite <-H17 in H6.
            eapply downLockFreeChildInv_responded; eauto.
          * intros; split.
            { rewrite rqsQ_enqMP_rs; [reflexivity|assumption]. }
            { solve_q. }

      - (** case [RsDownRqDownRule] *)
        disc_rule_conds.
        destruct HmoutsV.
        eapply downLockedInv_requested; eauto.
        eapply downLockFreeInv_msgs_preserved; [eassumption|].
        intros; split; solve_q.
    Qed.

    Lemma downLockInvORq_step_int_child:
      forall oidx,
        DownLockInvORq orqs msgs oidx ((orqs@[oidx]) >>=[[]] (fun orq => orq)) ->
        In oidx (map (@obj_idx _) (sys_objs sys)) ->
        GoodRqRsRule dtr sys (obj_idx obj) rule ->
        parentIdxOf dtr (obj_idx obj) = Some oidx ->
        DownLockInvORq (orqs+[obj_idx obj <- norq])
                     (enqMsgs mouts (deqMsgs (idsOf mins) msgs)) oidx
                     ((orqs@[ oidx]) >>=[[]] (fun orq => orq)).
    Proof.
    Admitted.

    Lemma downLockInvORq_step_int_other:
      forall oidx,
        DownLockInvORq orqs msgs oidx ((orqs@[oidx]) >>=[[]] (fun orq => orq)) ->
        In oidx (map (@obj_idx _) (sys_objs sys)) ->
        GoodRqRsRule dtr sys (obj_idx obj) rule ->
        oidx <> obj_idx obj ->
        parentIdxOf dtr (obj_idx obj) <> Some oidx ->
        DownLockInvORq (orqs+[obj_idx obj <- norq])
                       (enqMsgs mouts (deqMsgs (idsOf mins) msgs)) oidx
                       ((orqs@[ oidx]) >>=[[]] (fun orq => orq)).
    Proof.
      intros.
      destruct Hsd.
      red in H; red.
      good_rqrs_rule_cases rule.

      - (** case [ImmDownRule] *)
        disc_rule_conds.
        destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
      
    Admitted.

    Lemma downLockInv_step_int:
      DownLockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      DownLockInv {| bst_oss := (oss) +[ obj_idx obj <- nost];
                     bst_orqs := (orqs) +[ obj_idx obj <- norq];
                     bst_msgs := enqMsgs mouts (deqMsgs (idsOf mins) msgs) |}.
    Proof.
      intros.
      do 2 red; simpl; intros.
      good_rqrs_rule_get rule.
      specialize (H _ H0); simpl in H; dest.

      M.cmp (obj_idx obj) oidx; mred; simpl in *.
      - (** case [oidx = obj_idx obj] *)
        apply downLockInvORq_step_int_me; assumption.
      - (** case [oidx <> obj_idx obj] *)
        remember (parentIdxOf dtr (obj_idx obj)) as opidx.
        destruct opidx as [pidx|].
        + destruct (eq_nat_dec oidx pidx); subst.
          * apply downLockInvORq_step_int_child; auto.
          * apply downLockInvORq_step_int_other; auto.
            rewrite <-Heqopidx.
            intro Hx; elim n0; inv Hx; reflexivity.
        + apply downLockInvORq_step_int_other; auto.
          rewrite <-Heqopidx; discriminate.
    Qed.

  End InternalStep.

  Lemma downLockInv_step:
    InvStep sys step_m DownLockInv.
  Proof.
    red; intros.
    inv H1.
    - auto.
    - apply downLockInv_step_ext_in; auto.
    - apply downLockInv_step_ext_out; auto.
    - eapply downLockInv_step_int; eauto.
      eapply footprints_ok; eassumption.
  Qed.

  Lemma downLockInv_ok:
    InvReachable sys step_m DownLockInv.
  Proof.
    apply inv_reachable.
    - apply downLockInv_init.
    - apply downLockInv_step.
  Qed.
  
End DownLockInv.

Close Scope list.
Close Scope fmap.

