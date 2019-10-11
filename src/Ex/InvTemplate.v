Require Import List FMap Lia.
Require Import Common Topology ListSupport IndexSupport.
Require Import Syntax MessagePool Semantics StepM Invariant.
Require Import RqRsLang.

Require Import Ex.TopoTemplate Ex.RuleTemplate.

Import PropMonadNotations.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

(** Common Invariants that might be shared among various protocols *)

Definition MsgExistsSig (sig: MSig) (msgs: MessagePool Msg) :=
  exists idm, InMPI msgs idm /\ sigOf idm = sig.

Definition MsgP (spl: list (MSig * (Id Msg -> Prop))) (idm: Id Msg) :=
  caseDec sig_dec (sigOf idm) True
          (map (fun sp => (fst sp, snd sp idm)) spl).

Definition MsgsP (spl: list (MSig * (Id Msg -> Prop))) (msgs: MessagePool Msg) :=
  forall idm, InMPI msgs idm -> MsgP spl idm.

Definition MsgsNotExist (sigs: list MSig) (msgs: MessagePool Msg) :=
  MsgsP (map (fun sig => (sig, fun _ => False)) sigs) msgs.

Section InObjInds.
  Variable (tr: tree) (bidx: IdxT).
  Let topo := fst (tree2Topo tr bidx).
  Let cifc := snd (tree2Topo tr bidx).

  Context `{OStateIfc}.
  Variable (sys: System).

  Definition InObjInds (st: MState) :=
    forall oidx,
      _ <+- (bst_oss st)@[oidx];
        In oidx (c_li_indices cifc ++ c_l1_indices cifc).

  Hypothesis (Hinit: InObjInds (initsOf sys))
             (Hinds: SubList (map obj_idx (sys_objs sys))
                             (c_li_indices cifc ++ c_l1_indices cifc)).

  Lemma tree2Topo_InObjInds_step:
    InvStep sys step_m InObjInds.
  Proof.
    red; intros.
    inv H2; [assumption..|].
    red; simpl; intros.
    mred; auto.
    simpl.
    apply Hinds.
    apply in_map; assumption.
  Qed.
  
  Lemma tree2Topo_InObjInds_inv_ok:
    InvReachable sys step_m InObjInds.
  Proof.
    apply inv_reachable.
    - apply Hinit.
    - apply tree2Topo_InObjInds_step.
  Qed.

End InObjInds.

Section MsgConflicts.

  Definition RsDownConflicts (oidx: IdxT) (orq: ORq Msg) (msgs: MessagePool Msg) :=
    forall rsDown,
      fst (sigOf rsDown) = downTo oidx ->
      fst (snd (sigOf rsDown)) = MRs ->
      InMPI msgs rsDown ->
      (orq@[upRq] <> None) /\
      (forall rqUp,
          fst (sigOf rqUp) = rqUpFrom oidx ->
          InMPI msgs rqUp -> False) /\
      (forall rrsDown,
          fst (sigOf rrsDown) = downTo oidx ->
          fst (snd (sigOf rrsDown)) = MRs ->
          valOf rsDown <> valOf rrsDown ->
          InMPI msgs rrsDown -> False) /\
      (forall rqDown,
          fst (sigOf rqDown) = downTo oidx ->
          fst (snd (sigOf rqDown)) = MRq ->
          FirstMPI msgs rqDown -> False) /\
      (forall rsUp,
          fst (sigOf rsUp) = rsUpFrom oidx ->
          InMPI msgs rsUp -> False).

  Definition RqUpConflicts (oidx: IdxT) (orq: ORq Msg) (msgs: MessagePool Msg) :=
    forall rqUp,
      fst (sigOf rqUp) = rqUpFrom oidx ->
      InMPI msgs rqUp ->
      (orq@[upRq] <> None) /\
      (forall rrqUp,
          fst (sigOf rrqUp) = rqUpFrom oidx ->
          valOf rqUp <> valOf rrqUp ->
          InMPI msgs rrqUp -> False) /\
      (forall rsDown,
          fst (sigOf rsDown) = downTo oidx ->
          fst (snd (sigOf rsDown)) = MRs ->
          InMPI msgs rsDown -> False).

  Definition RqDownConflicts (oidx: IdxT) (porq: ORq Msg) (msgs: MessagePool Msg) :=
    forall rqDown,
      fst (sigOf rqDown) = downTo oidx ->
      fst (snd (sigOf rqDown)) = MRq ->
      InMPI msgs rqDown ->
      (porq@[downRq] <> None) /\
      (forall rrqDown,
          fst (sigOf rrqDown) = downTo oidx ->
          fst (snd (sigOf rrqDown)) = MRq ->
          valOf rqDown <> valOf rrqDown ->
          InMPI msgs rrqDown -> False) /\
      (forall rsUp,
          fst (sigOf rsUp) = rsUpFrom oidx ->
          InMPI msgs rsUp -> False).

  Definition RsUpConflicts (oidx: IdxT) (porq: ORq Msg) (msgs: MessagePool Msg) :=
    forall rsUp,
      fst (sigOf rsUp) = rsUpFrom oidx ->
      InMPI msgs rsUp ->
      (porq@[downRq] <> None) /\
      (forall rqDown,
          fst (sigOf rqDown) = downTo oidx ->
          fst (snd (sigOf rqDown)) = MRq ->
          InMPI msgs rqDown -> False) /\
      (forall rrsUp,
          fst (sigOf rrsUp) = rsUpFrom oidx ->
          valOf rsUp <> valOf rrsUp ->
          InMPI msgs rrsUp -> False).

  Definition ParentLockConflicts (orqs: ORqs Msg) (oidx pidx: IdxT) (msgs: MessagePool Msg) :=
    OLockedTo orqs pidx (Some (downTo oidx)) ->
    (forall rsDown,
        fst (sigOf rsDown) = downTo oidx ->
        fst (snd (sigOf rsDown)) = MRs ->
        InMPI msgs rsDown ->
        False) /\
    (forall rqUp,
        fst (sigOf rqUp) = rqUpFrom oidx ->
        InMPI msgs rqUp ->
        False) /\
    (forall orq,
        orqs@[oidx] = Some orq ->
        orq@[upRq] = None ->
        False).

  Variable (tr: tree) (bidx: IdxT).
  Hypothesis (Htr: tr <> Node nil).
  Let topo := fst (tree2Topo tr bidx).
  Let cifc := snd (tree2Topo tr bidx).

  Context `{OStateIfc}.
  Variable (sys: System).
  
  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hrrs: RqRsSys topo sys)
             (Hoinds: SubList (c_li_indices cifc ++ c_l1_indices cifc)
                              (map (@obj_idx _) (sys_objs sys))).

  Definition RootChnInv (st: MState) :=
    forall idm,
      (idOf idm = downTo (rootOf topo) \/
       idOf idm = rqUpFrom (rootOf topo) \/
       idOf idm = rsUpFrom (rootOf topo)) ->
      ~ InMPI (bst_msgs st) idm.
  
  Definition MsgConflictsInv (st: MState) :=
    forall oidx orq,
      In oidx (c_li_indices cifc ++ c_l1_indices cifc) ->
      (bst_orqs st)@[oidx] = Some orq ->
      RsDownConflicts oidx orq (bst_msgs st) /\
      RqUpConflicts oidx orq (bst_msgs st) /\
      (forall pidx,
          parentIdxOf topo oidx = Some pidx ->
          ParentLockConflicts (bst_orqs st) oidx pidx (bst_msgs st) /\
          (forall porq,
              (bst_orqs st)@[pidx] = Some porq ->
              RqDownConflicts oidx porq (bst_msgs st) /\
              RsUpConflicts oidx porq (bst_msgs st))).

  Lemma tree2Topo_MsgConflicts_inv_ok:
    forall (Hrcinv: InvReachable sys step_m RootChnInv),
      InvReachable sys step_m MsgConflictsInv.
  Proof.
    unfold InvReachable, MsgConflictsInv; intros.
    specialize (Hrcinv _ H0).

    unfold cifc in H1.
    rewrite c_li_indices_head_rootOf in H1 by assumption.
    inv H1.

    1: { (* the root case *)
      repeat ssplit.
      { red; intros; exfalso.
        eapply Hrcinv; eauto.
        left; assumption.
      }
      { red; intros; exfalso.
        eapply Hrcinv; eauto.
        right; left; assumption.
      }
      { intros.
        exfalso; apply parentIdxOf_child_not_root in H1; auto.
        apply tree2Topo_WfDTree.
      }
    }

    (* non-root cases *)
    assert (exists pidx,
               In pidx (c_li_indices cifc) /\
               parentIdxOf topo oidx = Some pidx).
    { apply in_app_or in H3; destruct H3.
      { apply c_li_indices_tail_has_parent; assumption. }
      { apply c_l1_indices_has_parent; assumption. }
    }
    destruct H1 as [pidx [? ?]].

    pose proof (tree2Topo_TreeTopo tr bidx).
    destruct H5; dest.
    specialize (H5 _ _ H4); dest.

    assert (exists obj, In obj (sys_objs sys) /\ obj_idx obj = oidx).
    { apply in_app_or in H3; destruct H3.
      { apply tl_In in H3.
        apply SubList_app_4 in Hoinds; apply Hoinds in H3.
        apply in_map_iff in H3; destruct H3 as [obj [? ?]]; subst.
        exists obj; auto.
      }
      { apply SubList_app_5 in Hoinds; apply Hoinds in H3.
        apply in_map_iff in H3; destruct H3 as [obj [? ?]]; subst.
        exists obj; auto.
      }
    }
    destruct H10 as [obj [? ?]]; subst.

    assert (exists pobj, In pobj (sys_objs sys) /\ obj_idx pobj = pidx).
    { apply SubList_app_4 in Hoinds; apply Hoinds in H1.
      apply in_map_iff in H1; destruct H1 as [pobj [? ?]]; subst.
      exists pobj; auto.
    }
    destruct H11 as [pobj [? ?]]; subst.

    repeat ssplit.
    - red; intros; repeat ssplit; intros.
      + intro Hx.
        eapply upLockFree_rsDown_in_false
          with (obj0:= obj) (down:= downTo (obj_idx obj))
               (rsdm:= valOf rsDown); eauto.
        unfold sigOf in H12; simpl in H12; red in H14; rewrite H12 in H14; assumption.
      + eapply rqUp_in_rsDown_in_false
          with (obj0:= obj) (rqUp0:= rqUpFrom (obj_idx obj)) (rqum:= valOf rqUp)
               (down:= downTo (obj_idx obj)) (rsdm:= valOf rsDown); eauto.
        * unfold sigOf in H15; simpl in H15; red in H16; rewrite H15 in H16; assumption.
        * unfold sigOf in H12; simpl in H12; red in H14; rewrite H12 in H14; assumption.
      + eapply rsDown_in_rsDown_in_false
          with (obj0:= obj) (down:= downTo (obj_idx obj))
               (rsdm1:= valOf rsDown) (rsdm2:= valOf rrsDown); eauto.
        * unfold sigOf in H12; simpl in H12; red in H14; rewrite H12 in H14; assumption.
        * unfold sigOf in H15; simpl in H15; red in H18; rewrite H15 in H18; assumption.
      + eapply rsDown_in_rqDown_first_false
          with (cobj:= obj) (pobj0:= pobj) (down:= downTo (obj_idx obj))
               (rsdm:= valOf rsDown) (rqdm:= valOf rqDown); eauto.
        * unfold sigOf in H12; simpl in H12; red in H14; rewrite H12 in H14; assumption.
        * unfold sigOf in H15; simpl in H15; red in H17; rewrite H15 in H17; assumption.
      + eapply rsDown_in_rsUp_in_false
          with (cobj:= obj) (pobj0:= pobj) (rsUp0:= rsUpFrom (obj_idx obj))
               (down:= downTo (obj_idx obj))
               (rsdm:= valOf rsDown) (rsum:= valOf rsUp); eauto.
        * unfold sigOf in H12; simpl in H12; red in H14; rewrite H12 in H14; assumption.
        * unfold sigOf in H15; simpl in H15; red in H16; rewrite H15 in H16; assumption.

    - red; intros; repeat ssplit; intros.
      + intro Hx.
        eapply upLockFree_rqUp_in_false
          with (obj0:= obj) (rqUp0:= rqUpFrom (obj_idx obj))
               (rqum:= valOf rqUp); eauto.
        unfold sigOf in H12; simpl in H12; red in H13; rewrite H12 in H13; assumption.
      + eapply rqUp_in_rqUp_in_false
          with (obj0:= obj) (rqUp0:= rqUpFrom (obj_idx obj))
               (rqum1:= valOf rqUp) (rqum2:= valOf rrqUp); eauto.
        * unfold sigOf in H12; simpl in H12; red in H13; rewrite H12 in H13; assumption.
        * unfold sigOf in H14; simpl in H14; red in H16; rewrite H14 in H16; assumption.
      + eapply rqUp_in_rsDown_in_false
          with (obj0:= obj) (rqUp0:= rqUpFrom (obj_idx obj)) (rqum:= valOf rqUp)
               (down:= downTo (obj_idx obj)) (rsdm:= valOf rsDown); eauto.
        * unfold sigOf in H12; simpl in H12; red in H13; rewrite H12 in H13; assumption.
        * unfold sigOf in H14; simpl in H14; red in H16; rewrite H14 in H16; assumption.

    - intros; split.
      + red; intros; repeat ssplit.
        * intros.
          disc_rule_conds.
          eapply rsDown_parent_locked_false with (obj0:= obj); eauto.
          destruct rsDown as [rsDown rsdm]; simpl in *; subst; assumption.
        * intros.
          disc_rule_conds.
          eapply rqUp_parent_locked_false with (obj0:= obj); eauto.
          destruct rqUp as [rqUp rqum]; simpl in *; subst; eassumption.
        * intros.
          disc_rule_conds.
          eapply upLockFree_parent_locked_false with (obj0:= obj); eauto.

      + intros; split.
        * red; intros.
          disc_rule_conds.
          repeat ssplit; intros.
          { intro Hx.
            eapply downLockFree_rqDown_in_false
              with (pobj0:= pobj) (rqDown0:= downTo (obj_idx obj))
                   (rqdm:= valOf rqDown); eauto.
            destruct rqDown as [rqDown rqdm]; simpl in *; subst; assumption.
          }
          { eapply rqDown_in_rqDown_in_false
              with (pobj0:= pobj) (rqDown0:= downTo (obj_idx obj))
                   (rqdm1:= valOf rqDown) (rqdm2:= valOf rrqDown); eauto.
            { destruct rqDown as [rqDown rqdm]; simpl in *; subst; assumption. }
            { destruct rrqDown as [rrqDown rqdm]; simpl in *; subst; assumption. }
          }
          { eapply rqDown_in_rsUp_in_false
              with (pobj0:= pobj) (rqDown0:= downTo (obj_idx obj))
                   (rqdm:= valOf rqDown) (rsum:= valOf rsUp); eauto.
            { destruct rqDown as [rqDown rqdm]; simpl in *; subst; assumption. }
            { destruct rsUp as [rsUp rsum]; simpl in *; subst; assumption. }
          }

        * red; intros.
          disc_rule_conds.
          repeat ssplit; intros.
          { intro Hx.
            eapply downLockFree_rsUp_in_false
              with (pobj0:= pobj) (rsUp0:= rsUpFrom (obj_idx obj))
                   (rsum:= valOf rsUp); eauto.
            destruct rsUp as [rsUp rsum]; simpl in *; subst; assumption.
          }
          { eapply rqDown_in_rsUp_in_false
              with (pobj0:= pobj) (rqDown0:= downTo (obj_idx obj))
                   (rqdm:= valOf rqDown) (rsum:= valOf rsUp); eauto.
            { destruct rqDown as [rqDown rqdm]; simpl in *; subst; assumption. }
            { destruct rsUp as [rsUp rsum]; simpl in *; subst; assumption. }
          }
          { eapply rsUp_in_rsUp_in_false
              with (pobj0:= pobj) (rsUp0:= rsUpFrom (obj_idx obj))
                   (rsum1:= valOf rsUp) (rsum2:= valOf rrsUp); eauto.
            { destruct rsUp as [rsUp rsum]; simpl in *; subst; assumption. }
            { destruct rrsUp as [rrsUp rsum]; simpl in *; subst. assumption. }
          }
  Qed.

End MsgConflicts.

Ltac disc_MsgConflictsInv oidx :=
  repeat
    match goal with
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (c_li_indices _ ++ c_l1_indices _),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ Hin Horq);
      simpl in Hmcfi; dest
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (c_l1_indices _),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_intror Hin)) Horq);
      simpl in Hmcfi; dest
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (c_li_indices _),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_introl Hin)) Horq);
      simpl in Hmcfi; dest
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (tl (c_li_indices _)),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_introl (tl_In _ _ Hin))) Horq);
      simpl in Hmcfi; dest
    | [Hp: parentIdxOf _ oidx = Some ?pidx,
           Hmcfp: forall _, parentIdxOf _ oidx = Some _ ->
                            ParentLockConflicts _ _ _ _ /\ _ |- _] =>
      specialize (Hmcfp _ Hp); destruct Hmcfp
    | [Ho: ?orqs@[?pidx] = Some _,
           Hmcfp: forall _, ?orqs@[?pidx] = Some _ -> _ /\ _ |- _] =>
      specialize (Hmcfp _ Ho); destruct Hmcfp
    end.

Section Facts.

  Lemma MsgExistsSig_MsgsNotExist_false:
    forall msgs sigs,
      MsgsNotExist sigs msgs ->
      forall sig,
        In sig sigs ->
        MsgExistsSig sig msgs -> False.
  Proof.
    intros.
    destruct H1 as [idm [? ?]]; subst.
    specialize (H _ H1); clear H1.
    induction sigs; [dest_in|].
    destruct (sig_dec (sigOf idm) a); subst.
    - red in H.
      do 2 rewrite map_cons in H.
      rewrite caseDec_head_eq in H by reflexivity.
      auto.
    - inv H0; [auto|].
      red in H.
      do 2 rewrite map_cons in H.
      rewrite caseDec_head_neq in H by assumption.
      auto.
  Qed.

  Lemma not_MsgExistsSig_MsgsNotExist:
    forall (sigs: list MSig) (msgs: MessagePool Msg),
      (forall sig, In sig sigs -> MsgExistsSig sig msgs -> False) ->
      MsgsNotExist sigs msgs.
  Proof.
    induction sigs; simpl; intros;
      [hnf; intros; reflexivity|].

    do 2 red; intros.
    red; do 2 rewrite map_cons.
    destruct (sig_dec (sigOf idm) a).
    - subst; elim (H _ (or_introl eq_refl)).
      red; eauto.
    - rewrite caseDec_head_neq by assumption.
      eapply IHsigs; [|eassumption].
      intros; eapply H; eauto.
  Qed.

  Lemma MsgsP_enqMP:
    forall spl msgs,
      MsgsP spl msgs ->
      forall midx msg,
        MsgP spl (midx, msg) ->
        MsgsP spl (enqMP midx msg msgs).
  Proof.
    unfold MsgsP, MsgP; intros.
    apply InMP_enqMP_or in H1; destruct H1; auto.
    destruct idm as [midx' msg']; simpl in *; dest; subst.
    assumption.
  Qed.

  Lemma MsgsP_other_midx_enqMP:
    forall spl msgs,
      MsgsP spl msgs ->
      forall midx msg,
        ~ In midx (map (fun sp => fst (fst sp)) spl) ->
        MsgsP spl (enqMP midx msg msgs).
  Proof.
    unfold MsgsP, MsgP; intros.
    apply InMP_enqMP_or in H1; destruct H1; auto.
    destruct idm as [midx' msg']; simpl in *; dest; subst.
    destruct msg as [mid mty mval].
    unfold sigOf; simpl.
    clear -H0.
    induction spl; [simpl; auto|].
    unfold map; rewrite caseDec_head_neq.
    - apply IHspl.
      intro Hx; elim H0; right; assumption.
    - simpl; intro Hx.
      elim H0; left.
      unfold MSig in *; rewrite <-Hx; reflexivity.
  Qed.

  Lemma MsgsP_other_midx_enqMsgs:
    forall spl msgs,
      MsgsP spl msgs ->
      forall eins,
        DisjList (idsOf eins) (map (fun sp => fst (fst sp)) spl) ->
        MsgsP spl (enqMsgs eins msgs).
  Proof.
    intros.
    generalize dependent msgs.
    induction eins as [|ein eins]; simpl; intros; [assumption|].
    destruct ein as [midx msg]; simpl in *.
    apply DisjList_cons in H0; dest.
    eapply IHeins; eauto.
    apply MsgsP_other_midx_enqMP; auto.
  Qed.

  Lemma MsgsP_other_msg_id_enqMP:
    forall spl msgs,
      MsgsP spl msgs ->
      forall midx msg,
        ~ In (msg_id msg) (map (fun sp => snd (snd (fst sp))) spl) ->
        MsgsP spl (enqMP midx msg msgs).
  Proof.
    unfold MsgsP, MsgP; intros.
    apply InMP_enqMP_or in H1; destruct H1; auto.
    destruct idm as [midx' msg']; simpl in *; dest; subst.
    destruct msg as [mid mty mval]; simpl in H0.
    unfold sigOf; simpl.
    clear -H0.
    induction spl; [simpl; auto|].
    unfold map; rewrite caseDec_head_neq.
    - apply IHspl.
      intro Hx; elim H0; right; assumption.
    - simpl; intro Hx.
      elim H0; left.
      unfold MSig in *; rewrite <-Hx; reflexivity.
  Qed.

  Lemma MsgsP_other_msg_id_enqMsgs:
    forall spl msgs,
      MsgsP spl msgs ->
      forall eins,
        DisjList (map (fun idm => msg_id (valOf idm)) eins)
                 (map (fun sp => snd (snd (fst sp))) spl) ->
        MsgsP spl (enqMsgs eins msgs).
  Proof.
    intros.
    generalize dependent msgs.
    induction eins as [|ein eins]; simpl; intros; [assumption|].
    destruct ein as [midx msg]; simpl in *.
    apply DisjList_cons in H0; dest.
    eapply IHeins; eauto.
    apply MsgsP_other_msg_id_enqMP; auto.
  Qed.

  Lemma MsgsP_enqMP_inv:
    forall spl msgs midx msg,
      MsgsP spl (enqMP midx msg msgs) ->
      MsgsP spl msgs.
  Proof.
    unfold MsgsP; intros.
    apply H.
    apply InMP_or_enqMP; auto.
  Qed.

  Lemma MsgsP_enqMsgs_inv:
    forall spl msgs eins,
      MsgsP spl (enqMsgs eins msgs) ->
      MsgsP spl msgs.
  Proof.
    unfold MsgsP; intros.
    apply H.
    apply InMP_or_enqMsgs; auto.
  Qed.

  Lemma MsgsP_deqMP:
    forall spl msgs,
      MsgsP spl msgs ->
      forall midx,
        MsgsP spl (deqMP midx msgs).
  Proof.
    unfold MsgsP; intros.
    apply InMP_deqMP in H0; auto.
  Qed.

  Lemma MsgsP_deqMsgs:
    forall spl msgs,
      MsgsP spl msgs ->
      forall minds,
        MsgsP spl (deqMsgs minds msgs).
  Proof.
    unfold MsgsP; intros.
    apply InMP_deqMsgs in H0; auto.
  Qed.

  Lemma MsgsP_other_midx_deqMP_inv:
    forall spl msgs midx,
      MsgsP spl (deqMP midx msgs) ->
      ~ In midx (map (fun sp => fst (fst sp)) spl) ->
      MsgsP spl msgs.
  Proof.
    unfold MsgsP, MsgP; intros.
    destruct (idx_dec midx (idOf idm)); subst;
      [|apply H; apply deqMP_InMP_midx; auto].

    clear -H0.
    induction spl; [simpl; auto|].
    unfold map; rewrite caseDec_head_neq.
    - apply IHspl.
      intro Hx; elim H0; right; assumption.
    - simpl; intro Hx.
      elim H0; left.
      unfold MSig in *; rewrite <-Hx; reflexivity.
  Qed.

  Lemma MsgsP_other_midx_deqMsgs_inv:
    forall spl minds msgs,
      MsgsP spl (deqMsgs minds msgs) ->
      DisjList minds (map (fun sp => fst (fst sp)) spl) ->
      MsgsP spl msgs.
  Proof.
    intros.
    generalize dependent msgs.
    induction minds as [|mind minds]; simpl; intros; [assumption|].
    apply DisjList_cons in H0; dest.
    eapply MsgsP_other_midx_deqMP_inv.
    - eapply IHminds; eauto.
    - assumption.
  Qed.

  Lemma MsgsP_other_msg_id_deqMP_inv:
    forall spl msgs midx msg,
      MsgsP spl (deqMP midx msgs) ->
      FirstMP msgs midx msg ->
      ~ In (msg_id msg) (map (fun sp => snd (snd (fst sp))) spl) ->
      MsgsP spl msgs.
  Proof.
    unfold MsgsP, MsgP; intros.
    destruct (idx_dec midx (idOf idm)); subst;
      [|apply H; apply deqMP_InMP_midx; auto].

    destruct (msg_dec msg (valOf idm)); subst;
      [|apply H; eapply deqMP_InMP; eauto; congruence].

    clear -H1.
    induction spl; [simpl; auto|].
    unfold map; rewrite caseDec_head_neq.
    - apply IHspl.
      intro Hx; elim H1; right; assumption.
    - simpl; intro Hx.
      elim H1; left.
      unfold MSig in *; rewrite <-Hx; reflexivity.
  Qed.

  Lemma MsgsP_other_msg_id_deqMsgs_inv:
    forall spl rmsgs msgs,
      MsgsP spl (deqMsgs (idsOf rmsgs) msgs) ->
      NoDup (idsOf rmsgs) ->
      Forall (FirstMPI msgs) rmsgs ->
      DisjList (map (fun idm => msg_id (valOf idm)) rmsgs)
               (map (fun sp => snd (snd (fst sp))) spl) ->
      MsgsP spl msgs.
  Proof.
    intros.
    generalize dependent msgs.
    induction rmsgs as [|rmsg rmsgs]; simpl; intros; [assumption|].
    inv H0; inv H1.
    apply DisjList_cons in H2; dest.
    eapply MsgsP_other_msg_id_deqMP_inv; eauto.
    eapply IHrmsgs; eauto.
    apply FirstMPI_Forall_deqMP; auto.
  Qed.
  
End Facts.

Ltac solve_DisjList_ex dec :=
  repeat (rewrite map_trans; simpl);
  apply (DisjList_spec_1 dec); intros;
  repeat
    match goal with
    | [H: In _ (map _ _) |- _] => apply in_map_iff in H; dest; subst
    | [H: Forall _ ?l, Hin: In _ ?l |- _] =>
      rewrite Forall_forall in H; specialize (H _ Hin)
    | [H: ?e = _ |- ~ In ?e _] => rewrite H
    end;
  solve_not_in.

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
           |eapply MsgsP_other_msg_id_deqMsgs_inv in H;
            [|eassumption|eassumption|solve_DisjList_ex idx_dec]
    ]).

Ltac solve_MsgsP :=
  repeat
    (first [assumption
           |apply MsgsP_other_msg_id_enqMP; [|solve_not_in]
           |apply MsgsP_other_midx_enqMP; [|solve_chn_not_in]
           |apply MsgsP_other_msg_id_enqMsgs; [|solve_DisjList_ex idx_dec]
           |apply MsgsP_deqMP
           |apply MsgsP_deqMsgs]).

Hint Unfold MsgsNotExist: RuleConds.

