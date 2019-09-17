Require Import List FMap Lia.
Require Import Common Topology ListSupport IndexSupport.
Require Import Syntax MessagePool Semantics StepM Invariant.
Require Import RqRsLang. Import RqRsNotations.

Require Import Ex.TopoTemplate Ex.RuleTemplate.

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

  Definition MsgConflictsInv (st: MState) :=
    forall oidx orq,
      In oidx (c_li_indices cifc ++ c_l1_indices cifc) ->
      (bst_orqs st)@[oidx] = Some orq ->
      RsDownConflicts oidx orq (bst_msgs st) /\
      RqUpConflicts oidx orq (bst_msgs st).

  Lemma tree2Topo_MsgConflicts_inv_ok:
    InvReachable sys step_m MsgConflictsInv.
  Proof.
    unfold InvReachable, MsgConflictsInv; intros.

    unfold cifc in H1.
    rewrite c_li_indices_head_rootOf in H1 by assumption.
    inv H1.

    1: { (* the root case *)
      (** TODO: need to prove an invariant about the root (main memory):
       * no messages exist in any channel of the root, i.e., the RqUp, RsUp,
       * and Down queues are all empty for the root.
       *)
      admit.
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

    split; red; intros; repeat ssplit; intros.
    - intro Hx.
      eapply upLocked_rsDown_in_false
        with (obj0:= obj) (down:= downTo (obj_idx obj))
             (rsdm:= valOf rsDown); eauto.
      unfold sigOf in H12; simpl in H12; red in H14; rewrite H12 in H14; assumption.
    - eapply rqUp_in_rsDown_in_false
        with (obj0:= obj) (rqUp0:= rqUpFrom (obj_idx obj)) (rqum:= valOf rqUp)
             (down:= downTo (obj_idx obj)) (rsdm:= valOf rsDown); eauto.
      + unfold sigOf in H15; simpl in H15; red in H16; rewrite H15 in H16; assumption.
      + unfold sigOf in H12; simpl in H12; red in H14; rewrite H12 in H14; assumption.
    - eapply rsDown_in_rsDown_in_false
        with (obj0:= obj) (down:= downTo (obj_idx obj))
             (rsdm1:= valOf rsDown) (rsdm2:= valOf rrsDown); eauto.
      + unfold sigOf in H12; simpl in H12; red in H14; rewrite H12 in H14; assumption.
      + unfold sigOf in H15; simpl in H15; red in H18; rewrite H15 in H18; assumption.
    - eapply rsDown_in_rqDown_first_false
        with (cobj:= obj) (pobj0:= pobj) (down:= downTo (obj_idx obj))
             (rsdm:= valOf rsDown) (rqdm:= valOf rqDown); eauto.
      + unfold sigOf in H12; simpl in H12; red in H14; rewrite H12 in H14; assumption.
      + unfold sigOf in H15; simpl in H15; red in H17; rewrite H15 in H17; assumption.
    - eapply rsDown_in_rsUp_in_false
        with (cobj:= obj) (pobj0:= pobj) (rsUp0:= rsUpFrom (obj_idx obj))
             (down:= downTo (obj_idx obj))
             (rsdm:= valOf rsDown) (rsum:= valOf rsUp); eauto.
      + unfold sigOf in H12; simpl in H12; red in H14; rewrite H12 in H14; assumption.
      + unfold sigOf in H15; simpl in H15; red in H16; rewrite H15 in H16; assumption.
    - intro Hx.
      eapply upLocked_rqUp_in_false
        with (obj0:= obj) (rqUp0:= rqUpFrom (obj_idx obj))
             (rqum:= valOf rqUp); eauto.
      unfold sigOf in H12; simpl in H12; red in H13; rewrite H12 in H13; assumption.
    - eapply rqUp_in_rqUp_in_false
        with (obj0:= obj) (rqUp0:= rqUpFrom (obj_idx obj))
             (rqum1:= valOf rqUp) (rqum2:= valOf rrqUp); eauto.
      + unfold sigOf in H12; simpl in H12; red in H13; rewrite H12 in H13; assumption.
      + unfold sigOf in H14; simpl in H14; red in H16; rewrite H14 in H16; assumption.
    - eapply rqUp_in_rsDown_in_false
        with (obj0:= obj) (rqUp0:= rqUpFrom (obj_idx obj)) (rqum:= valOf rqUp)
             (down:= downTo (obj_idx obj)) (rsdm:= valOf rsDown); eauto.
      + unfold sigOf in H12; simpl in H12; red in H13; rewrite H12 in H13; assumption.
      + unfold sigOf in H14; simpl in H14; red in H16; rewrite H14 in H16; assumption.
  Admitted.

End MsgConflicts.

Section Facts.

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

Hint Unfold MsgsNotExist: RuleConds.
