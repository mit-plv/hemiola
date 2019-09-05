Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Mesi.ImplOStateIfc.

(** Common Invariants that might be shared with the MOSI case study *)

Definition MsgExistsSig (sig: MSig) (msgs: MessagePool Msg) :=
  exists idm, InMPI msgs idm /\ sigOf idm = sig.

Definition MsgP (spl: list (MSig * (Id Msg -> Prop))) (idm: Id Msg) :=
  caseDec sig_dec (sigOf idm) True
          (map (fun sp => (fst sp, snd sp idm)) spl).

Definition MsgsP (spl: list (MSig * (Id Msg -> Prop))) (msgs: MessagePool Msg) :=
  forall idm, InMPI msgs idm -> MsgP spl idm.

Definition MsgsNotExist (sigs: list MSig) (msgs: MessagePool Msg) :=
  MsgsP (map (fun sig => (sig, fun _ => False)) sigs) msgs.

Section CoherenceUnit.
  Variables (oidx: IdxT)
            (orq: ORq Msg)
            (ost: OState)
            (msgs: MessagePool Msg).

  Definition NoRsI :=
    MsgsNotExist [(downTo oidx, (MRs, mesiInvRs))] msgs.

  Definition NoRqI :=
    MsgsNotExist [(rqUpFrom oidx, (MRq, mesiInvWRq));
                    (rqUpFrom oidx, (MRq, mesiPushWRq))] msgs.

  (** 0) Coherence: which values are in a coherent state *)

  Definition ImplOStateMESI (cv: nat): Prop :=
    mesiS <= ost#[status] -> NoRsI -> ost#[val] = cv.

  Definition CohInvRq :=
    mesiM <= ost#[status] ->
    forall idm,
      InMPI msgs idm ->
      sigOf idm = (rqUpFrom oidx, (MRq, mesiInvWRq)) ->
      msg_value (valOf idm) = ost#[val].

  Definition CohPushRq :=
    mesiS <= ost#[status] ->
    forall idm,
      InMPI msgs idm ->
      sigOf idm = (rqUpFrom oidx, (MRq, mesiPushWRq)) ->
      msg_value (valOf idm) = ost#[val].

  (** 1) Exclusiveness: if a coherence unit is exclusive, then all other units
   * are in an invalid status. *)
  
  Definition ObjExcl0 :=
    mesiE <= ost#[status] /\ NoRsI.

  Definition ObjExcl :=
    ObjExcl0 \/
    MsgExistsSig (downTo oidx, (MRs, mesiRsE)) msgs \/
    MsgExistsSig (downTo oidx, (MRs, mesiRsM)) msgs.

  Definition NoCohMsgs :=
    MsgsNotExist [(downTo oidx, (MRs, mesiRsS));
                    (downTo oidx, (MRs, mesiRsE));
                    (rsUpFrom oidx, (MRs, mesiDownRsS))] msgs.

  Definition ObjInvalid0 :=
    ost#[status] = mesiI /\ NoCohMsgs.

  Definition ObjInvalid :=
    ObjInvalid0 \/
    MsgExistsSig (downTo oidx, (MRs, mesiInvRs)) msgs.

  (** 2) Clean "E" in MESI: the invariant says that owners have the same clean
   * data if a bottom cache has E.
   *)

  Definition ObjExclClean :=
    ost#[status] = mesiE /\ NoRsI.

  Definition ObjStillClean (cv: nat) :=
    ost#[status] = mesiI ->
    ost#[dir].(dir_st) = mesiE ->
    ost#[val] = cv.

  Section Facts.

    Lemma NoRsI_MsgExistsSig_InvRs_false:
      MsgExistsSig (downTo oidx, (MRs, mesiInvRs)) msgs ->
      NoRsI -> False.
    Proof.
      intros.
      destruct H as [idm [? ?]].
      specialize (H0 _ H).
      unfold MsgP in H0.
      rewrite H1 in H0.
      unfold map, caseDec in H0.
      find_if_inside; auto.
    Qed.

  End Facts.

End CoherenceUnit.

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

  Definition RsDownConflictsInv (st: MState) :=
    forall oidx orq,
      In oidx (c_li_indices cifc ++ c_l1_indices cifc) ->
      (bst_orqs st)@[oidx] = Some orq ->
      RsDownConflicts oidx orq (bst_msgs st).

  Lemma tree2Topo_non_root_RsDownConflicts_inv_ok:
    InvReachable sys step_m RsDownConflictsInv.
  Proof.
    unfold InvReachable, RsDownConflictsInv; intros.

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

    red; intros; repeat ssplit; intros.
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
  Admitted.

End MsgConflicts.

(** End of the common invariants -- *)

Lemma mesi_RsDownConflicts:
  forall tr (Htr: tr <> Node nil),
    InvReachable (impl Htr) step_m (RsDownConflictsInv tr 0).
Proof.
  intros.
  apply tree2Topo_non_root_RsDownConflicts_inv_ok; auto.
  simpl; unfold mem, li, l1.
  rewrite map_app.
  do 2 rewrite map_trans.
  do 2 rewrite map_id.
  rewrite app_comm_cons.
  rewrite <-c_li_indices_head_rootOf by assumption.
  apply SubList_refl.
Qed.

Definition InvObjExcl0 (oidx: IdxT) (ost: OState) (msgs: MessagePool Msg) :=
  ObjExcl0 oidx ost msgs ->
  NoCohMsgs oidx msgs /\ CohInvRq oidx ost msgs /\ CohPushRq oidx ost msgs.

Definition InvExcl (st: MState): Prop :=
  forall eidx,
    eost <+- (bst_oss st)@[eidx];
      (InvObjExcl0 eidx eost (bst_msgs st) /\
       (ObjExcl eidx eost (bst_msgs st) ->
        forall oidx,
          oidx <> eidx ->
          ost <+- (bst_oss st)@[oidx];
            ObjInvalid oidx ost (bst_msgs st))).

Definition InvExclC (st: MState): Prop :=
  forall eidx,
    eost <+- (bst_oss st)@[eidx];
      (ObjExclClean eidx eost (bst_msgs st) ->
       forall oidx,
         oidx <> eidx ->
         ost <+- (bst_oss st)@[oidx];
           ObjStillClean ost eost#[val]).

Lemma caseDec_head_eq:
  forall {A B} (eq_dec: forall a1 a2: A, {a1 = a2} + {a1 <> a2})
         k (df: B) hd tl,
    k = fst hd ->
    caseDec eq_dec k df (hd :: tl) = snd hd.
Proof.
  intros; subst.
  destruct hd as [hk hv]; simpl.
  find_if_inside; [reflexivity|exfalso; auto].
Qed.

Lemma caseDec_head_neq:
  forall {A B} (eq_dec: forall a1 a2: A, {a1 = a2} + {a1 <> a2})
         k (df: B) hd tl,
    k <> fst hd ->
    caseDec eq_dec k df (hd :: tl) = caseDec eq_dec k df tl.
Proof.
  intros; subst.
  destruct hd as [hk hv]; simpl.
  find_if_inside; [exfalso; auto|reflexivity].
Qed.

Ltac disc_caseDec Hcd :=
  repeat
    (first [rewrite caseDec_head_eq in Hcd by reflexivity
           |rewrite caseDec_head_neq in Hcd by discriminate]);
  simpl in Hcd.

Ltac solve_caseDec :=
  repeat
    (first [rewrite caseDec_head_eq by reflexivity
           |rewrite caseDec_head_neq by discriminate]);
  simpl.

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

  Lemma InvExcl_excl_invalid:
    forall st (He: InvExcl st) msgs eidx eost,
      bst_msgs st = msgs ->
      (bst_oss st)@[eidx] = Some eost ->
      NoRsI eidx msgs ->
      mesiE <= eost#[status] ->
      forall oidx ost,
        oidx <> eidx ->
        (bst_oss st)@[oidx] = Some ost ->
        ObjInvalid oidx ost msgs.
  Proof.
    intros; subst.
    specialize (He eidx).
    disc_rule_conds_ex.
    unfold ObjExcl, ObjExcl0 in H5; simpl in H5.
    specialize (H5 (or_introl (conj H2 H1)) _ H3).
    solve_rule_conds_ex.
  Qed.

  Corollary InvExcl_excl_invalid_status:
    forall st (He: InvExcl st) eidx eost,
      (bst_oss st)@[eidx] = Some eost ->
      NoRsI eidx (bst_msgs st) ->
      mesiE <= eost#[status] ->
      forall oidx ost,
        oidx <> eidx ->
        (bst_oss st)@[oidx] = Some ost ->
        NoRsI oidx (bst_msgs st) ->
        ost#[status] = mesiI.
  Proof.
    intros.
    eapply InvExcl_excl_invalid in H1; eauto.
    destruct H1.
    - apply H1.
    - exfalso; eapply NoRsI_MsgExistsSig_InvRs_false; eauto.
  Qed.
  
End Facts.

Hint Unfold MsgsNotExist NoRsI ImplOStateMESI: RuleConds.

