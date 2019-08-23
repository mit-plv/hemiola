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

(* NOTE: these ltacs only work for constants (channels, objects, etc.),
 * thus will be used only in this file.
 *)
(* Ltac get_lock_minds oidx := *)
(*   progress (good_footprint_get oidx); *)
(*   repeat (repeat disc_rule_conds_unit_simpl; try disc_footprints_ok); *)
(*   disc_minds_const. *)
 
(* Ltac get_lock_inv obj sys := *)
(*   let H := fresh "H" in *)
(*   assert (In obj (sys_objs sys)) as H by (simpl; tauto); *)
(*   progress (good_locking_get obj); *)
(*   clear H. *)

Existing Instance Mesi.ImplOStateIfc.

Definition MsgExistsSig (sig: MSig) (msgs: MessagePool Msg) :=
  exists idm, InMPI msgs idm /\ sigOf idm = sig.

Definition MsgP (spl: list (MSig * (Id Msg -> Prop))) (idm: Id Msg) :=
  caseDec sig_dec (sigOf idm) True
          (map (fun sp => (fst sp, snd sp idm)) spl).

Definition MsgsP (spl: list (MSig * (Id Msg -> Prop))) (msgs: MessagePool Msg) :=
  forall idm, InMPI msgs idm -> MsgP spl idm.

Definition MsgsNotExist (sigs: list MSig) (msgs: MessagePool Msg) :=
  MsgsP (map (fun sig => (sig, fun _ => False)) sigs) msgs.

Section ObjUnit.
  Variables (oidx: IdxT)
            (orq: ORq Msg)
            (ost: OState)
            (msgs: MessagePool Msg).

  Definition NoRsI :=
    MsgsNotExist [(downTo oidx, (MRs, mesiRsI))] msgs.

  Definition ImplOStateMESI (cv: nat): Prop :=
    mesiS <= ost#[implStatusIdx] -> NoRsI ->
    ost#[implValueIdx] = cv.

  Definition ObjExcl0 :=
    mesiE <= ost#[implStatusIdx] /\ NoRsI.

  Definition ObjExcl :=
    ObjExcl0 \/
    MsgExistsSig (downTo oidx, (MRs, mesiRsE)) msgs \/
    MsgExistsSig (downTo oidx, (MRs, mesiRsM)) msgs.

  Definition NoCohMsgs :=
    MsgsNotExist [(downTo oidx, (MRs, mesiRsS));
                    (downTo oidx, (MRs, mesiRsE));
                    (rsUpFrom oidx, (MRs, mesiDownRsS))] msgs.

  Definition ObjInvalid0 :=
    ost#[implStatusIdx] = mesiI /\ NoCohMsgs.

  Definition ObjInvalid :=
    ObjInvalid0 \/
    MsgExistsSig (downTo oidx, (MRs, mesiRsI)) msgs.

  Definition CohRqI :=
    ost#[implStatusIdx] = mesiM ->
    forall idm,
      InMPI msgs idm ->
      sigOf idm = (rqUpFrom oidx, (MRq, mesiRqI)) ->
      msg_value (valOf idm) = ost#[implValueIdx].

  Section Facts.

    Lemma NoRsI_MsgExistsSig_false:
      MsgExistsSig (downTo oidx, (MRs, mesiRsI)) msgs ->
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
  
End ObjUnit.

Definition InvObjExcl0 (oidx: IdxT) (ost: OState) (msgs: MessagePool Msg) :=
  ObjExcl0 oidx ost msgs ->
  NoCohMsgs oidx msgs /\ CohRqI oidx ost msgs.

Definition InvExcl (st: MState): Prop :=
  forall eidx,
    eost <+- (bst_oss st)@[eidx];
      (InvObjExcl0 eidx eost (bst_msgs st) /\
       (ObjExcl eidx eost (bst_msgs st) ->
        forall oidx,
          oidx <> eidx ->
          ost <+- (bst_oss st)@[oidx];
            ObjInvalid oidx ost (bst_msgs st))).

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
      mesiE <= eost#[implStatusIdx] ->
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
      mesiE <= eost#[implStatusIdx] ->
      forall oidx ost,
        oidx <> eidx ->
        (bst_oss st)@[oidx] = Some ost ->
        NoRsI oidx (bst_msgs st) ->
        ost#[implStatusIdx] = mesiI.
  Proof.
    intros.
    eapply InvExcl_excl_invalid in H1; eauto.
    destruct H1.
    - apply H1.
    - exfalso; eapply NoRsI_MsgExistsSig_false; eauto.
  Qed.
  
End Facts.

Hint Unfold MsgsNotExist NoRsI ImplOStateMESI (* ObjExcl0 ObjExcl *)
     (* NoCohMsgs *) (* CohRqI *) (* ObjInvalid0 ObjInvalid *) (* InvObjExcl0 *): RuleConds.

