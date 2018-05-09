Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics SemFacts StepT.
Require Import Invariant Simulation.
Require Import Serial SerialFacts.
Require Import PredMsg StepPred.

Set Implicit Arguments.

Section GivenMsg.
  Variable (MsgT SysT: Type).
  Context `{HasMsg MsgT} `{IsSystem SysT} `{HasInit SysT OStates}.

  Lemma buildRawPSys_oindsOf:
    forall (sys: SysT), oindsOf sys = oindsOf (buildRawPSys MsgT sys).
  Proof.
    reflexivity.
  Qed.

  Lemma buildRawPSys_pToSystem_buildRawSys:
    forall (sys: SysT), pToSystem (buildRawPSys MsgT sys) = buildRawSys sys.
  Proof.
    reflexivity.
  Qed.

  Lemma addPRules_indices:
    forall rules sys,
      oindsOf (addPRules (MsgT:= MsgT) rules sys) =
      oindsOf sys.
  Proof.
    reflexivity.
  Qed.

  Corollary addPRules_behaviorOf:
    forall psys prules phst,
      behaviorOf (addPRules (MsgT:= MsgT) prules psys) phst =
      behaviorOf psys phst.
  Proof.
    induction phst; [reflexivity|].
    simpl; rewrite IHphst; reflexivity.
  Qed.

  Lemma pToSystem_indices:
    forall psys, oindsOf psys = oindsOf (pToSystem (MsgT:= MsgT) psys).
  Proof.
    reflexivity.
  Qed.

  Lemma pToTHistory_behaviorOf:
    forall psys phst,
      behaviorOf psys phst =
      behaviorOf (pToSystem (MsgT:= MsgT) psys) (pToTHistory phst).
  Proof.
    induction phst; simpl; intros; [reflexivity|].
    rewrite IHphst; f_equal.
    clear; destruct a; simpl; auto.
    - repeat f_equal.
      induction mins; simpl; auto.
      rewrite IHmins; reflexivity.
    - repeat f_equal.
      induction mouts; simpl; auto.
      rewrite IHmouts; reflexivity.
  Qed.

End GivenMsg.

(* Lemma atomic_history_pred_tinfo: *)
(*   forall sys ts rq hst mouts, *)
(*     Atomic sys ts rq hst mouts -> *)
(*     forall st1 st2, *)
(*       steps step_t sys st1 hst st2 -> *)
(*       forall phst, *)
(*         pToTHistory phst = hst -> *)
(*         Forall *)
(*           (fun lbl => *)
(*              match lbl with *)
(*              | PlblInt _ pins pouts => *)
(*                Forall (fun pmsg => *)
(*                          let tmsg := pmsg_omsg pmsg in *)
(*                          let msg := tmsg_msg tmsg in *)
(*                          if fromExternal sys msg then *)
(*                            msg = rq /\ tmsg_info tmsg = None *)
(*                          else *)
(*                            tmsg_info tmsg = Some (buildTInfo ts [rq]) *)
(*                       ) pins /\ *)
(*                Forall (fun pmsg => *)
(*                          tmsg_info (pmsg_omsg pmsg) = Some (buildTInfo ts [rq])) pouts *)
(*              | _ => False *)
(*              end) phst. *)
(* Proof. *)
(*   intros. *)
(*   eapply atomic_hst_tinfo in H; eauto; subst. *)

(*   clear -H. *)
(*   induction phst; [constructor|]. *)
(*   inv H; specialize (IHphst H3). *)
(*   constructor; auto. *)
(*   destruct a; auto. *)
  
(*   simpl in H2; clear -H2; destruct H2. *)
(*   split. *)

(*   - clear -H. *)
(*     induction mins; [constructor|]. *)
(*     inv H; specialize (IHmins H3). *)
(*     constructor; auto. *)

(*     destruct a as [[msg oti] pred]; simpl in *. *)
(*     destruct oti; dest; simpl in *; unfold_idx; subst. *)
(*     + destruct (ma_from _ ?<n _); congruence. *)
(*     + destruct (ma_from _ ?<n _); [congruence|auto]. *)

(*   - clear -H0. *)
(*     induction mouts; [constructor|]. *)
(*     inv H0; constructor; auto. *)
(* Qed. *)

Lemma rsBackFDefault_singleton:
  forall val ost,
    rsBackFDefault [val] ost = val.
Proof.
  simpl; intros.
  destruct val; reflexivity.
Qed.

Definition step_pred_t :=
  step_pred (stR:= PTStateR) step_t (@pToSystem TMsg) pToTLabel.

Theorem extAtomic_steps_pred_ok:
  forall sys ginv st1 thst st2 ts rqin mouts,
    InvStep sys step_t ginv ->
    steps step_t sys st1 thst st2 ->
    ExtAtomic sys ts rqin thst mouts ->
    forall psys: PSystem TMsg,
      pToSystem psys = sys ->
      InvStep psys step_pred_t (LiftInv (@pstx_st _ _ PTStateR) ginv) /\
      exists pst1 phst pst2,
        pToTHistory phst = thst /\
        pstx_st pst1 = st1 /\
        pstx_st pst2 = st2 /\
        steps step_pred_t psys pst1 phst pst2.
Proof.
Admitted.

Lemma step_pred_rules_split:
  forall oinds minds merqs merss Hmvalid inits prules1 prules2 pst1 plbl pst2,
    step_pred_t {| psys_oinds := oinds;
                   psys_minds := minds;
                   psys_merqs := merqs;
                   psys_merss := merss;
                   psys_msg_inds_valid := Hmvalid;
                   psys_inits := inits;
                   psys_rules := prules1 ++ prules2 |} pst1 plbl pst2 ->
    step_pred_t {| psys_oinds := oinds;
                   psys_minds := minds;
                   psys_merqs := merqs;
                   psys_merss := merss;
                   psys_msg_inds_valid := Hmvalid;
                   psys_inits := inits;
                   psys_rules := prules1 |} pst1 plbl pst2 \/
    step_pred_t {| psys_oinds := oinds;
                   psys_minds := minds;
                   psys_merqs := merqs;
                   psys_merss := merss;
                   psys_msg_inds_valid := Hmvalid;
                   psys_inits := inits;
                   psys_rules := prules2 |} pst1 plbl pst2.
Proof.
Admitted.

Corollary step_pred_rules_split_addPRules_1:
  forall (psys: PSystem TMsg) prule prules pst1 plbl pst2,
    step_pred_t (addPRules (prule :: prules) (buildRawPSys _ psys)) pst1 plbl pst2 ->
    step_pred_t (addPRules [prule] (buildRawPSys _ psys)) pst1 plbl pst2 \/
    step_pred_t (addPRules prules (buildRawPSys _ psys)) pst1 plbl pst2.
Proof.
  intros.
  apply step_pred_rules_split; auto.
Qed.

Corollary step_pred_rules_split_addPRules_2:
  forall (psys: PSystem TMsg) prule1 prule2 prules pst1 plbl pst2,
    step_pred_t (addPRules (prule1 :: prule2 :: prules) (buildRawPSys _ psys)) pst1 plbl pst2 ->
    step_pred_t (addPRules [prule1] (buildRawPSys _ psys)) pst1 plbl pst2 \/
    step_pred_t (addPRules [prule2] (buildRawPSys _ psys)) pst1 plbl pst2 \/
    step_pred_t (addPRules prules (buildRawPSys _ psys)) pst1 plbl pst2.
Proof.
  intros.
  apply step_pred_rules_split_addPRules_1 in H; destruct H; auto.
  apply step_pred_rules_split_addPRules_1 in H; destruct H; auto.
Qed.

