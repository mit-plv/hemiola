Require Import Bool List String Peano_dec Lia.
Require Import Common FMap HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Ex.Msi Ex.SpecSv.
Require Import Ex.MsiSv.MsiSv Ex.MsiSv.MsiSvTopo.

Set Implicit Arguments.

Import MonadNotations.
Import CaseNotations.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Ltac solve_msi :=
  unfold msiM, msiS, msiI in *; lia.

Ltac solve_msi_false :=
  exfalso; try congruence;
  match goal with
  | [H: msiS <= msiI |- _] => clear -H; solve_msi
  | [H: msiM <= msiI |- _] => clear -H; solve_msi
  | [H: msiM <= msiS |- _] => clear -H; solve_msi
  | [H1: ?t = msiI, H2: msiS <= ?t |- _] =>
    rewrite H1 in H2; clear -H2; solve_msi
  | [H1: ?t = msiI, H2: msiM <= ?t |- _] =>
    rewrite H1 in H2; clear -H2; solve_msi
  | [H1: ?t = msiS, H2: msiM <= ?t |- _] =>
    rewrite H1 in H2; clear -H2; solve_msi
  end.

Section Inv.

  Existing Instance MsiSv.ImplOStateIfc.

  Section InvDir.
    Variables (post: OState)
              (porq: ORq Msg).

    (* Why exclusiveness of the directory:
     * It's simple. We need to know [P.st = C2.st = I] when [C1.st = M] and
     * [C1] is lock-free. By the soundness of the directory, we can get
     * [P.dir.C1 = M]. Then by this exclusiveness, we can get
     * [P.st = P.dir.C2 = I].
     *)
    Definition DirExcl1: Prop :=
      (msiM <= post#[implDirIdx].(fst) ->
       post#[implStatusIdx] = msiI /\ post#[implDirIdx].(snd) = msiI) /\
      (post#[implStatusIdx] = msiI ->
       post#[implDirIdx].(snd) = msiI ->
       msiM <= post#[implDirIdx].(fst)).

    Definition DirExcl2: Prop :=
      (msiM <= post#[implDirIdx].(snd) ->
       post#[implStatusIdx] = msiI /\ post#[implDirIdx].(fst) = msiI) /\
      (post#[implStatusIdx] = msiI ->
       post#[implDirIdx].(fst) = msiI ->
       msiM <= post#[implDirIdx].(snd)).

    Definition DirCorrectM: Prop :=
      (msiM <= post#[implStatusIdx] ->
       post#[implDirIdx].(fst) = msiI /\ post#[implDirIdx].(snd) = msiI) /\
      (post#[implDirIdx].(fst) = msiI ->
       post#[implDirIdx].(snd) = msiI ->
       msiM <= post#[implStatusIdx]).

    (* Why soundness of the shared status:
     * the parent is upgraded to M when all children values are evicted.
     * In this case the parent does not update the value, but maintain the
     * value since the protocol is write-through. But in order to check
     * correctness we need to know the parent status is S when all children
     * values are evicted.
     *)
    Definition DirSoundS: Prop :=
      (post#[implDirIdx].(fst) = msiS \/ post#[implDirIdx].(snd) = msiS) ->
      post#[implStatusIdx] = msiS.

    Definition DirCorrectS: Prop :=
      post#[implStatusIdx] = msiS ->
      (post#[implDirIdx].(fst) <= msiS /\ post#[implDirIdx].(snd) <= msiS).
        
    Definition DirInvP: Prop :=
      DirSoundS /\ DirExcl1 /\ DirExcl2 /\
      DirCorrectM /\ DirCorrectS.

  End InvDir.

  Section DownLockInv.
    Variables (post: OState)
              (porq: ORq Msg).

    Definition ParentDownRsS1 (rqid: RqInfo Msg): Prop :=
      rqid.(rqi_msg).(msg_id) = msiDownRqS ->
      msiM <= post#[implDirIdx].(snd).
      
    Definition ParentDownRsS2 (rqid: RqInfo Msg): Prop :=
      rqid.(rqi_msg).(msg_id) = msiDownRqS ->
      msiM <= post#[implDirIdx].(fst).

    Definition ParentDownRsI1 (rqid: RqInfo Msg): Prop :=
      rqid.(rqi_msg).(msg_id) = msiDownRqI ->
      msiS <= post#[implDirIdx].(snd).

    Definition ParentDownRsI2 (rqid: RqInfo Msg): Prop :=
      rqid.(rqi_msg).(msg_id) = msiDownRqI ->
      msiS <= post#[implDirIdx].(fst).

    Definition ParentDownLockBack: Prop :=
      rqid <+- porq@[downRq];
        (rqid.(rqi_minds_rss) = [c1pRs] ->
         rqid.(rqi_midx_rsb) = pc2 /\ ParentDownRsS2 rqid /\ ParentDownRsS2 rqid) /\
        (rqid.(rqi_minds_rss) = [c2pRs] ->
         rqid.(rqi_midx_rsb) = pc1 /\ ParentDownRsS1 rqid /\ ParentDownRsI1 rqid).

    Definition DownLockInv: Prop :=
      ParentDownLockBack.

  End DownLockInv.

  Definition ImplInvB (st: MState): Prop :=
    post <-- (bst_oss st)@[parentIdx];
      porq <-- (bst_orqs st)@[parentIdx];
      DirInvP post /\ DownLockInv post porq.

  Hint Unfold DirSoundS DirExcl1 DirExcl2
       DirCorrectM DirCorrectS DirInvP
       ParentDownRsS1 ParentDownRsS2 ParentDownRsI1 ParentDownRsI2
       ParentDownLockBack DownLockInv
       ImplInvB: RuleConds.

  Ltac disc_impl_inv_b :=
    repeat
      match goal with
      | [H: getDir _ _ = _ |- _] => unfold getDir in H; simpl in H
      | [H1: msg_id _ = _, H2: msg_id _ = _ |- _] => rewrite H1 in H2; discriminate
      end.

  Ltac disc_rule_custom ::=
    try disc_impl_inv_b.

  Lemma implInvB_init:
    ImplInvB (initsOf impl).
  Proof.
    red; simpl.
    unfold implOStatesInit, implORqsInit; mred.
    simpl; repeat split;
      try (simpl in *; solve_msi_false; fail); auto;
        try (simpl; intros; discriminate).
  Qed.

  Lemma implInvB_invStep:
    InvStep impl step_m ImplInvB.
  Proof.
    unfold InvStep; intros.
    inv H1; try assumption.
    dest_in.

    (* It roughly takes 3 minutes to solve all 40 cases. *)
    all: solve_rule_conds_ex; solve_msi; fail.
  Qed.

  Lemma implInvB_ok:
    InvReachable impl step_m ImplInvB.
  Proof.
    apply inv_reachable.
    - apply implInvB_init.
    - apply implInvB_invStep.
  Qed.

End Inv.

Hint Unfold DirSoundS DirExcl1 DirExcl2
     DirCorrectM DirCorrectS DirInvP
     ParentDownRsS1 ParentDownRsS2 ParentDownRsI1 ParentDownRsI2
     ParentDownLockBack DownLockInv: RuleConds.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

