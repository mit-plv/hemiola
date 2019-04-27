Require Import Bool List String Peano_dec Omega.
Require Import Common FMap HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Msi MsiSv SpecSv MsiSvTopo.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Notation "A <-- OA ; CONT" :=
  (OA >>=[False] (fun A => CONT)) (at level 15, right associativity).
Notation "A <+- OA ; CONT" :=
  (OA >>=[True] (fun A => CONT)) (at level 15, right associativity).

Fixpoint caseDec {A B} (dec: forall a1 a2: A, {a1 = a2} + {a1 <> a2})
         (a: A) (def: B) (cs: list (A * B)) :=
  match cs with
  | nil => def
  | (ca, cp) :: cs' =>
    if dec a ca then cp else caseDec dec a def cs'
  end.

Notation "x : t" := (x, t) (at level 90, only parsing): cases_scope.
Notation "| xt1 | xt2 | .. | xtn" :=
  (cons xt1 (cons xt2 .. (cons xtn nil) ..)) (at level 95, only parsing): cases_scope.
Delimit Scope cases_scope with cases.
Notation "'match' 'case' X 'on' DEC 'default' DEF 'with' CS 'end'" :=
  (caseDec DEC X DEF CS%cases) (only parsing).

Definition Mii := (IdxT * IdxT)%type.

Definition mii_dec: forall mii1 mii2: Mii, {mii1 = mii2} + {mii1 <> mii2}.
Proof.
  decide equality.
  - apply eq_nat_dec.
  - apply eq_nat_dec.
Defined.

Definition miis_dec := list_eq_dec mii_dec.

Definition miiOf (idm: Id Msg): Mii := (idOf idm, msg_id (valOf idm)).
Definition miisOf (msgs: list (Id Msg)): list Mii :=
  map miiOf msgs.

Definition AtomicMsgOutsInv {oifc} (mp: MsgOutPred oifc)
           (eouts: list (Id Msg)) (nst: MState oifc): Prop :=
  Forall (fun eout => mp eout nst.(bst_oss)) eouts.

Definition AtomicLocksInv {oifc}
           (lp: IdxT -> ORq Msg -> Prop)
           (hst: MHistory) (nst: MState oifc): Prop :=
  forall oidx,
    In oidx (oindsOf hst) ->
    orq <-- (bst_orqs nst)@[oidx]; lp oidx orq.

Definition AtomicInv {oifc}
           (mp: MsgOutPred oifc)
           (lp: IdxT -> ORq Msg -> Prop):
  list (Id Msg) (* inits *) ->
  MState oifc (* starting state *) ->
  MHistory (* atomic history *) ->
  list (Id Msg) (* eouts *) ->
  MState oifc (* ending state *) -> Prop :=
  fun inits st1 hst eouts st2 =>
    AtomicMsgOutsInv mp eouts st2 /\
    AtomicLocksInv lp hst st2.

Section Inv.

  Definition ImplOStateI (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] = msiI.

  Definition ImplOStateS (cv: nat) (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] = msiI \/
    (ost#[implStatusIdx] = msiS /\ ost#[implValueIdx] = cv).

  Definition ImplOStateM (cv: nat) (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] = msiM /\ ost#[implValueIdx] = cv.

  Definition ImplStateI (oss: OStates ImplOStateIfc): Prop.
  Proof.
    refine ((oss@[parentIdx]) >>=[False] (fun post => _)).
    refine ((oss@[child1Idx]) >>=[False] (fun cost1 => _)).
    refine ((oss@[child2Idx]) >>=[False] (fun cost2 => _)).
    exact (ImplOStateI post /\ (* Directory status is I as well. *)
           ImplOStateI cost1 /\ ImplOStateI cost2).
  Defined.

  Definition ImplStateS (cv: nat) (oss: OStates ImplOStateIfc): Prop.
  Proof.
    refine ((oss@[parentIdx]) >>=[False] (fun post => _)).
    refine ((oss@[child1Idx]) >>=[False] (fun cost1 => _)).
    refine ((oss@[child2Idx]) >>=[False] (fun cost2 => _)).
    refine (post#[implStatusIdx] = msiS /\ _). (* Directory status is S. *)
    exact (ImplOStateS cv cost1 /\ ImplOStateS cv cost2).
  Defined.

  Definition ImplStateM (cv: nat) (oss: OStates ImplOStateIfc): Prop.
  Proof.
    refine ((oss@[parentIdx]) >>=[False] (fun post => _)).
    refine ((oss@[child1Idx]) >>=[False] (fun cost1 => _)).
    refine ((oss@[child2Idx]) >>=[False] (fun cost2 => _)).
    refine (post#[implStatusIdx] = msiM /\ _). (* Directory status is M. *)
    exact ((ImplOStateM cv cost1 /\ ImplOStateI cost2) \/
           (ImplOStateI cost1 /\ ImplOStateM cv cost2) \/
           (ImplOStateS cv cost1 /\ ImplOStateS cv cost2)).
  Defined.

  Definition ImplStateCoherent
             (cv: nat) (oss: OStates ImplOStateIfc): Prop :=
    ImplStateI oss \/ ImplStateS cv oss \/ ImplStateM cv oss.
  
  Definition ImplStateMSI (st: MState ImplOStateIfc): Prop :=
    exists cv, (* The coherent value always exists. *)
      ImplStateCoherent cv st.(bst_oss).

  Ltac disc_msi :=
    match goal with
    | [H: ImplStateCoherent _ _ |- _] => red in H
    | [H: _ \/ _ |- _] => destruct H

    | [H: ImplStateM _ _ |- _] => red in H
    | [H: ImplStateS _ _ |- _] => red in H
    | [H: ImplStateI _ |- _] => red in H

    | [H: ImplOStateM _ _ |- _] => destruct H
    | [H: ImplOStateS _ _ |- _] => destruct H
    | [H: ImplOStateI _ |- _] => red in H

    | [H: ?oss@[_] = Some ?ost |- _] =>
      match type of ost with
      | OState _ =>
        let val := fresh "val" in
        let stt := fresh "stt" in
        destruct ost as [val [stt ?]]
      end
    end.
  
  Ltac disc_rule_custom ::=
    try disc_msi;
    try (unfold msiI, msiS, msiM in *; omega).
  
  Section Facts.

    Lemma implStateCoherent_M_value_changed:
      forall cv oss,
        ImplStateCoherent cv oss ->
        forall oidx ost,
          (oidx = child1Idx \/ oidx = child2Idx) ->
          oss@[oidx] = Some ost ->
          ost#[implStatusIdx] = msiM ->
          forall n uv,
            ImplStateCoherent n (oss +[oidx <- (n, (msiM, uv))]).
    Proof.
      intros; solve_rule_conds_ex.
      - right; right.
        red; solve_rule_conds_ex.
        left; solve_rule_conds_ex.
      - right; right.
        red; solve_rule_conds_ex.
        right; left; solve_rule_conds_ex.
    Qed.

    Lemma implStateCoherent_downgraded_to_S:
      forall cv oss,
        ImplStateCoherent cv oss ->
        forall oidx ost,
          (oidx = child1Idx \/ oidx = child2Idx) ->
          oss@[oidx] = Some ost ->
          ost#[implStatusIdx] >= msiS ->
          ImplStateCoherent cv (oss +[oidx <- (fst ost, (msiS, snd (snd ost)))]).
    Proof.
      intros; solve_rule_conds_ex.
      all: try (right; left; red; solve_rule_conds_ex; auto; fail).
      all: try (right; right;
                red; solve_rule_conds_ex;
                right; right;
                solve_rule_conds_ex).
    Qed.

    Lemma implStateCoherent_downgraded_to_I:
      forall cv oss,
        ImplStateCoherent cv oss ->
        forall oidx ost,
          (oidx = child1Idx \/ oidx = child2Idx) ->
          oss@[oidx] = Some ost ->
          ImplStateCoherent cv (oss +[oidx <- (fst ost, (msiI, snd (snd ost)))]).
    Proof.
      intros; solve_rule_conds_ex.
      all: try (left; red; solve_rule_conds_ex; fail).
      all: try (right; left; red; solve_rule_conds_ex; auto; fail).
      all: try (right; right;
                red; solve_rule_conds_ex;
                right; right;
                solve_rule_conds_ex; fail).
      - right; right.
        red; solve_rule_conds_ex.
        right; left; solve_rule_conds_ex.
      - right; right.
        red; solve_rule_conds_ex.
        left; solve_rule_conds_ex.
    Qed.

    Lemma msiSv_impl_InvTrs_ext_in:
      forall st1 eins st2,
        ImplStateMSI st1 ->
        step_m impl st1 (RlblIns eins) st2 ->
        ImplStateMSI st2.
    Proof.
      intros; inv_step.
      destruct H as [cv ?]; exists cv.
      assumption.
    Qed.

    Lemma msiSv_impl_InvTrs_ext_out:
      forall st1 eouts st2,
        ImplStateMSI st1 ->
        step_m impl st1 (RlblOuts eouts) st2 ->
        ImplStateMSI st2.
    Proof.
      intros; inv_step.
      destruct H as [cv ?]; exists cv.
      assumption.
    Qed.

    Definition MsiSvMsgOutPred: MsgOutPred ImplOStateIfc :=
      fun eout oss =>
        match case (miiOf eout) on mii_dec default True with
        | (ec1, Spec.getRq): False
        | (ec1, Spec.setRq): False
        | (ec1, Spec.evictRq): False
        | (ec2, Spec.getRq): False
        | (ec2, Spec.setRq): False
        | (ec2, Spec.evictRq): False
                           
        | (pc1, msiRsS): 
            post <-- oss@[parentIdx];
            cost2 <-- oss@[child2Idx];
            (post#[implStatusIdx] = msiS /\
             ImplOStateS post#[implValueIdx] cost2 /\
             msg_value (valOf eout) = VNat post#[implValueIdx])
        | (pc2, msiRsS):
            post <-- oss@[parentIdx];
            cost1 <-- oss@[child1Idx];
            (post#[implStatusIdx] = msiS /\
             ImplOStateS post#[implValueIdx] cost1 /\
             msg_value (valOf eout) = VNat post#[implValueIdx])
        | (pc1, msiRsM):
            post <-- oss@[parentIdx];
            cost2 <-- oss@[child2Idx];
            (post#[implStatusIdx] = msiM /\ ImplOStateI cost2)
        | (pc2, msiRsM):
            post <-- oss@[parentIdx];
            cost1 <-- oss@[child1Idx];
            (post#[implStatusIdx] = msiM /\ ImplOStateI cost1)

        | (c1pRs, msiDownRsS):
            cost1 <-- oss@[child1Idx];
            (cost1#[implStatusIdx] = msiS /\             
             msg_value (valOf eout) = VNat cost1#[implValueIdx])
        | (c2pRs, msiDownRsS):
            cost2 <-- oss@[child2Idx];
            (cost2#[implStatusIdx] = msiS /\
             msg_value (valOf eout) = VNat cost2#[implValueIdx])
        | (c1pRs, msiDownRsM):
            cost1 <-- oss@[child1Idx];
            (cost1#[implStatusIdx] = msiI)
        | (c2pRs, msiDownRsM):
            cost2 <-- oss@[child2Idx];
            (cost2#[implStatusIdx] = msiI)
        end.

    Lemma msiSvMsgOutPred_good:
      GoodMsgOutPred topo impl MsiSvMsgOutPred.
    Proof.
    Admitted.

    Definition MsiSvLockPred (oidx: IdxT) (orq: ORq Msg): Prop :=
      match case oidx on eq_nat_dec default True with
      | child1Idx: True
      | child2Idx: True
      | parentIdx:
          rqid <+- orq@[downRq];
          ((rqid.(rqi_minds_rss) = [c1pRs] /\ rqid.(rqi_midx_rsb) = pc2) \/
           (rqid.(rqi_minds_rss) = [c2pRs] /\ rqid.(rqi_midx_rsb) = pc1))
      end.

    Ltac disc_AtomicInv :=
      repeat
        match goal with
        | [H: AtomicInv _ _ _ _ _ _ _ |- _] => red in H; dest
        end.

    Ltac disc_rule_custom ::=
      try disc_footprints_ok;
      try disc_AtomicInv.

    Ltac atomic_cont_exfalso_bound :=
      exfalso;
      disc_rule_conds_ex;
      repeat 
        match goal with
        | [H1: AtomicMsgOutsInv _ ?eouts _, H2: In _ ?eouts |- _] =>
          red in H1; rewrite Forall_forall in H1;
          specialize (H1 _ H2); simpl in H1
        | [H: MsiSvMsgOutPred _ _ |- _] => red in H
        | [H1: caseDec _ ?mii _ _ |- _] =>
          match mii with
          | miiOf (?midx, ?msg) =>
            match goal with
            | [H2: msg_id ?msg = ?mid |- _] =>
              progress replace mii with (midx, mid) in H1
                by (unfold miiOf; simpl; rewrite H2; reflexivity);
              simpl in H1
            end
          end
        end;
      assumption.

    Ltac atomic_init_exfalso_rq :=
      exfalso;
      disc_rule_conds_ex;
      repeat
        match goal with
        | [H: _ = _ \/ _ |- _] =>
          destruct H; [subst; try discriminate|auto]
        end.

    Ltac atomic_init_exfalso_rs_from_parent :=
      exfalso;
      repeat
        (repeat match goal with
                | [H: UpLockInvORq _ _ _ _ _ |- _] => red in H
                | [H1: ?orq@[0] = Some _, H2: context[?orq@[0]] |- _] =>
                  rewrite H1 in H2; simpl in H2
                | [H: UpLockRsFromParent _ _ _ |- _] =>
                  let rsFrom := fresh "rsFrom" in
                  destruct H as [rsFrom [? ?]]
                end;
         unfold upRq in *;
         disc_rule_conds_ex);
      repeat
        match goal with
        | [H1: _ = ?rsFrom \/ _, H2: edgeDownTo _ _ = Some ?rsFrom |- _] =>
          destruct H1; [subst; try discriminate|auto]
        end.

    Ltac atomic_init_exfalso_rs_to_parent :=
      exfalso;
      pose proof msiSv_impl_RqRsDTree;
      repeat
        (repeat match goal with
                | [H: DownLockInvORq _ _ _ _ _ |- _] => red in H
                | [H1: ?orq@[1] = Some _, H2: context[?orq@[1]] |- _] =>
                  rewrite H1 in H2; simpl in H2
                | [H: DownLockRssToParent _ _ _ |- _] => red in H
                | [H: _ = rqi_minds_rss _ |- _] => apply eq_sym in H
                end;
         unfold downRq in *;
         disc_rule_conds_ex);
      repeat
        match goal with
        | [H1: _ = ?rsFrom \/ _, H2: rsEdgeUpFrom _ _ = Some ?rsFrom |- _] =>
          destruct H1; [subst; try discriminate|auto]
        end.

    Ltac atomic_init_solve_AtomicMsgOutsInv :=
      simpl; repeat constructor.

    Ltac atomic_init_solve_AtomicLocksInv :=
      red; intros; dest_in;
      repeat (simpl; mred);
      unfold miiOf; simpl;
      repeat
        match goal with
        | [H: msg_id ?msg = _ |- context [msg_id ?msg] ] => rewrite H
        | [H1: msg_id ?msg = _, H2: context [msg_id ?msg] |- _] =>
          rewrite H1 in H2
        | [H: ?orq@[?i] = Some _ |- context [?orq@[?i]] ] => rewrite H
        | [H1: ?orq@[?i] = Some _, H2: context [?orq@[?i]] |- _] =>
          rewrite H1 in H2
        | [H: ?orq@[?i] = None |- context [?orq@[?i]] ] => rewrite H
        | [H1: ?orq@[?i] = None, H2: context [?orq@[?i]] |- _] =>
          rewrite H1 in H2
        end;
      repeat (red; simpl; mred; auto).

    Local Ltac atomic_init_solve_AtomicInv :=
      split; [atomic_init_solve_AtomicMsgOutsInv
             |atomic_init_solve_AtomicLocksInv].

    Lemma msiSv_impl_InvTrs_init:
      forall st1,
        Reachable (steps step_m) impl st1 ->
        ImplStateMSI st1 ->
        forall oidx ridx ins outs st2,
          SubList (idsOf ins) (sys_merqs impl) ->
          step_m impl st1 (RlblInt oidx ridx ins outs) st2 ->
          AtomicInv
            MsiSvMsgOutPred MsiSvLockPred
            ins st1 [RlblInt oidx ridx ins outs] outs st2 /\
          ImplStateMSI st2.
    Proof.
      intros.
      inv_step.
      pose proof (upLockInv_ok
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree H) as Hulinv.
      pose proof (downLockInv_ok
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree
                    msiSv_impl_GoodExtRssSys H) as Hdlinv.
      good_locking_get obj.
      dest_in.

      3, 7, 10, 13, 17, 20: atomic_init_exfalso_rs_from_parent.
      3, 6, 10, 13, 15-24: atomic_init_exfalso_rq.

      - disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        assumption.

      - disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        assumption.

      - disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        destruct H0 as [cv ?]; simpl in H.
        exists n; simpl.
        eapply implStateCoherent_M_value_changed; eauto.

      - disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        assumption.

      - disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        assumption.

      - disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child2Idx <- pos]) with oss by meq.
        assumption.

      - disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child2Idx <- pos]) with oss by meq.
        assumption.

      - disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        destruct H0 as [cv ?]; simpl in H.
        exists n; simpl.
        eapply implStateCoherent_M_value_changed; eauto.

      - disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child2Idx <- pos]) with oss by meq.
        assumption.

      - disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child2Idx <- pos]) with oss by meq.
        assumption.

      - atomic_init_exfalso_rs_to_parent.
        + assert (rqEdgeUpFrom topo ext1Idx = Some ec1) by reflexivity.
          solve_midx_false.
        + assert (rqEdgeUpFrom topo ext2Idx = Some ec2) by reflexivity.
          solve_midx_false.

      - atomic_init_exfalso_rs_to_parent.
        + assert (rqEdgeUpFrom topo ext1Idx = Some ec1) by reflexivity.
          solve_midx_false.
        + assert (rqEdgeUpFrom topo ext2Idx = Some ec2) by reflexivity.
          solve_midx_false.
    Qed.

    Lemma miisOf_app:
      forall miis1 miis2,
        miisOf (miis1 ++ miis2) = miisOf miis1 ++ miisOf miis2.
    Proof.
      unfold miisOf; intros.
      apply map_app.
    Qed.

    Ltac obj_visited_rsDown oidx :=
      try match goal with
          | [Ha: Atomic _ _ _ ?hst _ _ |- _] =>
            assert (In oidx (oindsOf hst))
              by (eapply extAtomic_rsDown_acceptor_visited; eauto;
                  [exact msiSv_impl_RqRsSys
                  |econstructor; eassumption
                  |red; auto])
          end.

    Ltac disc_lock_preds_with Hl oidx :=
      match type of Hl with
      | AtomicLocksInv _ ?hst _ =>
        match goal with
        | [Hin: In oidx (oindsOf ?hst) |- _] =>
          specialize (Hl _ Hin); simpl in Hl;
          disc_rule_conds_ex; red in Hl; simpl in Hl
        end
      end.

    Ltac disc_lock_preds oidx :=
      match goal with
      | [H: AtomicLocksInv _ _ _ |- _] =>
        let Hl := fresh "H" in
        pose proof H as Hl;
        disc_lock_preds_with Hl oidx
      end.

    Ltac disc_mii_caseDec :=
      match goal with
      | [H1: caseDec _ ?mii _ _ |- _] =>
        match mii with
        | miiOf (?midx, ?msg) =>
          match goal with
          | [H2: msg_id ?msg = ?mid |- _] =>
            progress replace mii with (midx, mid) in H1
              by (unfold miiOf; simpl; rewrite H2; reflexivity);
            simpl in H1
          end
        end
      end.

    Ltac disc_msg_preds_with Hl Hin :=
      match type of Hl with
      | AtomicMsgOutsInv _ ?eouts _ =>
        red in Hl; rewrite Forall_forall in Hl;
        specialize (Hl _ Hin); simpl in Hl;
        red in Hl; disc_mii_caseDec
      end.

    Ltac disc_msg_preds Hin :=
      match goal with
      | [H: AtomicMsgOutsInv _ _ _ |- _] =>
        let Hl := fresh "H" in
        pose proof H as Hl;
        disc_msg_preds_with Hl Hin
      end.
    
    Opaque upRq downRq.

    Ltac disc_minds_const :=
      repeat
        match goal with
        | [H: rqEdgeUpFrom ?dtr ?oidx = Some ?midx |- _] =>
          is_const dtr; is_const oidx; is_var midx; inv H
        | [H: rsEdgeUpFrom ?dtr ?oidx = Some ?midx |- _] =>
          is_const dtr; is_const oidx; is_var midx; inv H
        | [H: edgeDownTo ?dtr ?oidx = Some ?midx |- _] =>
          is_const dtr; is_const oidx; is_var midx; inv H
        end.

    Ltac disc_rule_custom ::=
      try disc_footprints_ok;
      try disc_msg_case;
      try disc_AtomicInv;
      try disc_minds_const.

    Lemma msiSv_impl_InvTrs: InvTrs impl ImplStateMSI.
    Proof.
      eapply inv_atomic_InvTrs;
        [red; intros; eapply msiSv_impl_InvTrs_ext_in; eauto
        |red; intros; eapply msiSv_impl_InvTrs_ext_out; eauto
        |].
      instantiate (1:= AtomicInv MsiSvMsgOutPred MsiSvLockPred).
      red; intros.
      destruct H1.
      generalize dependent ist2.
      induction H3; simpl; intros; subst;
        [inv_steps; apply msiSv_impl_InvTrs_init; auto|].

      inv_steps.
      pose proof (footprints_ok msiSv_impl_GoodRqRsSys (reachable_steps H H9))
        as Hftinv.
      specialize (IHAtomic H1 _ H9); dest.
      inv_step; dest_in.

      (** child1 *)

      - atomic_cont_exfalso_bound.
      - atomic_cont_exfalso_bound.

      - (** [childGetRsS] *)
        disc_rule_conds_ex.
        good_footprint_get child1Idx.
        disc_rule_conds_ex.

        (* discharge lock predicates *)
        obj_visited_rsDown child1Idx.
        disc_lock_preds child1Idx.
        disc_rule_conds_ex.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.

        (* generate hints for leaves (L1 caches) *)
        pose proof (parentIdxOf_child_indsOf _ _ H8).
        dest_in; try discriminate; simpl in *.
        cbn in H24; inv H24.

        (* construction *)
        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rsDown_preserves_msg_out_preds; eauto;
                [exact msiSv_impl_RqRsSys
                |red; auto
                |exact msiSvMsgOutPred_good].
            }
            { repeat (constructor; simpl). }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red; simpl.
          eexists.
          right; left.
          red; solve_rule_conds_ex.
          right; solve_rule_conds_ex.
        
      - (** [childDownRqS] *)
        disc_rule_conds_ex.

        (* construction *)
        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqDown_preserves_msg_out_preds; eauto;
                [exact msiSv_impl_RqRsSys
                |red; auto
                |exact msiSvMsgOutPred_good].
            }
            { repeat (constructor; simpl).
              red; simpl.
              mred; simpl; auto.
            }
          * red; simpl; intros.
            icase oidx.
            { mred. }
            { mred; apply H7; auto. }
        + destruct H6 as [cv ?]; simpl in H6.
          exists cv; simpl.
          apply implStateCoherent_downgraded_to_S; auto.
        
      - atomic_cont_exfalso_bound.
      - atomic_cont_exfalso_bound.
      - (** [childSetRsM] *)
        disc_rule_conds_ex.
        good_footprint_get child1Idx.
        disc_rule_conds_ex.

        (* discharge lock predicates *)
        obj_visited_rsDown child1Idx.
        disc_lock_preds child1Idx.
        disc_rule_conds_ex.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.

        (* generate hints for leaves (L1 caches) *)
        pose proof (parentIdxOf_child_indsOf _ _ H8).
        dest_in; try discriminate; simpl in *.
        cbn in H24; inv H24.

        (* construction *)
        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rsDown_preserves_msg_out_preds; eauto;
                [exact msiSv_impl_RqRsSys
                |red; auto
                |exact msiSvMsgOutPred_good].
            }
            { repeat (constructor; simpl). }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red; simpl.
          eexists.
          right; right.
          red; solve_rule_conds_ex.
          left; solve_rule_conds_ex.
          
      - (** [childDownRqM] *)
        disc_rule_conds_ex.

        (* construction *)
        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqDown_preserves_msg_out_preds; eauto;
                [exact msiSv_impl_RqRsSys
                |red; auto
                |exact msiSvMsgOutPred_good].
            }
            { repeat (constructor; simpl).
              red; simpl.
              mred; simpl; auto.
            }
          * red; simpl; intros.
            icase oidx.
            { mred. }
            { mred; apply H7; auto. }
        + destruct H6 as [cv ?]; simpl in H6.
          exists cv; simpl.
          apply implStateCoherent_downgraded_to_I; auto.

      - atomic_cont_exfalso_bound.
      - (** [childEvictRsI] *)
        disc_rule_conds_ex.
        good_footprint_get child1Idx.
        disc_rule_conds_ex.

        (* discharge lock predicates *)
        obj_visited_rsDown child1Idx.
        disc_lock_preds child1Idx.
        disc_rule_conds_ex.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.

        (* generate hints for leaves (L1 caches) *)
        pose proof (parentIdxOf_child_indsOf _ _ H8).
        dest_in; try discriminate; simpl in *.
        cbn in H22; inv H22.

        (* construction *)
        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rsDown_preserves_msg_out_preds; eauto;
                [exact msiSv_impl_RqRsSys
                |red; auto
                |exact msiSvMsgOutPred_good].
            }
            { repeat (constructor; simpl). }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + destruct H6 as [cv ?]; simpl in H6.
          exists cv; simpl.
          apply implStateCoherent_downgraded_to_I; auto.

      (** child2 *)

      - atomic_cont_exfalso_bound.
      - atomic_cont_exfalso_bound.
      - (** [childGetRsS] *)
        disc_rule_conds_ex.
        good_footprint_get child2Idx.
        disc_rule_conds_ex.

        (* discharge lock predicates *)
        obj_visited_rsDown child2Idx.
        disc_lock_preds child2Idx.
        disc_rule_conds_ex.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.

        (* generate hints for leaves (L1 caches) *)
        pose proof (parentIdxOf_child_indsOf _ _ H8).
        dest_in; try discriminate; simpl in *.
        cbn in H24; inv H24.

        (* construction *)
        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rsDown_preserves_msg_out_preds; eauto;
                [exact msiSv_impl_RqRsSys
                |red; auto
                |exact msiSvMsgOutPred_good].
            }
            { repeat (constructor; simpl). }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red; simpl.
          eexists.
          right; left.
          red; solve_rule_conds_ex.
          right; solve_rule_conds_ex.
            
      - (** [childDownRqS] *)
        disc_rule_conds_ex.

        (* construction *)
        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqDown_preserves_msg_out_preds; eauto;
                [exact msiSv_impl_RqRsSys
                |red; auto
                |exact msiSvMsgOutPred_good].
            }
            { repeat (constructor; simpl).
              red; simpl.
              mred; simpl; auto.
            }
          * red; simpl; intros.
            icase oidx.
            { mred. }
            { mred; apply H7; auto. }
        + destruct H6 as [cv ?]; simpl in H6.
          exists cv; simpl.
          apply implStateCoherent_downgraded_to_S; auto.
        
      - atomic_cont_exfalso_bound.
      - atomic_cont_exfalso_bound.
      - (** [childSetRsM] *)
        disc_rule_conds_ex.
        good_footprint_get child2Idx.
        disc_rule_conds_ex.

        (* discharge lock predicates *)
        obj_visited_rsDown child2Idx.
        disc_lock_preds child2Idx.
        disc_rule_conds_ex.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.

        (* generate hints for leaves (L1 caches) *)
        pose proof (parentIdxOf_child_indsOf _ _ H8).
        dest_in; try discriminate; simpl in *.
        cbn in H24; inv H24.

        (* construction *)
        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rsDown_preserves_msg_out_preds; eauto;
                [exact msiSv_impl_RqRsSys
                |red; auto
                |exact msiSvMsgOutPred_good].
            }
            { repeat (constructor; simpl). }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red; simpl.
          eexists.
          right; right.
          red; solve_rule_conds_ex.
          right; left; solve_rule_conds_ex.

      - (** [childDownRqM] *)
        disc_rule_conds_ex.

        (* construction *)
        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqDown_preserves_msg_out_preds; eauto;
                [exact msiSv_impl_RqRsSys
                |red; auto
                |exact msiSvMsgOutPred_good].
            }
            { repeat (constructor; simpl).
              red; simpl.
              mred; simpl; auto.
            }
          * red; simpl; intros.
            icase oidx.
            { mred. }
            { mred; apply H7; auto. }
        + destruct H6 as [cv ?]; simpl in H6.
          exists cv; simpl.
          apply implStateCoherent_downgraded_to_I; auto.

      - atomic_cont_exfalso_bound.
      - (** [childEvictRsI] *)
        disc_rule_conds_ex.
        good_footprint_get child2Idx.
        disc_rule_conds_ex.

        (* discharge lock predicates *)
        obj_visited_rsDown child2Idx.
        disc_lock_preds child2Idx.
        disc_rule_conds_ex.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.

        (* generate hints for leaves (L1 caches) *)
        pose proof (parentIdxOf_child_indsOf _ _ H8).
        dest_in; try discriminate; simpl in *.
        cbn in H22; inv H22.

        (* construction *)
        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rsDown_preserves_msg_out_preds; eauto;
                [exact msiSv_impl_RqRsSys
                |red; auto
                |exact msiSvMsgOutPred_good].
            }
            { repeat (constructor; simpl). }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + destruct H6 as [cv ?]; simpl in H6.
          exists cv; simpl.
          apply implStateCoherent_downgraded_to_I; auto.

      (** parent *)

      - (** [parentGetRqImm] *)
        disc_rule_conds_ex.

        destruct H6 as [cv ?]; simpl in H6.

        (* construction *)
        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqUp_preserves_msg_out_preds
                with (oidx:= child1Idx); eauto.
              { exact msiSv_impl_RqRsSys. }
              { intro; dest_in; discriminate. }
              { red; auto. }
              { reflexivity. }
              { exact msiSvMsgOutPred_good. }
            }
            { admit. }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + replace (oss +[parentIdx <- pos]) with oss by meq.
          exists cv; assumption.

    Admitted.

    Lemma ImplStateMSI_init:
      ImplStateMSI (initsOf impl).
    Proof.
      repeat red.
      exists 0.
      right; left.
      repeat split; right; split; reflexivity.
    Qed.

    Lemma ImplStateMSI_invStep:
      InvStep impl step_m ImplStateMSI.
    Proof.
      apply invSeq_serializable_invStep.
      - apply ImplStateMSI_init.
      - apply inv_trs_seqSteps.
        apply msiSv_impl_InvTrs.
      - eapply rqrs_Serializable.
        apply msiSv_impl_RqRsSys.
    Qed.

  End Facts.
  
End Inv.

Section Sim.

  Local Definition spec := SpecSv.spec 1.
  Local Definition impl := MsiSv.impl.

  (** Simulation between states *)

  Definition SpecState (v: nat) (oss: OStates SpecOStateIfc): Prop.
  Proof.
    refine ((oss@[specIdx]) >>=[False] (fun sost => _)).
    exact (sost#[specValueIdx] = v).
  Defined.

  (** * FIXME: simulation should connect external request/response queues:
   * while connecting them we need to include [RqInfo] as well.
   *)

  Definition SimMSI: MState ImplOStateIfc -> MState SpecOStateIfc -> Prop :=
    fun ist sst =>
      exists cv,
        ImplStateCoherent cv ist.(bst_oss) /\
        SpecState cv sst.(bst_oss).

  Section Facts.

    Lemma SimMsiSv_init:
      SimMSI (initsOf impl) (initsOf spec).
    Proof.
      repeat red.
      exists 0; split.
      - right; left.
        repeat split; right; split; reflexivity.
      - reflexivity.
    Qed.

    Lemma SimMsiSv_sim:
      InvSim step_m step_m ImplStateMSI SimMSI impl spec.
    Proof.
      red; intros.

      (** TODO: simulation proof should be very easy when equipped with 
       *        sufficient invariants, by iterating all possible state 
       *        transitions by rules.
       *        Automate this process.
       *)
      inv H2.
    Admitted.
    
    Theorem MsiSv_ok:
      (steps step_m) # (steps step_m) |-- impl ⊑ spec.
    Proof.
      apply invSim_implies_refinement
        with (ginv:= ImplStateMSI)
             (sim:= SimMSI).
      - apply SimMsiSv_sim.
      - apply ImplStateMSI_invStep.
      - apply SimMsiSv_init.
      - apply ImplStateMSI_init.
    Qed.

  End Facts.
  
End Sim.

