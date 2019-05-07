Require Import Bool List String Peano_dec.
Require Import Lia. (* experimental *)
Require Import Common FMap HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Msi MsiSv SpecSv MsiSvTopo.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Notation "A <-- OA ; CONT" :=
  (OA >>=[False] (fun A => CONT)) (at level 84, right associativity).
Notation "A <+- OA ; CONT" :=
  (OA >>=[True] (fun A => CONT)) (at level 84, right associativity).
Notation "! OA ; CONT" :=
  (OA = None -> CONT) (at level 84, right associativity).

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
  Forall (fun eout => mp eout nst.(bst_oss) nst.(bst_orqs)) eouts.

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

  (** Basic predicates per an object *)
  
  Definition ImplOStateM (cv: nat) (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] = msiM /\ ost#[implValueIdx] = cv.

  Definition ImplOStateS (cv: nat) (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] = msiS /\ ost#[implValueIdx] = cv.

  Definition ImplOStateI (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] = msiI.

  Definition ImplOStateSI (cv: nat) (ost: OState ImplOStateIfc): Prop :=
    ImplOStateS cv ost \/ ImplOStateI ost.

  Definition ImplOStateMSI (cv: nat) (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] >= msiS -> ost#[implValueIdx] = cv.

  Definition ImplDirM (ost: OState ImplOStateIfc): Prop :=
    (ost#[implDirIdx].(fst) = msiM /\ ost#[implDirIdx].(snd) = msiI) \/
    (ost#[implDirIdx].(fst) = msiI /\ ost#[implDirIdx].(snd) = msiM).

  Definition ImplDirS (ost: OState ImplOStateIfc): Prop :=
    ost#[implDirIdx].(fst) <= msiS /\
    ost#[implDirIdx].(snd) <= msiS.

  Definition ImplDirI (ost: OState ImplOStateIfc): Prop :=
    ost#[implDirIdx].(fst) = msiI /\
    ost#[implDirIdx].(snd) = msiI.

  Section GInv.
    Variables (post cost1 cost2: OState ImplOStateIfc)
              (porq corq1 corq2: ORq Msg).

    (** The first invariant: the directory status is coherent to statuses of
     * children. Note that an object is *not* required to keep the coherency
     * when it is (properly) locked (the meaning of "properly" depends on the
     * protocol).
     *)
    Definition ImplDirCoh: Prop :=
      !porq@[downRq];
        (!corq1@[upRq]; cost1#[implStatusIdx] = post#[implDirIdx].(fst)) /\
        (!corq2@[upRq]; cost2#[implStatusIdx] = post#[implDirIdx].(snd)).
    
    (** The second invariant is only for parent, saying that the parent status
     * and its directory status are coherent.
     *)
    Definition ImplParentCoh (cv: nat): Prop :=
      !porq@[downRq];
      ((ImplOStateM cv post /\ ImplDirI post) \/
       (ImplOStateS cv post /\ ImplDirS post) \/
       (ImplOStateI post /\ ImplDirM post)).

    (** The last invariant is for children, in order for ensuring
     * the local coherency. 
     *)
    Definition ImplChildCoh1 (cv: nat): Prop :=
      !corq1@[upRq]; ImplOStateMSI cv cost1.
    Definition ImplChildCoh2 (cv: nat): Prop :=
      !corq2@[upRq]; ImplOStateMSI cv cost2.

    Definition ImplChildrenCoh: Prop :=
      !corq1@[upRq]; !corq2@[upRq];
        (cost1#[implStatusIdx] = msiM -> cost2#[implStatusIdx] = msiI) /\
        (cost2#[implStatusIdx] = msiM -> cost1#[implStatusIdx] = msiI).
  
    Definition ImplStateCoh (cv: nat): Prop :=
      ImplParentCoh cv /\ 
      ImplChildCoh1 cv /\ ImplChildCoh2 cv /\
      ImplChildrenCoh.

  End GInv.

  Definition ImplStateInv (st: MState ImplOStateIfc): Prop :=
    post <-- (bst_oss st)@[parentIdx];
      cost1 <-- (bst_oss st)@[child1Idx];
      cost2 <-- (bst_oss st)@[child2Idx];
      porq <-- (bst_orqs st)@[parentIdx];
      corq1 <-- (bst_orqs st)@[child1Idx];
      corq2 <-- (bst_orqs st)@[child2Idx];
      (exists cv, ImplStateCoh post cost1 cost2 porq corq1 corq2 cv) /\
      (ImplDirCoh post cost1 cost2 porq corq1 corq2).
  
  Hint Unfold ImplOStateM ImplOStateS ImplOStateI ImplOStateSI ImplOStateMSI
       ImplDirM ImplDirS ImplDirI
       ImplDirCoh ImplParentCoh ImplChildCoh1 ImplChildCoh2 ImplChildrenCoh
       ImplStateCoh: RuleConds.

  Ltac disc_msi :=
    try
      match goal with
      | [H: ?t = ?t -> _ |- _] => specialize (H eq_refl)
      | [H: ?p -> _, Hp: ?p |- _] => specialize (H Hp)
      | [H: VNat ?v = VNat _ |- _] => is_var v; inv H
      | [H: VNat _ = VNat ?v |- _] => is_var v; inv H
      | [H: ?oss@[parentIdx] = Some ?ost |- _] =>
        match type of ost with
        | OState _ =>
          let val := fresh "val" in
          let stt := fresh "stt" in
          let dir := fresh "dir" in
          destruct ost as [val [stt [dir ?]]]
        end
      | [H: ?oss@[child1Idx] = Some ?ost |- _] =>
        match type of ost with
        | OState _ =>
          let val := fresh "val" in
          let stt := fresh "stt" in
          destruct ost as [val [stt ?]]
        end
      | [H: ?oss@[child2Idx] = Some ?ost |- _] =>
        match type of ost with
        | OState _ =>
          let val := fresh "val" in
          let stt := fresh "stt" in
          destruct ost as [val [stt ?]]
        end
      | [H: msiM = _ |- _] => apply eq_sym in H
      | [H: msiS = _ |- _] => apply eq_sym in H
      | [H: msiI = _ |- _] => apply eq_sym in H
      | [H1: ?t = msiM, H2: ?t = msiS |- _] => rewrite H1 in H2; discriminate
      | [H1: ?t = msiM, H2: ?t = msiI |- _] => rewrite H1 in H2; discriminate
      | [H1: ?t = msiS, H2: ?t = msiI |- _] => rewrite H1 in H2; discriminate
      | [H1: ?t = msiM, H2: ?t <= msiS |- _] =>
        rewrite H1 in H2; unfold msiM, msiS in H2; lia
      | [H1: ?t = msiI, H2: ?t >= msiS |- _] =>
        rewrite H1 in H2; unfold msiS, msiI in H2; lia
      end.

  Ltac disc_rule_custom ::=
    try disc_msi.
  
  Section Facts.

    Lemma implStateInv_orqs_weakened:
      forall st oidx orq norq rqt rqi nmsgs,
        ImplStateInv st ->
        (bst_orqs st)@[oidx] = Some orq ->
        norq = orq +[rqt <- rqi] ->
        ImplStateInv {| bst_oss := bst_oss st;
                        bst_orqs := (bst_orqs st) +[oidx <- norq];
                        bst_msgs := nmsgs |}.
    Proof.
      unfold ImplStateInv; simpl; intros.
      disc_rule_conds_const.
      destruct H as [[cv ?] ?].
      solve_rule_conds_ex.
    Qed.

    Lemma implStateCoh_M_value_changed:
      forall st,
        ImplStateInv st ->
        forall oidx ost orq,
          (oidx = child1Idx \/ oidx = child2Idx) ->
          (bst_oss st)@[oidx] = Some ost ->
          ost#[implStatusIdx] = msiM ->
          (bst_orqs st)@[oidx] = Some orq ->
          orq@[upRq] = None ->
          forall n (uv: DirT * unit) nmsgs,
            ImplStateInv
              (Build_MState
                 (oifc:= ImplOStateIfc)
                 ((bst_oss st) +[oidx <- (n, (msiM, uv))])
                 (bst_orqs st) nmsgs).
    Proof.
      unfold ImplStateInv; simpl; intros.
      disc_rule_conds_const.
      destruct H as [[cv ?] ?].
      disc_rule_conds_ex.
      - destruct H0; discriminate.
      - split.
        + exists n; repeat split.
          * disc_rule_conds_ex.
            destruct H as [|[|]]; try (exfalso; solve_rule_conds_ex; fail).
            right; right.
            solve_rule_conds_ex.
          * solve_rule_conds_ex.
            unfold msiM, msiS, msiI in *; lia.
          * solve_rule_conds_ex.
          * solve_rule_conds_ex.
        + solve_rule_conds_ex.
      - split.
        + exists n; repeat split.
          * disc_rule_conds_ex.
            destruct H as [|[|]]; try (exfalso; solve_rule_conds_ex; fail).
            right; right.
            solve_rule_conds_ex.
          * solve_rule_conds_ex.
            unfold msiM, msiS, msiI in *; lia.
          * solve_rule_conds_ex.
          * solve_rule_conds_ex.
        + solve_rule_conds_ex.
      - eauto 6.
    Qed.

    Lemma msiSv_impl_InvTrs_ext_in:
      forall st1 eins st2,
        ImplStateInv st1 ->
        step_m impl st1 (RlblIns eins) st2 ->
        ImplStateInv st2.
    Proof.
      intros; inv_step; assumption.
    Qed.

    Lemma msiSv_impl_InvTrs_ext_out:
      forall st1 eouts st2,
        ImplStateInv st1 ->
        step_m impl st1 (RlblOuts eouts) st2 ->
        ImplStateInv st2.
    Proof.
      intros; inv_step; assumption.
    Qed.

    Definition MsiSvMsgOutPred: MsgOutPred ImplOStateIfc :=
      fun eout oss orqs =>
        match case (miiOf eout) on mii_dec default True with
        | (ec1, Spec.getRq): False
        | (ec1, Spec.setRq): False
        | (ec1, Spec.evictRq): False
        | (ec2, Spec.getRq): False
        | (ec2, Spec.setRq): False
        | (ec2, Spec.evictRq): False

        | (pc1, msiRsS): 
            post <-- oss@[parentIdx];
            porq <-- orqs@[parentIdx];
            post#[implStatusIdx] = msiS /\
            post#[implDirIdx].(fst) = msiS /\
            porq@[downRq] = None /\
            msg_value (valOf eout) = VNat post#[implValueIdx]
        | (pc2, msiRsS):
            post <-- oss@[parentIdx];
            porq <-- orqs@[parentIdx];
            post#[implStatusIdx] = msiS /\
            post#[implDirIdx].(snd) = msiS /\
            porq@[downRq] = None /\
            msg_value (valOf eout) = VNat post#[implValueIdx]

        | (pc1, msiRsM):
            post <-- oss@[parentIdx];
            porq <-- orqs@[parentIdx];
            post#[implStatusIdx] = msiI /\
            post#[implDirIdx].(fst) = msiM /\
            porq@[downRq] = None
        | (pc2, msiRsM):
            post <-- oss@[parentIdx];
            porq <-- orqs@[parentIdx];
            post#[implStatusIdx] = msiI /\
            post#[implDirIdx].(snd) = msiM /\
            porq@[downRq] = None

        | (pc1, msiRsI):
            post <-- oss@[parentIdx];
            ((post#[implStatusIdx] = msiM /\
              post#[implDirIdx].(fst) = msiI) \/
             (post#[implStatusIdx] = msiS /\
              post#[implDirIdx].(fst) = msiI))
        | (pc2, msiRsI):
            post <-- oss@[parentIdx];
            ((post#[implStatusIdx] = msiM /\
              post#[implDirIdx].(snd) = msiI) \/
             (post#[implStatusIdx] = msiS /\
              post#[implDirIdx].(snd) = msiI))

        | (c1pRs, msiDownRsS):
            cost1 <-- oss@[child1Idx];
            cost1#[implStatusIdx] = msiS /\             
            msg_value (valOf eout) = VNat cost1#[implValueIdx]
        | (c2pRs, msiDownRsS):
            cost2 <-- oss@[child2Idx];
            cost2#[implStatusIdx] = msiS /\
            msg_value (valOf eout) = VNat cost2#[implValueIdx]

        | (c1pRs, msiDownRsM):
            cost1 <-- oss@[child1Idx];
            cost1#[implStatusIdx] = msiI
        | (c2pRs, msiDownRsM):
            cost2 <-- oss@[child2Idx];
            cost2#[implStatusIdx] = msiI
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
          ((rqid.(rqi_minds_rss) = [c2pRs] /\ rqid.(rqi_midx_rsb) = pc1) \/
           (rqid.(rqi_minds_rss) = [c1pRs] /\ rqid.(rqi_midx_rsb) = pc2))
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
        | [H: MsiSvMsgOutPred _ _ _ |- _] => red in H
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
        ImplStateInv st1 ->
        forall oidx ridx ins outs st2,
          SubList (idsOf ins) (sys_merqs impl) ->
          step_m impl st1 (RlblInt oidx ridx ins outs) st2 ->
          AtomicInv
            MsiSvMsgOutPred MsiSvLockPred
            ins st1 [RlblInt oidx ridx ins outs] outs st2 /\
          ImplStateInv st2.
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

      (** List of [Rule]s:
       * [childGetRqImm; childGetRqS; childGetRsS; childDownRqS; 
       *  childSetRqImm; childSetRqM; childSetRsM; childDownRqM;
       *  childEvictRqI; childEvictRsI] for [child1Idx] ++
       * [childGetRqImm; childGetRqS; childGetRsS; childDownRqS; 
       *  childSetRqImm; childSetRqM; childSetRsM; childDownRqM;
       *  childEvictRqI; childEvictRsI] for [child2Idx] ++
       * [parentGetRqImm; parentGetDownRqS; parentSetRqImm; parentSetDownRqM;
       *  parentGetDownRsS; parentSetDownRsM;
       *  parentEvictRqImmS; parentEvictRqImmLastS; parentEvictRqImmM] * 2
       *)

      3, 7, 10, 13, 17, 20: atomic_init_exfalso_rs_from_parent.
      all: try (atomic_init_exfalso_rq; fail).

      - (** [childGetRqImm] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        replace (orqs +[child1Idx <- norq]) with orqs by meq.
        assumption.

      - (** [childGetRqS] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        eapply implStateInv_orqs_weakened in H0; eauto.

      - (** [childSetRqImm] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (orqs +[child1Idx <- norq]) with orqs by meq.
        eapply implStateCoh_M_value_changed in H0; eauto.

      - (** [childSetRqM] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        eapply implStateInv_orqs_weakened in H0; eauto.

      - (** [childEvictRqI] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        eapply implStateInv_orqs_weakened in H0; eauto.

      - (** [childGetRqImm] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child2Idx <- pos]) with oss by meq.
        replace (orqs +[child2Idx <- norq]) with orqs by meq.
        assumption.

      - (** [childGetRqS] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child2Idx <- pos]) with oss by meq.
        eapply implStateInv_orqs_weakened in H0; eauto.

      - (** [childSetRqImm] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (orqs +[child2Idx <- norq]) with orqs by meq.
        eapply implStateCoh_M_value_changed in H0; eauto.

      - (** [childSetRqM] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child2Idx <- pos]) with oss by meq.
        eapply implStateInv_orqs_weakened in H0; eauto.

      - (** [childEvictRqI] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child2Idx <- pos]) with oss by meq.
        eapply implStateInv_orqs_weakened in H0; eauto.
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

    Ltac obj_visited_rsUp oidx ocidx :=
      try match goal with
          | [Ha: Atomic _ _ _ ?hst _ _ |- _] =>
            assert (In parentIdx (oindsOf hst))
              by (eapply extAtomic_rsUp_acceptor_visited
                    with (cidx:= ocidx); eauto;
                  [exact msiSv_impl_RqRsSys
                  |econstructor; eassumption
                  |red; auto
                  |reflexivity])
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
      try disc_msi;
      try disc_minds_const.

    Lemma msiSv_impl_InvTrs: InvTrs impl ImplStateInv.
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
      pose proof (upLockInv_ok
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree (reachable_steps H H9)) as Hulinv.
      pose proof (downLockInv_ok
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree
                    msiSv_impl_GoodExtRssSys (reachable_steps H H9)) as Hdlinv.
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
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child2Idx]) as [cost2|]; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|]; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          split.
          * exists val0.
            red; repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex.
              unfold msiM, msiS, msiI in *; lia.
            }
            { solve_rule_conds_ex.
              unfold msiM, msiS, msiI in *; lia.
            }
          * solve_rule_conds_ex.

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
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[parentIdx]) as [post|] eqn:Hpost; simpl in *; [|auto].
          destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
          destruct (orqs@[parentIdx]) as [porq|] eqn:Hporq; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          split.
          * exists cv.
            red; repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex.
              unfold msiM, msiS, msiI in *; lia.
            }
          * disc_rule_conds_ex.
            exfalso.
            assert (In parent (sys_objs impl)) by (simpl; tauto).
            good_locking_get parent.
            clear H24.
            eapply downLockInvORq_down_rqsQ_length_one_locked
              with (cidx:= child1Idx) in H27; eauto;
              [|reflexivity
               |eapply rqsQ_length_ge_one; [eauto|apply FirstMP_InMP; assumption]].
            destruct H27 as [rqid [? [? [rsUp ?]]]]; dest.
            disc_rule_conds_ex.

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
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child2Idx]) as [cost2|]; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|]; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          split.
          * exists n.
            red; repeat ssplit.
            { solve_rule_conds_ex.
              destruct H6 as [|[|]]; try (exfalso; dest; discriminate).
              right; right; solve_rule_conds_ex.
            }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex.
              unfold msiM, msiS, msiI in *; lia.
            }
            { solve_rule_conds_ex.
              { unfold msiM, msiS, msiI in *; lia. }
              { unfold msiM, msiS, msiI in *; lia. }
            }
          * solve_rule_conds_ex.

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
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[parentIdx]) as [post|] eqn:Hpost; simpl in *; [|auto].
          destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
          destruct (orqs@[parentIdx]) as [porq|] eqn:Hporq; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          split.
          * exists cv.
            red; repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * disc_rule_conds_ex.
            exfalso.
            assert (In parent (sys_objs impl)) by (simpl; tauto).
            good_locking_get parent.
            clear H24.
            eapply downLockInvORq_down_rqsQ_length_one_locked
              with (cidx:= child1Idx) in H27; eauto;
              [|reflexivity
               |eapply rqsQ_length_ge_one; [eauto|apply FirstMP_InMP; assumption]].
            destruct H27 as [rqid [? [? [rsUp ?]]]]; dest.
            disc_rule_conds_ex.

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
        + red in H6; red; simpl in *; mred; simpl.
          rename porq into orq.
          destruct (oss@[child2Idx]) as [cost2|]; simpl in *; [|auto].
          destruct (orqs@[parentIdx]) as [porq|]; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|]; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          split.
          * exists cv.
            clear H22.
            red; repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex.
              unfold msiM, msiS, msiI in *; lia.
            }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * destruct H24.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }

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
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|]; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|]; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          split.
          * exists val0.
            red; repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex.
              unfold msiM, msiS, msiI in *; lia.
            }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex.
              unfold msiM, msiS, msiI in *; lia.
            }
          * solve_rule_conds_ex.

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
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[parentIdx]) as [post|] eqn:Hpost; simpl in *; [|auto].
          destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
          destruct (orqs@[parentIdx]) as [porq|] eqn:Hporq; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          split.
          * exists cv.
            red; repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex.
              unfold msiM, msiS, msiI in *; lia.
            }
          * disc_rule_conds_ex.
            exfalso.
            assert (In parent (sys_objs impl)) by (simpl; tauto).
            good_locking_get parent.
            clear H24.
            eapply downLockInvORq_down_rqsQ_length_one_locked
              with (cidx:= child2Idx) in H27; eauto;
              [|reflexivity
               |eapply rqsQ_length_ge_one; [eauto|apply FirstMP_InMP; assumption]].
            destruct H27 as [rqid [? [? [rsUp ?]]]]; dest.
            disc_rule_conds_ex.
        
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
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|]; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|]; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          split.
          * exists n.
            red; repeat ssplit.
            { solve_rule_conds_ex.
              destruct H6 as [|[|]]; try (exfalso; dest; discriminate).
              right; right; solve_rule_conds_ex.
            }
            { solve_rule_conds_ex.
              unfold msiM, msiS, msiI in *; lia.
            }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex.
              { unfold msiM, msiS, msiI in *; lia. }
              { unfold msiM, msiS, msiI in *; lia. }
            }
          * solve_rule_conds_ex.
          
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
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[parentIdx]) as [post|] eqn:Hpost; simpl in *; [|auto].
          destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
          destruct (orqs@[parentIdx]) as [porq|] eqn:Hporq; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          split.
          * exists cv.
            red; repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * disc_rule_conds_ex.
            exfalso.
            assert (In parent (sys_objs impl)) by (simpl; tauto).
            good_locking_get parent.
            clear H24.
            eapply downLockInvORq_down_rqsQ_length_one_locked
              with (cidx:= child2Idx) in H27; eauto;
              [|reflexivity
               |eapply rqsQ_length_ge_one; [eauto|apply FirstMP_InMP; assumption]].
            destruct H27 as [rqid [? [? [rsUp ?]]]]; dest.
            disc_rule_conds_ex.

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
        + red in H6; red; simpl in *; mred; simpl.
          rename porq into orq.
          destruct (oss@[child1Idx]) as [cost1|]; simpl in *; [|auto].
          destruct (orqs@[parentIdx]) as [porq|]; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|]; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          split.
          * exists cv.
            red; repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex.
              unfold msiM, msiS, msiI in *; lia.
            }
            { solve_rule_conds_ex. }
          * destruct H24.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }

      (** parent(child1) *)

      - (** [parentGetRqImm] *)
        disc_rule_conds_ex.

        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqUp_preserves_msg_out_preds
                with (oidx:= child1Idx); [exact msiSv_impl_RqRsSys|..]; eauto.
              { intro; dest_in; discriminate. }
              { red; auto. }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl).
              red; repeat (simpl; mred).
            }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
          destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          split.
          * exists cv.
            clear H8.
            red; repeat ssplit.
            { solve_rule_conds_ex.
              right; left.
              destruct H6 as [|[|]].
              { solve_rule_conds_ex.
                unfold msiM, msiS, msiI in *; lia.
              }
              { solve_rule_conds_ex. }
              { unfold msiM, msiS, msiI in *; lia. }
            }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * disc_rule_conds_ex.
            assert (In (child child1Idx ec1 ce1 c1pRq c1pRs pc1) (sys_objs impl))
              by (simpl; tauto).
            good_locking_get (child child1Idx ec1 ce1 c1pRq c1pRs pc1).
            clear H24.
            eapply upLockInvORq_rqUp_length_one_locked in H26; try reflexivity;
              [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
            solve_rule_conds_ex.

      - (** [parentGetDownRqS] *)
        disc_rule_conds_ex.

        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqUp_preserves_msg_out_preds
                with (oidx:= child1Idx); [exact msiSv_impl_RqRsSys|..]; eauto.
              { intro; dest_in; discriminate. }
              { red; auto. }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl). }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred).
              simpl; left; auto.
            }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|]; simpl in *; [|auto].
          destruct (oss@[child2Idx]) as [cost2|]; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|]; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|]; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          split.
          * exists cv.
            clear H8.
            red; repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * solve_rule_conds_ex.

      - (** [parentSetRqImm] *)
        disc_rule_conds_ex.

        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqUp_preserves_msg_out_preds
                with (oidx:= child1Idx); [exact msiSv_impl_RqRsSys|..]; eauto.
              { intro; dest_in; discriminate. }
              { red; auto. }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl).
              red; repeat (simpl; mred).
            }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
          destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          unfold getDir in H14; simpl in H14.
          split.
          * exists cv.
            red; repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * disc_rule_conds_ex.
            assert (In (child child1Idx ec1 ce1 c1pRq c1pRs pc1) (sys_objs impl))
              by (simpl; tauto).
            good_locking_get (child child1Idx ec1 ce1 c1pRq c1pRs pc1).
            clear H24.
            eapply upLockInvORq_rqUp_length_one_locked in H26; try reflexivity;
              [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
            solve_rule_conds_ex.

      - (** [parentSetDownRqM] *)
        disc_rule_conds_ex.

        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqUp_preserves_msg_out_preds
                with (oidx:= child1Idx); [exact msiSv_impl_RqRsSys|..]; eauto.
              { intro; dest_in; discriminate. }
              { red; auto. }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl). }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred).
              simpl; left; auto.
            }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|]; simpl in *; [|auto].
          destruct (oss@[child2Idx]) as [cost2|]; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|]; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|]; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          split.
          * exists cv.
            clear H8.
            red; repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * solve_rule_conds_ex.

      - (** [parentGetDownRsS] *)
        disc_rule_conds_ex.

        obj_visited_rsUp parentIdx child2Idx.
        disc_lock_preds parentIdx.
        disc_rule_conds_ex.
        destruct H11; dest; [|discriminate].
        clear H11.
        disc_rule_conds_ex.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.
        
        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rsUps_preserves_msg_out_preds
                with (rsUps:= [(c2pRs, rmsg)]); eauto.
              { exact msiSv_impl_RqRsSys. }
              { repeat constructor; intro; dest_in. }
              { apply SubList_cons; [|apply SubList_nil].
                assumption.
              }
              { instantiate (1:= fun _ => True).
                instantiate (1:= [pc2]).
                repeat split.
                { discriminate. }
                { repeat constructor.
                  simpl; exists child2Idx.
                  repeat split.
                }
              }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl).
              red; simpl.
              solve_rule_conds_ex.
            }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.

          assert (In (child child1Idx ec1 ce1 c1pRq c1pRs pc1) (sys_objs impl))
            by (simpl; tauto).
          good_locking_get (child child1Idx ec1 ce1 c1pRq c1pRs pc1).
          clear H24.
          eapply upLockInvORq_parent_locked_locked in H26; try reflexivity;
            [|red; repeat (simpl; mred); eauto]; dest.
          
          split.
          * exists val0.
            clear H11.
            red; repeat ssplit.
            { solve_rule_conds_ex.
              right; left; auto.
            }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * solve_rule_conds_ex.

      - (** [parentSetDownRsM] *)
        disc_rule_conds_ex.

        obj_visited_rsUp parentIdx child2Idx.
        disc_lock_preds parentIdx.
        disc_rule_conds_ex.
        destruct H11; dest; [|discriminate].
        clear H11.
        disc_rule_conds_ex.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.
        
        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rsUps_preserves_msg_out_preds
                with (rsUps:= [(c2pRs, rmsg)]); eauto.
              { exact msiSv_impl_RqRsSys. }
              { repeat constructor; intro; dest_in. }
              { apply SubList_cons; [|apply SubList_nil].
                assumption.
              }
              { instantiate (1:= fun _ => True).
                instantiate (1:= [pc2]).
                repeat split.
                { discriminate. }
                { repeat constructor.
                  simpl; exists child2Idx.
                  repeat split.
                }
              }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl).
              red; simpl.
              solve_rule_conds_ex.
            }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.

          assert (In (child child1Idx ec1 ce1 c1pRq c1pRs pc1) (sys_objs impl))
            by (simpl; tauto).
          good_locking_get (child child1Idx ec1 ce1 c1pRq c1pRs pc1).
          clear H24.
          eapply upLockInvORq_parent_locked_locked in H26; try reflexivity;
            [|red; repeat (simpl; mred); eauto]; dest.

          split.
          * exists val0.
            clear H11.
            red; repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * solve_rule_conds_ex.

      - (** [parentEvictRqImmS] *)
        disc_rule_conds_ex.

        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqUp_preserves_msg_out_preds
                with (oidx:= child1Idx); [exact msiSv_impl_RqRsSys|..]; eauto.
              { intro; dest_in; discriminate. }
              { red; auto. }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl).
              red; repeat (simpl; mred).
              red in H6; simpl in H6.
              unfold getDir in *; simpl in *.
              disc_rule_conds_ex.
              destruct H6 as [|[|]]; dest.
              { exfalso; solve_rule_conds_ex. }
              { subst; auto. }
              { exfalso; destruct H26; solve_rule_conds_ex. }
            }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
          destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          unfold getDir in *; simpl in *.
          disc_rule_conds_ex.
          destruct H6 as [|[|]];
            [exfalso; solve_rule_conds_ex
            | |exfalso; destruct H6 as [? [|]]; solve_rule_conds_ex].
          
          split.
          * exists cv.
            repeat ssplit.
            { solve_rule_conds_ex.
              right; left.
              unfold msiM, msiS, msiI in *; lia.
            }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * disc_rule_conds_ex.
            assert (In (child child1Idx ec1 ce1 c1pRq c1pRs pc1) (sys_objs impl))
              by (simpl; tauto).
            good_locking_get (child child1Idx ec1 ce1 c1pRq c1pRs pc1).
            clear H6.
            eapply upLockInvORq_rqUp_length_one_locked in H28; try reflexivity;
              [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
            solve_rule_conds_ex.

      - (** [parentEvictRqImmLastS] *)
        disc_rule_conds_ex.

        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqUp_preserves_msg_out_preds
                with (oidx:= child1Idx); [exact msiSv_impl_RqRsSys|..]; eauto.
              { intro; dest_in; discriminate. }
              { red; auto. }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl).
              red; repeat (simpl; mred).
              lia.
            }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
          destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          unfold getDir in *; simpl in *.
          disc_rule_conds_ex.
          destruct H6 as [|[|]];
            [exfalso; solve_rule_conds_ex
            | |exfalso; destruct H6 as [? [|]]; solve_rule_conds_ex].
          
          split.
          * exists cv.
            repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * disc_rule_conds_ex.
            assert (In (child child1Idx ec1 ce1 c1pRq c1pRs pc1) (sys_objs impl))
              by (simpl; tauto).
            good_locking_get (child child1Idx ec1 ce1 c1pRq c1pRs pc1).
            clear H6.
            eapply upLockInvORq_rqUp_length_one_locked in H28; try reflexivity;
              [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
            solve_rule_conds_ex.

      - (** [parentEvictRqImmM] *)
        disc_rule_conds_ex.

        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqUp_preserves_msg_out_preds
                with (oidx:= child1Idx); [exact msiSv_impl_RqRsSys|..]; eauto.
              { intro; dest_in; discriminate. }
              { red; auto. }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl).
              red; repeat (simpl; mred).
              lia.
            }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
          destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          unfold getDir in *; simpl in *.
          disc_rule_conds_ex.
          destruct H6 as [|[|]]; try (exfalso; solve_rule_conds_ex; fail).

          assert (In (child child1Idx ec1 ce1 c1pRq c1pRs pc1) (sys_objs impl))
            by (simpl; tauto).
          good_locking_get (child child1Idx ec1 ce1 c1pRq c1pRs pc1).
          clear H26.
          eapply upLockInvORq_rqUp_length_one_locked in H27; try reflexivity;
            [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
          disc_rule_conds_ex.
          
          split.
          * exists n.
            repeat ssplit.
            { solve_rule_conds_ex.
              left.
              unfold msiM, msiS, msiI in *; lia.
            }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex.
              unfold msiM, msiS, msiI in *; lia.
            }
            { solve_rule_conds_ex. }
          * solve_rule_conds_ex.

      (** parent(child2) *)

      - (** [parentGetRqImm] *)
        disc_rule_conds_ex.

        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqUp_preserves_msg_out_preds
                with (oidx:= child2Idx); [exact msiSv_impl_RqRsSys|..]; eauto.
              { intro; dest_in; discriminate. }
              { red; auto. }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl).
              red; repeat (simpl; mred).
            }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
          destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          split.
          * exists cv.
            clear H8.
            red; repeat ssplit.
            { solve_rule_conds_ex.
              right; left.
              destruct H6 as [|[|]].
              { solve_rule_conds_ex.
                unfold msiM, msiS, msiI in *; lia.
              }
              { solve_rule_conds_ex. }
              { unfold msiM, msiS, msiI in *; lia. }
            }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * disc_rule_conds_ex.
            assert (In (child child2Idx ec2 ce2 c2pRq c2pRs pc2) (sys_objs impl))
              by (simpl; tauto).
            good_locking_get (child child2Idx ec2 ce2 c2pRq c2pRs pc2).
            clear H24.
            eapply upLockInvORq_rqUp_length_one_locked in H26; try reflexivity;
              [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
            solve_rule_conds_ex.

      - (** [parentGetDownRqS] *)
        disc_rule_conds_ex.

        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqUp_preserves_msg_out_preds
                with (oidx:= child2Idx); [exact msiSv_impl_RqRsSys|..]; eauto.
              { intro; dest_in; discriminate. }
              { red; auto. }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl). }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred).
              simpl; right; auto.
            }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|]; simpl in *; [|auto].
          destruct (oss@[child2Idx]) as [cost2|]; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|]; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|]; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          split.
          * exists cv.
            clear H8.
            red; repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * solve_rule_conds_ex.

      - (** [parentSetRqImm] *)
        disc_rule_conds_ex.

        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqUp_preserves_msg_out_preds
                with (oidx:= child2Idx); [exact msiSv_impl_RqRsSys|..]; eauto.
              { intro; dest_in; discriminate. }
              { red; auto. }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl).
              red; repeat (simpl; mred).
            }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
          destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          unfold getDir in H14; simpl in H14.
          split.
          * exists cv.
            red; repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * disc_rule_conds_ex.
            assert (In (child child2Idx ec2 ce2 c2pRq c2pRs pc2) (sys_objs impl))
              by (simpl; tauto).
            good_locking_get (child child2Idx ec2 ce2 c2pRq c2pRs pc2).
            clear H24.
            eapply upLockInvORq_rqUp_length_one_locked in H26; try reflexivity;
              [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
            solve_rule_conds_ex.

      - (** [parentSetDownRqM] *)
        disc_rule_conds_ex.

        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqUp_preserves_msg_out_preds
                with (oidx:= child2Idx); [exact msiSv_impl_RqRsSys|..]; eauto.
              { intro; dest_in; discriminate. }
              { red; auto. }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl). }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred).
              simpl; right; auto.
            }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|]; simpl in *; [|auto].
          destruct (oss@[child2Idx]) as [cost2|]; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|]; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|]; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          split.
          * exists cv.
            clear H8.
            red; repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * solve_rule_conds_ex.

      - (** [parentGetDownRsS] *)
        disc_rule_conds_ex.

        obj_visited_rsUp parentIdx child1Idx.
        disc_lock_preds parentIdx.
        disc_rule_conds_ex.
        destruct H11; dest; [discriminate|].
        clear H11.
        disc_rule_conds_ex.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.
        
        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rsUps_preserves_msg_out_preds
                with (rsUps:= [(c1pRs, rmsg)]); eauto.
              { exact msiSv_impl_RqRsSys. }
              { repeat constructor; intro; dest_in. }
              { apply SubList_cons; [|apply SubList_nil].
                assumption.
              }
              { instantiate (1:= fun _ => True).
                instantiate (1:= [pc1]).
                repeat split.
                { discriminate. }
                { repeat constructor.
                  simpl; exists child1Idx.
                  repeat split.
                }
              }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl).
              red; simpl.
              solve_rule_conds_ex.
            }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.

          assert (In (child child2Idx ec2 ce2 c2pRq c2pRs pc2) (sys_objs impl))
            by (simpl; tauto).
          good_locking_get (child child2Idx ec2 ce2 c2pRq c2pRs pc2).
          clear H24.
          eapply upLockInvORq_parent_locked_locked in H26; try reflexivity;
            [|red; repeat (simpl; mred); eauto]; dest.
          
          split.
          * exists val0.
            clear H11.
            red; repeat ssplit.
            { solve_rule_conds_ex.
              right; left; auto.
            }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * solve_rule_conds_ex.

      - (** [parentSetDownRsM] *)
        disc_rule_conds_ex.

        obj_visited_rsUp parentIdx child1Idx.
        disc_lock_preds parentIdx.
        disc_rule_conds_ex.
        destruct H11; dest; [discriminate|].
        clear H11.
        disc_rule_conds_ex.

        (* discharge message predicates *)
        disc_msg_preds H4.
        disc_rule_conds_ex.
        
        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rsUps_preserves_msg_out_preds
                with (rsUps:= [(c1pRs, rmsg)]); eauto.
              { exact msiSv_impl_RqRsSys. }
              { repeat constructor; intro; dest_in. }
              { apply SubList_cons; [|apply SubList_nil].
                assumption.
              }
              { instantiate (1:= fun _ => True).
                instantiate (1:= [pc1]).
                repeat split.
                { discriminate. }
                { repeat constructor.
                  simpl; exists child1Idx.
                  repeat split.
                }
              }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl).
              red; simpl.
              solve_rule_conds_ex.
            }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost1; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.

          assert (In (child child2Idx ec2 ce2 c2pRq c2pRs pc2) (sys_objs impl))
            by (simpl; tauto).
          good_locking_get (child child2Idx ec2 ce2 c2pRq c2pRs pc2).
          clear H24.
          eapply upLockInvORq_parent_locked_locked in H26; try reflexivity;
            [|red; repeat (simpl; mred); eauto]; dest.

          split.
          * exists val0.
            clear H11.
            red; repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * solve_rule_conds_ex.

      - (** [parentEvictRqImmS] *)
        disc_rule_conds_ex.

        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqUp_preserves_msg_out_preds
                with (oidx:= child2Idx); [exact msiSv_impl_RqRsSys|..]; eauto.
              { intro; dest_in; discriminate. }
              { red; auto. }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl).
              red; repeat (simpl; mred).
              red in H6; simpl in H6.
              unfold getDir in *; simpl in *.
              disc_rule_conds_ex.
              destruct H6 as [|[|]]; dest.
              { exfalso; solve_rule_conds_ex. }
              { subst; auto. }
              { exfalso; destruct H26; solve_rule_conds_ex. }
            }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
          destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          unfold getDir in *; simpl in *.
          disc_rule_conds_ex.
          destruct H6 as [|[|]];
            [exfalso; solve_rule_conds_ex
            | |exfalso; destruct H6 as [? [|]]; solve_rule_conds_ex].
          
          split.
          * exists cv.
            repeat ssplit.
            { solve_rule_conds_ex.
              right; left.
              unfold msiM, msiS, msiI in *; lia.
            }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * disc_rule_conds_ex.
            assert (In (child child2Idx ec2 ce2 c2pRq c2pRs pc2) (sys_objs impl))
              by (simpl; tauto).
            good_locking_get (child child2Idx ec2 ce2 c2pRq c2pRs pc2).
            clear H6.
            eapply upLockInvORq_rqUp_length_one_locked in H28; try reflexivity;
              [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
            solve_rule_conds_ex.

      - (** [parentEvictRqImmLastS] *)
        disc_rule_conds_ex.

        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqUp_preserves_msg_out_preds
                with (oidx:= child2Idx); [exact msiSv_impl_RqRsSys|..]; eauto.
              { intro; dest_in; discriminate. }
              { red; auto. }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl).
              red; repeat (simpl; mred).
              lia.
            }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
          destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          unfold getDir in *; simpl in *.
          disc_rule_conds_ex.
          destruct H6 as [|[|]];
            [exfalso; solve_rule_conds_ex
            | |exfalso; destruct H6 as [? [|]]; solve_rule_conds_ex].
          
          split.
          * exists cv.
            repeat ssplit.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * disc_rule_conds_ex.
            assert (In (child child2Idx ec2 ce2 c2pRq c2pRs pc2) (sys_objs impl))
              by (simpl; tauto).
            good_locking_get (child child2Idx ec2 ce2 c2pRq c2pRs pc2).
            clear H6.
            eapply upLockInvORq_rqUp_length_one_locked in H28; try reflexivity;
              [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
            solve_rule_conds_ex.

      - (** [parentEvictRqImmM] *)
        disc_rule_conds_ex.

        split.
        + split.
          * apply Forall_app.
            { apply forall_removeOnce.
              eapply atomic_rqUp_preserves_msg_out_preds
                with (oidx:= child2Idx); [exact msiSv_impl_RqRsSys|..]; eauto.
              { intro; dest_in; discriminate. }
              { red; auto. }
              { exact msiSvMsgOutPred_good. }
            }
            { repeat (constructor; simpl).
              red; repeat (simpl; mred).
              lia.
            }
          * red; simpl; intros.
            icase oidx.
            { repeat (simpl; red; mred). }
            { mred; apply H7; auto. }
        + red in H6; red; simpl in *; mred; simpl.
          destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|auto].
          destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|auto].
          destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|auto].
          destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|auto].
          destruct H6 as [[cv ?] ?].
          red in H6; dest.
          unfold getDir in *; simpl in *.
          disc_rule_conds_ex.
          destruct H6 as [|[|]]; try (exfalso; solve_rule_conds_ex; fail).

          assert (In (child child2Idx ec2 ce2 c2pRq c2pRs pc2) (sys_objs impl))
            by (simpl; tauto).
          good_locking_get (child child2Idx ec2 ce2 c2pRq c2pRs pc2).
          clear H26.
          eapply upLockInvORq_rqUp_length_one_locked in H27; try reflexivity;
            [|eapply findQ_length_ge_one; apply FirstMP_InMP; eassumption].
          disc_rule_conds_ex.
          
          split.
          * exists n.
            repeat ssplit.
            { solve_rule_conds_ex.
              left.
              unfold msiM, msiS, msiI in *; lia.
            }
            { solve_rule_conds_ex.
              unfold msiM, msiS, msiI in *; lia.
            }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
          * solve_rule_conds_ex.

    Qed.

    Lemma ImplStateInv_init:
      ImplStateInv (initsOf impl).
    Proof.
      vm_compute.
      (* TODO: need [sys_orqs_inits].. *)
    Admitted.

    Lemma ImplStateInv_invStep:
      InvStep impl step_m ImplStateInv.
    Proof.
      apply invSeq_serializable_invStep.
      - apply ImplStateInv_init.
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
        (* ImplStateInv cv ist.(bst_oss) /\ *) (** FIXME *)
        SpecState cv sst.(bst_oss).

  Section Facts.

    Lemma SimMsiSv_init:
      SimMSI (initsOf impl) (initsOf spec).
    Proof.
      (* repeat red. *)
      (* exists 0; split. *)
      (* - vm_compute; lia. *)
      (* - reflexivity. *)
    Admitted.

    Lemma SimMsiSv_sim:
      InvSim step_m step_m ImplStateInv SimMSI impl spec.
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
        with (ginv:= ImplStateInv)
             (sim:= SimMSI).
      - apply SimMsiSv_sim.
      - apply ImplStateInv_invStep.
      - apply SimMsiSv_init.
      - apply ImplStateInv_init.
    Qed.

  End Facts.
  
End Sim.

