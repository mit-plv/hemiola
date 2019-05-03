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
    (ost#[implStatusIdx] = msiM -> ost#[implValueIdx] = cv) /\
    (ost#[implStatusIdx] = msiS -> ost#[implValueIdx] = cv).

  Definition ImplDirM (ost: OState ImplOStateIfc): Prop :=
    (ost#[implDirIdx].(fst) = msiM /\ ost#[implDirIdx].(snd) = msiI) \/
    (ost#[implDirIdx].(fst) = msiI /\ ost#[implDirIdx].(snd) = msiM).

  Definition ImplDirS (ost: OState ImplOStateIfc): Prop :=
    ost#[implDirIdx].(fst) <= msiS /\
    ost#[implDirIdx].(snd) <= msiS.

  Definition ImplDirI (ost: OState ImplOStateIfc): Prop :=
    ost#[implDirIdx].(fst) = msiI /\
    ost#[implDirIdx].(snd) = msiI.

  (** The first invariant: the directory status is coherent to statuses of
   * children. Note that an object is *not* required to keep the coherency
   * when it is (properly) locked (the meaning of "properly" depends on the
   * protocol).
   *)
  Definition ImplDirCoh (oss: OStates ImplOStateIfc): Prop :=
    post <-- oss@[parentIdx];
      (cost1 <-- oss@[child1Idx];
         cost1#[implStatusIdx] = post#[implDirIdx].(fst)) /\
      (cost2 <-- oss@[child2Idx];
         cost2#[implStatusIdx] = post#[implDirIdx].(snd)).

  (** The second invariant is only for parent, saying that the parent status
   * and its directory status are coherent.
   *)
  Definition ImplParentCoh (cv: nat) (oss: OStates ImplOStateIfc): Prop :=
    post <-- oss@[parentIdx];
      ((ImplOStateM cv post /\ ImplDirI post) \/
       (ImplOStateS cv post /\ ImplDirS post) \/
       (ImplOStateI post /\ ImplDirM post)).

  (** The last invariant is for children, in order for ensuring
   * the local coherency. 
   *)
  Definition ImplChildCoh (cidx: IdxT)
             (cv: nat) (oss: OStates ImplOStateIfc): Prop :=
    cost <-- oss@[cidx]; ImplOStateMSI cv cost.
  
  Definition ImplStateCoh (cv: nat) (oss: OStates ImplOStateIfc): Prop :=
    ImplDirCoh oss /\
    ImplParentCoh cv oss /\
    ImplChildCoh child1Idx cv oss /\
    ImplChildCoh child2Idx cv oss.

  Definition ImplStable (orqs: ORqs Msg): Prop :=
    (porq <-- orqs@[parentIdx]; porq@[downRq] = None) /\
    (corq1 <-- orqs@[child1Idx]; corq1@[upRq] = None) /\
    (corq2 <-- orqs@[child2Idx]; corq2@[upRq] = None).

  Definition ImplStateInv (st: MState ImplOStateIfc): Prop :=
    ImplStable st.(bst_orqs) ->
    exists cv, (* The coherent value always exists. *)
      ImplStateCoh cv st.(bst_oss).
  
  Hint Unfold ImplOStateM ImplOStateS ImplOStateI ImplOStateSI ImplOStateMSI
       ImplDirM ImplDirS ImplDirI
       ImplDirCoh ImplParentCoh ImplChildCoh
       ImplStateCoh ImplStable: RuleConds.

  Ltac disc_msi :=
    try
      match goal with
      | [H: ?t = ?t -> _ |- _] => specialize (H eq_refl)
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
      end.

  Ltac disc_rule_custom ::=
    try disc_msi.
  
  Section Facts.

    Lemma implStateInv_child_orq_invalid:
      forall st oidx orq,
        (oidx = child1Idx \/ oidx = child2Idx) ->
        st.(bst_orqs)@[oidx] = Some orq ->
        orq@[upRq] <> None ->
        ImplStateInv st.
    Proof.
      intros.
      red; intros; exfalso.
      destruct H; solve_rule_conds_ex.
    Qed.

    Lemma implStateCoh_M_value_changed:
      forall cv oss,
        ImplStateCoh cv oss ->
        forall oidx ost,
          (oidx = child1Idx \/ oidx = child2Idx) ->
          oss@[oidx] = Some ost ->
          ost#[implStatusIdx] = msiM ->
          forall n (uv: DirT * unit),
            ImplStateCoh
              n (oss +[oidx <- (n, (msiM, uv))]).
    Proof.
      intros.
      destruct H0.
      - solve_rule_conds_ex.
        + right; right.
          destruct H3 as [|[|]]; try solve_rule_conds_ex.
        + destruct H3 as [|[|]]; try solve_rule_conds_ex.
          destruct H3; solve_rule_conds_ex.
        + destruct H3 as [|[|]]; try solve_rule_conds_ex.
          destruct H3; solve_rule_conds_ex.
      - solve_rule_conds_ex.
        + right; right.
          destruct H3 as [|[|]]; try solve_rule_conds_ex.
        + destruct H3 as [|[|]]; try solve_rule_conds_ex.
          destruct H0; solve_rule_conds_ex.
        + destruct H3 as [|[|]]; try solve_rule_conds_ex.
          destruct H0; solve_rule_conds_ex.
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

    (** * TODO: add proper conditions about directory! *)
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
            post#[implStatusIdx] = msiS /\
            post#[implDirIdx].(fst) = msiS /\
            post#[implDirIdx].(snd) = cost2#[implStatusIdx] /\
            ImplOStateSI post#[implValueIdx] cost2 /\
            msg_value (valOf eout) = VNat post#[implValueIdx]
        | (pc2, msiRsS):
            post <-- oss@[parentIdx];
            cost1 <-- oss@[child1Idx];
            post#[implStatusIdx] = msiS /\
            post#[implDirIdx].(fst) = cost1#[implStatusIdx] /\
            post#[implDirIdx].(snd) = msiS /\
            ImplOStateSI post#[implValueIdx] cost1 /\
            msg_value (valOf eout) = VNat post#[implValueIdx]

        | (pc1, msiRsM):
            post <-- oss@[parentIdx];
            cost2 <-- oss@[child2Idx];
            post#[implStatusIdx] = msiI /\
            post#[implDirIdx].(fst) = msiM /\
            post#[implDirIdx].(snd) = msiI /\
            ImplOStateI cost2
        | (pc2, msiRsM):
            post <-- oss@[parentIdx];
            cost1 <-- oss@[child1Idx];
            post#[implStatusIdx] = msiI /\
            post#[implDirIdx].(fst) = msiI /\
            post#[implDirIdx].(snd) = msiM /\
            ImplOStateI cost1

        | (pc1, msiRsI):
            post <-- oss@[parentIdx];
            cost2 <-- oss@[child2Idx];
            ((post#[implStatusIdx] = msiM /\
              post#[implDirIdx].(fst) = msiI /\
              post#[implDirIdx].(snd) = msiI /\
              ImplOStateI cost2) \/
             (post#[implStatusIdx] = msiS /\
              post#[implDirIdx].(fst) = msiI /\
              post#[implDirIdx].(snd) = cost2#[implStatusIdx] /\
              ImplOStateSI post#[implValueIdx] cost2))
        | (pc2, msiRsI):
            post <-- oss@[parentIdx];
            cost1 <-- oss@[child1Idx];
            ((post#[implStatusIdx] = msiM /\
              post#[implDirIdx].(fst) = msiI /\
              post#[implDirIdx].(snd) = msiI /\
              ImplOStateI cost1) \/
             (post#[implStatusIdx] = msiS /\
              post#[implDirIdx].(fst) = cost1#[implStatusIdx] /\
              post#[implDirIdx].(snd) = msiI /\
              ImplOStateSI post#[implValueIdx] cost1))

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
        eapply implStateInv_child_orq_invalid with (oidx:= child1Idx);
          simpl; eauto; mred.

      - (** [childSetRqImm] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        red; red in H0; simpl in *.
        replace (orqs +[child1Idx <- norq]) with orqs by meq.
        intros.
        specialize (H0 H4).
        destruct H0 as [cv ?].
        exists n; simpl.
        eapply implStateCoh_M_value_changed; eauto.

      - (** [childSetRqM] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        eapply implStateInv_child_orq_invalid with (oidx:= child1Idx);
          simpl; eauto; mred.

      - (** [childEvictRqI] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        eapply implStateInv_child_orq_invalid with (oidx:= child1Idx);
          simpl; eauto; mred.

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
        eapply implStateInv_child_orq_invalid with (oidx:= child2Idx);
          simpl; eauto; mred.

      - (** [childSetRqImm] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        red; red in H0; simpl in *.
        replace (orqs +[child2Idx <- norq]) with orqs by meq.
        intros.
        specialize (H0 H4).
        destruct H0 as [cv ?].
        exists n; simpl.
        eapply implStateCoh_M_value_changed; eauto.

      - (** [childSetRqM] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child2Idx <- pos]) with oss by meq.
        eapply implStateInv_child_orq_invalid with (oidx:= child2Idx);
          simpl; eauto; mred.

      - (** [childEvictRqI] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child2Idx <- pos]) with oss by meq.
        eapply implStateInv_child_orq_invalid with (oidx:= child2Idx);
          simpl; eauto; mred.
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
        + clear H0.
          red; simpl; intros.
          clear H0.
          exists n.
          repeat split.
          * solve_rule_conds_ex.
          * solve_rule_conds_ex.
            right; left.
            solve_rule_conds_ex.
            { unfold msiM, msiS, msiI in *; lia. }
            { unfold msiM, msiS, msiI in *; lia. }
          * solve_rule_conds_ex.
          * solve_rule_conds_ex.
            { unfold msiM, msiS, msiI in *; lia. }
            { inv H30.
              unfold msiM, msiS, msiI in *; lia.
            }
        
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
        + red; simpl; intros.
          exfalso.
          (** TODO: the parent is downlocked; automate reasoning it. *)
          admit.
        
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
        + clear H0.
          red; simpl; intros.
          clear H0.
          exists n.
          repeat split.
          * solve_rule_conds_ex.
          * solve_rule_conds_ex.
            right; right.
            solve_rule_conds_ex.
            left; auto.
          * solve_rule_conds_ex.
          * solve_rule_conds_ex.
            { unfold msiM, msiS, msiI in *; lia. }
            { unfold msiM, msiS, msiI in *; lia. }
          
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
        + red; simpl; intros.
          exfalso.
          (** TODO: the parent is downlocked; automate reasoning it. *)
          admit.

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
        + clear H0.
          red; simpl; intros.
          clear H0.
          exists (ost#[implValueIdx]).
          destruct H24.
          * repeat split.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex.
              left; solve_rule_conds_ex.
            }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex.
              { unfold msiM, msiS, msiI in *; lia. }
              { unfold msiM, msiS, msiI in *; lia. }
            }
          * repeat split.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex.
              right; left.
              solve_rule_conds_ex.
              { unfold msiM, msiS, msiI in *; lia. }
              { unfold msiM, msiS, msiI in *; lia. }
            }
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex.
              { unfold msiM, msiS, msiI in *; lia. }
              { unfold msiM, msiS, msiI in *; lia. }
            }

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
        + clear H0.
          red; simpl; intros.
          clear H0.
          exists n.
          repeat split.
          * solve_rule_conds_ex.
          * solve_rule_conds_ex.
            right; left.
            solve_rule_conds_ex.
            { unfold msiM, msiS, msiI in *; lia. }
            { unfold msiM, msiS, msiI in *; lia. }
          * solve_rule_conds_ex.
            { unfold msiM, msiS, msiI in *; lia. }
            { inv H30.
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
        + red; simpl; intros.
          exfalso.
          (** TODO: the parent is downlocked; automate reasoning it. *)
          admit.
        
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
        + clear H0.
          red; simpl; intros.
          clear H0.
          exists n.
          repeat split.
          * solve_rule_conds_ex.
          * solve_rule_conds_ex.
            right; right.
            solve_rule_conds_ex.
            right; auto.
          * solve_rule_conds_ex.
            { unfold msiM, msiS, msiI in *; lia. }
            { unfold msiM, msiS, msiI in *; lia. }
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
        + red; simpl; intros.
          exfalso.
          (** TODO: the parent is downlocked; automate reasoning it. *)
          admit.

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
        + clear H0.
          red; simpl; intros.
          clear H0.
          exists (ost#[implValueIdx]).
          destruct H24.
          * repeat split.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex.
              left; solve_rule_conds_ex.
            }
            { solve_rule_conds_ex.
              { unfold msiM, msiS, msiI in *; lia. }
              { unfold msiM, msiS, msiI in *; lia. }
            }
            { solve_rule_conds_ex. }
          * repeat split.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex.
              right; left.
              solve_rule_conds_ex.
              { unfold msiM, msiS, msiI in *; lia. }
              { unfold msiM, msiS, msiI in *; lia. }
            }
            { solve_rule_conds_ex.
              { unfold msiM, msiS, msiI in *; lia. }
              { unfold msiM, msiS, msiI in *; lia. }
            }
            { solve_rule_conds_ex. }

      (** parent *)

    Admitted.

    Lemma ImplStateInv_init:
      ImplStateInv (initsOf impl).
    Proof.
      vm_compute.
      intros; dest; exfalso; auto.
    Qed.

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
        ImplStateCoh cv ist.(bst_oss) /\
        SpecState cv sst.(bst_oss).

  Section Facts.

    Lemma SimMsiSv_init:
      SimMSI (initsOf impl) (initsOf spec).
    Proof.
      repeat red.
      exists 0; split.
      - vm_compute; lia.
      - reflexivity.
    Qed.

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

