Require Import Bool List String Peano_dec.
Require Import Common FMap HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsTopo RqRsFacts RqRsLang.
Require Import RqRsInvLock RqRsMsgPred RqRsCorrect.

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
           (abf: list Mii -> list Mii)
           (inits eouts: list (Id Msg)) (nst: MState oifc): Prop :=
  SubList (miisOf eouts) (abf (miisOf inits)) /\
  Forall (fun eout => mp eout nst.(bst_oss)) eouts.

Definition AtomicLocksInv {oifc}
           (lp: list Mii -> IdxT -> ORq Msg -> Prop)
           (inits: list (Id Msg)) (hst: MHistory) (nst: MState oifc): Prop :=
  forall oidx,
    In oidx (oindsOf hst) ->
    orq <-- (bst_orqs nst)@[oidx]; lp (miisOf inits) oidx orq.

Definition AtomicInv {oifc}
           (mp: MsgOutPred oifc) (abf: list Mii -> list Mii)
           (lp: list Mii -> IdxT -> ORq Msg -> Prop):
  list (Id Msg) (* inits *) ->
  MState oifc (* starting state *) ->
  MHistory (* atomic history *) ->
  list (Id Msg) (* eouts *) ->
  MState oifc (* ending state *) -> Prop :=
  fun inits st1 hst eouts st2 =>
    AtomicMsgOutsInv mp abf inits eouts st2 /\
    AtomicLocksInv lp inits hst st2.

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
           (ImplOStateI cost1 /\ ImplOStateM cv cost2)).
  Defined.

  Definition ImplStateCoherent
             (cv: nat) (oss: OStates ImplOStateIfc): Prop :=
    ImplStateI oss \/ ImplStateS cv oss \/ ImplStateM cv oss.
  
  Definition ImplStateMSI (st: MState ImplOStateIfc): Prop :=
    exists cv, (* The coherent value always exists. *)
      ImplStateCoherent cv st.(bst_oss).

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
      intros.
      destruct H as [|[|]].
      - exfalso; red in H.
        disc_rule_conds_ex.
        destruct H0; subst.
        + disc_rule_conds_ex.
          red in H3; simpl in H3.
          rewrite H3 in H2; discriminate.
        + disc_rule_conds_ex.
          red in H4; simpl in H4.
          rewrite H4 in H2; discriminate.
      - exfalso; red in H.
        disc_rule_conds_ex.
        destruct H0; subst.
        + disc_rule_conds_ex.
          destruct H3;
            try (dest; simpl in H0; rewrite H0 in H2; discriminate).
        + disc_rule_conds_ex.
          destruct H4;
            try (dest; simpl in H0; rewrite H0 in H2; discriminate).
      - right; right.
        red in H.
        disc_rule_conds_ex.
        destruct H0; subst.
        + destruct H3; dest.
          * red; red in H0, H3; dest.
            solve_rule_conds_ex.
            left; solve_rule_conds_ex.
          * red; red in H0, H3; dest.
            solve_rule_conds_ex.
            left; solve_rule_conds_ex.
        + destruct H3; dest.
          * red; red in H0, H3; dest.
            solve_rule_conds_ex.
            right; solve_rule_conds_ex.
          * red; red in H0, H3; dest.
            solve_rule_conds_ex.
            right; solve_rule_conds_ex.
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
        | (pc1, msiRsS): 
            post <-- oss@[parentIdx];
            cost2 <-- oss@[child2Idx];
            (post#[implStatusIdx] = msiS /\
             cost2#[implStatusIdx] = msiS /\
             msg_value (valOf eout) = VNat post#[implValueIdx])
        | (pc2, msiRsS):
            post <-- oss@[parentIdx];
            cost1 <-- oss@[child1Idx];
            (post#[implStatusIdx] = msiS /\
             cost1#[implStatusIdx] = msiS /\
             msg_value (valOf eout) = VNat post#[implValueIdx])
        | (pc1, msiRsM): 
            post <-- oss@[parentIdx];
            cost2 <-- oss@[child2Idx];
            (post#[implStatusIdx] = msiM /\ cost2#[implStatusIdx] = msiI)
        | (pc2, msiRsM):
            post <-- oss@[parentIdx];
            cost1 <-- oss@[child1Idx];
            (post#[implStatusIdx] = msiM /\ cost1#[implStatusIdx] = msiI)
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
      GoodMsgOutPred topo MsiSvMsgOutPred.
    Proof.
      red; intros.
      repeat split.
      - red; intros.
        red in H; dest.
        (** TODO: need a lemma [rsEdgeUpFrom dtr oidx = Some _ -> In oidx (indsOf dtr)] *)
    Admitted.

    Definition msiSvAtomicBoundF (inits: list Mii): list Mii :=
      match case inits on miis_dec default nil with
      | [(ec1, Spec.getRq)]:
          [(ce1, Spec.getRs); (c1pRq, msiRqS); (pc1, msiRsS);
             (pc2, msiDownRqS); (c2pRs, msiDownRsS)]
      | [(ec1, Spec.setRq)]:
          [(ce1, Spec.setRs); (c1pRq, msiRqM); (pc1, msiRsM);
             (pc2, msiDownRqM); (c2pRs, msiDownRsM)]
      | [(ec1, Spec.evictRq)]:
          [(ce1, Spec.evictRs); (c1pRq, msiRqI); (pc1, msiRsI)]
      | [(ec2, Spec.getRq)]:
          [(ce2, Spec.getRs); (c2pRq, msiRqS); (pc2, msiRsS);
             (pc1, msiDownRqS); (c1pRs, msiDownRsS)]
      | [(ec2, Spec.setRq)]:
          [(ce2, Spec.setRs); (c2pRq, msiRqM); (pc2, msiRsM);
             (pc1, msiDownRqM); (c1pRs, msiDownRsM)]
      | [(ec2, Spec.evictRq)]:
          [(ce2, Spec.evictRs); (c2pRq, msiRqI); (pc2, msiRsI)]
      end.

    Definition MsiSvLockPred (inits: list Mii) (oidx: IdxT) (orq: ORq Msg): Prop :=
      match case inits on miis_dec default False with
      | [(ec1, Spec.getRq)]:
          match case oidx on eq_nat_dec default True with
          | child1Idx:
              rqiu <+- orq@[upRq];
              (rqiu.(rqi_minds_rss) = [pc1])
          | parentIdx:
              rqid <+- orq@[downRq];
              (rqid.(rqi_minds_rss) = [c2pRs])
          end
      | [(ec1, Spec.setRq)]:
          match case oidx on eq_nat_dec default True with
          | child1Idx:
              rqiu <+- orq@[upRq];
              (rqiu.(rqi_minds_rss) = [pc1])
          | parentIdx:
              rqid <+- orq@[downRq];
              (rqid.(rqi_minds_rss) = [c2pRs])
          end
      | [(ec1, Spec.evictRq)]:
          match case oidx on eq_nat_dec default True with
          | child1Idx:
              rqiu <+- orq@[upRq];
              (rqiu.(rqi_minds_rss) = [pc1])
          | parentIdx: True
          end
      | [(ec2, Spec.getRq)]:
          match case oidx on eq_nat_dec default True with
          | child2Idx:
              rqiu <+- orq@[upRq];
              (rqiu.(rqi_minds_rss) = [pc2])
          | parentIdx:
              rqid <+- orq@[downRq];
              (rqid.(rqi_minds_rss) = [c1pRs])
          end
      | [(ec2, Spec.setRq)]:
          match case oidx on eq_nat_dec default True with
          | child2Idx:
              rqiu <+- orq@[upRq];
              (rqiu.(rqi_minds_rss) = [pc2])
          | parentIdx:
              rqid <+- orq@[downRq];
              (rqid.(rqi_minds_rss) = [c1pRs])
          end
      | [(ec2, Spec.evictRq)]:
          match case oidx on eq_nat_dec default True with
          | child2Idx:
              rqiu <+- orq@[upRq];
              (rqiu.(rqi_minds_rss) = [pc2])
          | parentIdx: True
          end
      end.

    Ltac disc_rule_custom ::=
      repeat
        match goal with
        | [H: AtomicInv _ _ _ _ _ _ _ _ |- _] => red in H; dest
        | [H: AtomicMsgOutsInv _ _ _ _ _ |- _] => red in H; dest
        end.

    Ltac atomic_cont_exfalso_bound :=
      exfalso;
      disc_rule_conds_ex;
      repeat 
        match goal with
        | [H1: SubList [_] ?eouts, H2: SubList (miisOf ?eouts) _ |- _] =>
          let Hs := fresh "H" in
          pose proof (SubList_trans (SubList_map miiOf H1) H2) as Hs;
          clear -Hs; apply SubList_singleton_In in Hs; cbn in Hs
        | [H: context[miis_dec ?miis1 ?miis2] |- _] =>
          destruct (miis_dec miis1 miis2) in H;
          try (Common.dest_in; discriminate)
        end.

    Ltac atomic_init_exfalso_rq :=
      exfalso;
      disc_rule_conds_ex;
      match goal with
      | [H1: SubList [_] _ |- _] =>
        apply SubList_singleton_In in H1; dest_in; discriminate
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
      match goal with
      | [H1: SubList [?rsFrom] _, H2: edgeDownTo _ _ = Some ?rsFrom |- _] =>
        apply SubList_singleton_In in H1; dest_in; discriminate
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
      match goal with
      | [H1: SubList [?rsFrom] _, H2: rsEdgeUpFrom _ _ = Some ?rsFrom |- _] =>
        apply SubList_singleton_In in H1; dest_in
      end.

    Ltac atomic_init_solve_AtomicMsgOutsInv_subList :=
      simpl; unfold miiOf; simpl;
      repeat
        match goal with
        | [H: msg_id ?msg = _ |- context [msg_id ?msg] ] => rewrite H
        | [H1: msg_id ?msg = _, H2: context [msg_id ?msg] |- _] =>
          rewrite H1 in H2
        end;
      repeat
        match goal with
        | [ |- SubList [_] _] => apply SubList_cons; [|apply SubList_nil]
        | [ |- In _ _] => simpl; tauto
        end.

    Ltac atomic_init_solve_AtomicMsgOutsInv :=
      split; [atomic_init_solve_AtomicMsgOutsInv_subList|
              simpl; repeat constructor].

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
      red; simpl; mred.

    Local Ltac atomic_init_solve_AtomicInv :=
      split; [atomic_init_solve_AtomicMsgOutsInv|
              atomic_init_solve_AtomicLocksInv].

    Lemma msiSv_impl_InvTrs_init:
      forall st1,
        Reachable (steps step_m) impl st1 ->
        ImplStateMSI st1 ->
        forall oidx ridx ins outs st2,
          SubList (idsOf ins) (sys_merqs impl) ->
          step_m impl st1 (RlblInt oidx ridx ins outs) st2 ->
          AtomicInv MsiSvMsgOutPred msiSvAtomicBoundF MsiSvLockPred
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

    Lemma msiSv_impl_InvTrs: InvTrs impl ImplStateMSI.
    Proof.
      eapply inv_atomic_InvTrs;
        [red; intros; eapply msiSv_impl_InvTrs_ext_in; eauto
        |red; intros; eapply msiSv_impl_InvTrs_ext_out; eauto
        |].
      instantiate (1:= AtomicInv
                         MsiSvMsgOutPred
                         msiSvAtomicBoundF
                         MsiSvLockPred).

      red; intros.
      destruct H1.
      generalize dependent ist2.
      induction H3; simpl; intros; subst.
      
      - inv_steps.
        apply msiSv_impl_InvTrs_init; auto.
        
      - inv_steps.
        specialize (IHAtomic H1 _ H9); dest.
        inv_step; dest_in.

        (** child1 *)

        + atomic_cont_exfalso_bound.
        + atomic_cont_exfalso_bound.
        + admit.
        + admit.
        + atomic_cont_exfalso_bound.
        + atomic_cont_exfalso_bound.
        + admit.
        + admit.
        + atomic_cont_exfalso_bound.
        + admit.

        (* child2 *)

        + atomic_cont_exfalso_bound.
        + atomic_cont_exfalso_bound.
        + admit.
        + admit.
        + atomic_cont_exfalso_bound.
        + atomic_cont_exfalso_bound.
        + admit.
        + admit.
        + atomic_cont_exfalso_bound.
        + admit.

        (* parent *)

        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        
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

