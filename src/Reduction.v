Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM SemFacts.
Require Import Topology Serial.

Require Import Permutation.

Set Implicit Arguments.

Ltac dest_step_m :=
  repeat match goal with
         | [H: steps step_m _ _ _ _ |- _] => inv H
         | [H: step_m _ _ _ _ |- _] => inv H
         | [H: {| bst_oss := _ |} = {| bst_oss := _ |} |- _] => inv H
         end; simpl in *.

Definition NonSilentHistory (hst: MHistory) :=
  Forall (fun lbl => lbl <> emptyRLabel _) hst.

Definition Internal (lbl: MLabel) :=
  match lbl with
  | RlblInt _ _ _ => True
  | _ => False
  end.

Definition InternalHistory (hst: MHistory) :=
  Forall (fun tlbl => Internal tlbl) hst.

Definition Reduced (sys: System) (hfr hto: MHistory) :=
  forall st1 st2,
    steps step_m sys st1 hfr st2 ->
    steps step_m sys st1 hto st2 /\
    BEquivalent sys hfr hto.

(*! General Facts *)

Lemma internal_history_behavior_nil:
  forall sys hst,
    InternalHistory hst -> behaviorOf sys hst = nil.
Proof.
  induction hst; simpl; intros; auto.
  inv H; rewrite IHhst by assumption.
  destruct a; auto; elim H2.
Qed.

Lemma reduced_app_1:
  forall sys hfr hto,
    Reduced sys hfr hto ->
    forall hst,
      Reduced sys (hst ++ hfr) (hst ++ hto).
Proof.
  unfold Reduced; intros.
  eapply steps_split in H0; [|reflexivity]; dest.
  specialize (H _ _ H0); dest.
  split.
  - eapply steps_append; eauto.
  - red; do 2 rewrite behaviorOf_app.
    rewrite H2; reflexivity.
Qed.

Lemma reduced_app_2:
  forall sys hfr hto,
    Reduced sys hfr hto ->
    forall hst,
      Reduced sys (hfr ++ hst) (hto ++ hst).
Proof.
  unfold Reduced; intros.
  eapply steps_split in H0; [|reflexivity]; dest.
  specialize (H _ _ H1); dest.
  split.
  - eapply steps_append; eauto.
  - red; do 2 rewrite behaviorOf_app.
    rewrite H2; reflexivity.
Qed.

Lemma reduced_serializable:
  forall sys st1 hfr st2,
    steps step_m sys st1 hfr st2 ->
    Serializable sys hfr ->
    forall hto,
      Reduced sys hfr hto ->
      Serializable sys hto.
Proof.
  unfold Serializable, Reduced; intros.
  destruct H0 as [shfr [stfr [? ?]]].
  exists shfr, stfr.
  split; auto.
  specialize (H1 _ _ H); dest.
  congruence.
Qed.

(*! Reducibility of incoming and outgoing labels *)

Lemma msg_ins_commutes:
  forall sys eins lbl,
    Internal lbl ->
    Reduced sys [RlblIns eins; lbl] [lbl; RlblIns eins].
Proof.
  unfold Reduced; intros.
  split.
  - destruct lbl as [|hdl mins mouts|]; [elim H| |elim H].
    dest_step_m.
    + econstructor.
      * econstructor.
        { econstructor. } 
        { econstructor; eauto. }
      * econstructor.
    + econstructor.
      * econstructor.
        { econstructor. }
        { econstructor; eauto. }
      * econstructor; try reflexivity; try eassumption.
        { eapply FirstMPI_Forall_enqMsgs; eauto. }
        { f_equal.
          rewrite enqMsgs_enqMsgs_comm.
          { rewrite enqMsgs_deqMsgs_FirstMPI_comm; auto.
            destruct H10; auto.
          }
          { destruct H2, H17.
            eapply DisjList_SubList; eauto.
            eapply DisjList_comm, DisjList_SubList; eauto.
            apply DisjList_app_4.
            { apply mindsOf_merqsOf_DisjList. }
            { apply DisjList_comm, merqsOf_merssOf_DisjList. }
          }
        }
  - hnf; cbn.
    destruct lbl; [elim H|auto|elim H].
Qed.

Lemma msg_in_reduced:
  forall sys eins hst2,
    InternalHistory hst2 ->
    Reduced sys (RlblIns eins :: hst2) (hst2 ++ [RlblIns eins]).
Proof.
  unfold Reduced; induction hst2 as [|lbl ?]; simpl; intros;
    [split; [assumption|reflexivity]|].
  inv H.
  split.
  - change (RlblIns eins :: lbl :: hst2) with ([RlblIns eins; lbl] ++ hst2) in H0.
    eapply steps_split in H0; [|reflexivity].
    destruct H0 as [sti [? ?]].
    eapply msg_ins_commutes in H0; [|assumption]; dest.
    pose proof (steps_append H H0); inv H2.
    specialize (IHhst2 H4 _ _ H8); dest.
    econstructor; eauto.
  - red; cbn.
    rewrite behaviorOf_app.
    rewrite internal_history_behavior_nil by assumption.
    destruct lbl; auto; elim H3.
Qed.

Lemma msg_outs_commutes:
  forall sys eouts lbl,
    Internal lbl ->
    Reduced sys [lbl; RlblOuts eouts] [RlblOuts eouts; lbl].
Proof.
  unfold Reduced; intros.
  split.
  - destruct lbl as [|hdl mins mouts|]; [elim H| |elim H].
    dest_step_m.
    + econstructor.
      * econstructor.
        { econstructor. }
        { econstructor; eauto. }
      * econstructor; eauto.
    + econstructor.
      * econstructor.
        { econstructor. }
        { econstructor; try reflexivity; try eassumption.
          assert (DisjList (idsOf mins) (idsOf eouts)).
          { destruct H3, H12.
            eapply DisjList_SubList; eauto.
            eapply DisjList_comm, DisjList_SubList; eauto.
            apply DisjList_comm, mindsOf_merssOf_DisjList.
          }
          eapply FirstMPI_Forall_deqMsgs; eauto.
        }
      * assert (DisjList (idsOf eouts) (idsOf mins)).
        { destruct H3, H12.
          eapply DisjList_SubList; eauto.
          eapply DisjList_comm, DisjList_SubList; eauto.
          apply mindsOf_merssOf_DisjList.
        }
        econstructor; try reflexivity; try eassumption.
        { eapply FirstMPI_Forall_enqMsgs.
          rewrite <-FirstMPI_Forall_deqMsgs; eauto.
        }
        { f_equal; rewrite <-enqMsgs_deqMsgs_FirstMPI_comm.
          { f_equal; eapply deqMsgs_deqMsgs_comm.
            apply DisjList_comm; auto.
          }
          { destruct H3; auto. }
          { rewrite <-FirstMPI_Forall_deqMsgs; eauto. }
        }
  - hnf; cbn.
    destruct lbl; [elim H|auto|elim H].
Qed.

Lemma msg_outs_reduced:
  forall sys eouts hst2,
    InternalHistory hst2 ->
    Reduced sys (hst2 ++ [RlblOuts eouts]) (RlblOuts eouts :: hst2).
Proof.
  unfold Reduced; induction hst2 as [|lbl ?]; simpl; intros; 
    [split; [assumption|reflexivity]|].
  inv H0; inv H.
  split.
  - specialize (IHhst2 H3 _ _ H4); dest.
    assert (steps step_m sys st1 (lbl :: RlblOuts eouts :: hst2) st2)
      by (econstructor; eauto).
    change (lbl :: RlblOuts eouts :: hst2) with
        ([lbl; RlblOuts eouts] ++ hst2) in H1.
    eapply steps_split in H1; [|reflexivity].
    destruct H1 as [sti [? ?]].
    change (RlblOuts eouts :: lbl :: hst2) with
        ([RlblOuts eouts; lbl] ++ hst2).
    eapply steps_append; eauto.
    eapply msg_outs_commutes; eauto.
  - red; cbn.
    rewrite behaviorOf_app.
    rewrite internal_history_behavior_nil by assumption.
    destruct lbl; auto; elim H2.
Qed.

(*! Reducibility of internal state transitions *)

Lemma msg_int_commutes_1:
  forall sys rule1 ins1 outs1 rule2 ins2 outs2,
    rule_oidx rule1 <> rule_oidx rule2 ->
    DisjList (idsOf ins1) (idsOf ins2) ->
    DisjList (idsOf outs1) (idsOf ins2) ->
    DisjList (idsOf outs1) (idsOf outs2) ->
    Reduced sys [RlblInt (Some rule2) ins2 outs2; RlblInt (Some rule1) ins1 outs1]
            [RlblInt (Some rule1) ins1 outs1; RlblInt (Some rule2) ins2 outs2].
Proof.
  unfold Reduced; intros.
  split; [|reflexivity].
  dest_step_m.
  econstructor.
  - econstructor.
    + econstructor.
    + econstructor; try reflexivity; try eassumption.
      * mred.
      * mred.
      * eapply FirstMPI_Forall_enqMsgs_inv in H22;
          [|apply DisjList_comm; auto].
        eapply FirstMPI_Forall_deqMsgs; eauto.
        apply DisjList_comm; auto.
  - econstructor; try reflexivity; try eassumption.
    + mred.
    + mred.
    + apply FirstMPI_Forall_enqMsgs.
      apply FirstMPI_Forall_deqMsgs; auto.
    + f_equal.
      * meq.
      * meq.
      * rewrite <-enqMsgs_deqMsgs_comm with (minds1:= idsOf ins2)
          by (apply DisjList_comm; assumption).
        rewrite deqMsgs_deqMsgs_comm by (apply DisjList_comm; assumption).
        rewrite enqMsgs_enqMsgs_comm with (msgs1:= outs2)
          by (apply DisjList_comm; assumption).
        rewrite enqMsgs_deqMsgs_FirstMPI_comm with (msgs2:= outs2).
        { reflexivity. }
        { destruct H13; auto. }
        { apply FirstMPI_Forall_deqMsgs; auto. }
Qed.

Lemma msg_int_commutes_2:
  forall sys rule1 ins1 outs1 rule2 ins2 outs2 rule3 ins3 outs3,
    rule_oidx rule1 <> rule_oidx rule2 ->
    DisjList (idsOf ins1) (idsOf ins2) ->
    DisjList (idsOf outs1) (idsOf outs2) ->
    DisjList (idsOf outs2) (idsOf ins3) ->
    (forall midx,
        In midx (idsOf outs1) ->
        In midx (idsOf ins2) ->
        In midx (idsOf ins3)) ->
    Reduced sys [RlblInt (Some rule3) ins3 outs3;
                   RlblInt (Some rule2) ins2 outs2;
                   RlblInt (Some rule1) ins1 outs1]
            [RlblInt (Some rule3) ins3 outs3;
               RlblInt (Some rule1) ins1 outs1;
               RlblInt (Some rule2) ins2 outs2].
Proof.
  unfold Reduced; intros.
  split; [|reflexivity].
  dest_step_m.
  econstructor; [econstructor; [econstructor; [econstructor|]|]|].

  - econstructor; try reflexivity; try eassumption; try (mred; fail).
    apply FirstMPI_Forall_enqMsgs_inv in H35; [|apply DisjList_comm; assumption].
    eapply FirstMPI_Forall_deqMsgs; [apply DisjList_comm; eassumption|].
    remember (deqMsgs (idsOf ins1) msgs) as imsgs; clear H14 Heqimsgs msgs.
    eapply FirstMPI_Forall_enqMsgs_order; eauto.
    + destruct H22; auto.
    + destruct H25; auto.
  - econstructor; try reflexivity; try eassumption; try (mred; fail).
    apply FirstMPI_Forall_enqMsgs.
    apply FirstMPI_Forall_deqMsgs; auto.
  - assert (enqMsgs outs2 (deqMsgs (idsOf ins2) (enqMsgs outs1 (deqMsgs (idsOf ins1) msgs))) =
            enqMsgs outs1 (deqMsgs (idsOf ins1) (enqMsgs outs2 (deqMsgs (idsOf ins2) msgs)))).
    {
      rewrite <-enqMsgs_deqMsgs_FirstMPI_comm with (msgs1:= ins1);
        [|destruct H15; auto
         |apply FirstMPI_Forall_deqMsgs; auto].
      rewrite deqMsgs_deqMsgs_comm by assumption.
      rewrite enqMsgs_enqMsgs_comm by assumption.

      rewrite enqMsgs_deqMsgs_comm_order with (msgs1:= outs1) (minds2:= idsOf ins2) (msgs3:= ins3).
      { reflexivity. }
      { destruct H22; auto. }
      { destruct H25; auto. }
      { assumption. }
      { eapply FirstMPI_Forall_enqMsgs_inv; eauto.
        apply DisjList_comm; assumption.
      }
    }

    econstructor; try reflexivity; try eassumption.
    + rewrite M.add_comm; assumption.
    + rewrite M.add_comm; assumption.
    + rewrite <-H4; assumption.
    + f_equal; try (meq; fail).
      rewrite H4; reflexivity.
Qed.

(*! Reducibility of request-forwardings and responses-back *)

Definition liftSingletonTrs (hst: MHistory) :=
  map (fun lbl => [lbl]) hst.

(* For a given list of "list of transactions," we want to preserve an order
 * for each "list of transactions."
 *)
Inductive OPermutation {A}: list (list (list A)) -> list A -> Prop :=
| OPermNil: OPermutation nil nil
| OPermCons:
    forall strss1 trs trss strss2 hst,
      OPermutation (strss1 ++ trss :: strss2) hst ->
      OPermutation (strss1 ++ (trs :: trss) :: strss2) (trs ++ hst).

Lemma downward_request_forwardings_reduced:
  forall sys rqfr rq rqfs rqfsp trss,

    (* A subtransaction for each downward request can happen 
     * in an arbitrary order. *)
    Permutation rqfs rqfsp ->

    (* [trss] are the subtransactions of downward requests,
     * where each of them is already [Atomic]. *)
    Forall (fun rqtrs => exists outs, Atomic (fst rqtrs) (snd rqtrs) outs)
           (combine rqfsp trss) ->

    (* Other irrelevant transaction segments and the subtransactions
     * are interleaved in an arbitrary manner. *)
    forall trsoths others,
      OPermutation [trss; liftSingletonTrs others] trsoths ->

      (* This reduction claims that all the irrelevant segments can be
       * left-pushed before the original request-forwarding label. *)
      Reduced sys (trsoths ++ [RlblInt (Some rqfr) [rq] rqfs])
              (List.concat trss ++ [RlblInt (Some rqfr) [rq] rqfs] ++ others).
Proof.
  (* induction on [OPermutation]? *)
Admitted.

Lemma upward_request_forwarding_reduced:
  forall sys rqfr rq rqf trs outs,

    (* The transaction for the upward request is already [Atomic]. *)
    Atomic rqf trs outs ->

    (* This reduction claims that intermediate irrelevant subhistory [others]
     * can be left-pushed before the original request-forwarding label. *)
    forall others,
      Reduced sys (trs ++ others ++ [RlblInt (Some rqfr) [rq] [rqf]])
              (trs ++ [RlblInt (Some rqfr) [rq] [rqf]] ++ others).
Proof.
  (* induction on [others]? *)
Admitted.

Lemma upward_responses_back_reduced:
  forall sys rsbr rss rssp trss rsb,

    (* A subtransaction for each upward response can happen 
     * in an arbitrary order. *)
    Permutation rss rssp ->

    (* [trss] are the subtransactions of upward responses,
     * where each of them is already [Atomic]. *)
    Forall (fun rstrs =>
              exists rq, Atomic rq (snd rstrs) (enqMPI (fst rstrs) (emptyMP _)))
           (combine rssp trss) ->

    (* Other irrelevant transaction segments and the subtransactions
     * are interleaved in an arbitrary manner. *)
    forall trsoths others,
      OPermutation [trss; liftSingletonTrs others] trsoths ->

      (* This reduction claims that all the irrelevant segments can be
       * right-pushed after the response-back label. *)
      Reduced sys (RlblInt (Some rsbr) rss [rsb] :: trsoths)
              (others ++ RlblInt (Some rsbr) rss [rsb] :: List.concat trss).
Proof.
Admitted.

Lemma downward_response_back_reduced:
  forall sys rq rsbr rs trs rsb,

    (* The transaction for the downward response is already [Atomic]. *)
    Atomic rq trs (enqMPI rs (emptyMP _)) ->

    (* This reduction claims that intermediate irrelevant subhistory [others] *)
    (* can be right-pushed after the response-back label. *)
    forall others,
      Reduced sys (RlblInt (Some rsbr) [rs] [rsb] :: others ++ trs)
              (others ++ RlblInt (Some rsbr) [rs] [rsb] :: trs).
Proof.
  (* induction on [others]? *)
Admitted.

