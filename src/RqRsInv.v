Require Import Peano_dec List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics StepM Invariant Serial.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

(** Useful invariants on top of [RqRsSys] *)

Ltac inv_steps :=
  repeat
    match goal with
    | [H: steps _ _ _ _ _ |- _] => inv H
    end.

Ltac inv_step :=
  repeat
    match goal with
    | [H: step_m _ _ (RlblInt _ _ _ _) _ |- _] => inv H
    | [H: {| bst_oss := _; bst_orqs := _; bst_msgs := _ |} =
          {| bst_oss := _; bst_orqs := _; bst_msgs := _ |} |- _] => inv H
    end.

Ltac red_obj_rule :=
  repeat
    match goal with
    | [H: step_m _ _ (RlblInt _ _ _ _) _ |- _] => inv H
    | [H: {| bst_oss := _; bst_orqs := _; bst_msgs := _ |} =
          {| bst_oss := _; bst_orqs := _; bst_msgs := _ |} |- _] => inv H
    | [H0: In ?obj1 (sys_objs ?sys),
       H1: In ?obj2 (sys_objs ?sys),
       H2: obj_idx ?obj1 = obj_idx ?obj2 |- _] =>
      pose proof (obj_same_id_in_system_same _ _ _ H0 H1 H2);
      subst; clear H0 H2
    | [H0: In ?rule1 (obj_rules ?obj),
       H1: In ?rule2 (obj_rules ?obj),
       H2: rule_idx ?obj1 = rule_idx ?obj2 |- _] =>
      pose proof (rules_same_id_in_object_same _ _ _ H0 H1 H2);
      subst; clear H0 H2
    end.

Ltac good_rqrs_rule_get rule :=
  match goal with
  | [H: GoodRqRsSys _ ?sys,
     Hobj: In ?obj (sys_objs ?sys),
     Hrule: In rule (obj_rules ?obj) |- _] =>
    let Hg := fresh "H" in
    pose proof H as Hg;
    red in Hg; rewrite Forall_forall in Hg;
    specialize (Hg _ Hobj);
    red in Hg; rewrite Forall_forall in Hg;
    specialize (Hg _ Hrule)
  end.

Ltac good_rqrs_rule_cases rule :=
  match goal with
  | [H: GoodRqRsRule _ _ rule |- _] =>
    destruct H as [|[|[|[|]]]]
  end.

Ltac disc_rule_custom := idtac.
Ltac disc_rule_conds :=
  repeat
    (match goal with
     | [H: ImmDownRule _ _ _ |- _] =>
       let cidx := fresh "cidx" in
       let rqFrom := fresh "rqFrom" in
       let rsTo := fresh "rsTo" in
       destruct H as [cidx [rqFrom [rsTo ?]]]; dest
     | [H: ImmUpRule _ _ _ |- _] =>
       let rqFrom := fresh "rqFrom" in
       let rsTo := fresh "rsTo" in
       destruct H as [rqFrom [rsTo ?]]; dest
     | [H: RqFwdRule _ _ _ |- _] =>
       let rqFrom := fresh "rqFrom" in
       let rqTos := fresh "rqTos" in
       red in H;
       destruct H as [rqFrom [rqTos ?]]; dest
     | [H: RqUpUp _ _ _ _ ?rule \/
           RqUpDown _ _ _ _ ?rule \/
           RqDownDown _ _ _ _ ?rule |- _] =>
       destruct H as [|[|]]
     | [H: RqUpUp _ _ _ _ _ |- _] => red in H; dest
     | [H: RqUpDown _ _ _ _ _ |- _] => red in H; dest
     | [H: RqDownDown _ _ _ _ _ |- _] => red in H; dest
     | [H: RsBackRule _ |- _] =>
       let rssFrom := fresh "rssFrom" in
       let rsbTo := fresh "rsbTo" in
       destruct H as [rssFrom [rsbTo ?]]; dest
     | [H: RsDownRqDownRule _ _ _ |- _] =>
       let rsFrom := fresh "rsFrom" in
       let rqTos := fresh "rqTos" in
       destruct H as [rsFrom [rqTos ?]]; dest

     | [H: (FootprintReleasingUp _ _ _ /\ _) \/
           (FootprintReleasingDown _ _ _ /\ _) |- _] => destruct H; dest
     | [H: FootprintReleasingUp _ _ _ |- _] => red in H; dest
     | [H: FootprintReleasingDown _ _ _ |- _] => red in H; dest
     | [H: FootprintingUp _ _ _ |- _] => red in H
     | [H: FootprintingDown _ _ _ |- _] => red in H
     | [H: FootprintedUp _ _ _ |- _] =>
       let rqi := fresh "rqi" in
       destruct H as [rqi ?]; dest
     | [H: FootprintedDown _ _ _ |- _] =>
       let rqi := fresh "rqi" in
       destruct H as [rqi ?]; dest
     | [H: FootprintUpToDown _ _ _ _ |- _] =>
       let rqFrom := fresh "rqFrom" in
       let rsbTo := fresh "rsbTo" in
       let nrssFrom := fresh "nrssFrom" in
       destruct H as [rqFrom [rsbTo [nrssFrom ?]]]; dest
                                
     | [H: MsgsFrom _ _ _ _ |- _] => red in H
     | [H: MsgsTo _ _ |- _] => red in H
     | [H: RqAccepting _ _ _ |- _] => red in H
     | [H: RsReleasing _ |- _] => red in H

     | [H: DownLockFree _ _ _ |- _] => red in H
     | [H: DownLockFreeORq _ |- _] => red in H
     | [H: UpLockFree _ _ _ |- _] => red in H
     | [H: UpLockFreeORq _ |- _] => red in H

     | [H: StateSilent _ |- _] => red in H
     | [H: FootprintSilent _ |- _] => red in H; dest
     | [H: FootprintUpSilent _ |- _] => red in H
     | [H: FootprintDownSilent _ |- _] => red in H
                                             
     | [H1: rule_precond ?rule ->oprec _, H2: rule_precond ?rule _ _ _ |- _] =>
       specialize (H1 _ _ _ H2)
     | [H: (_ /\oprec _) _ _ _ |- _] => destruct H
     | [H1: rule_trs ?rule ?ost ?orq ?ins = _, H2: context[rule_trs ?rule _ _ _] |- _] =>
       specialize (H2 ost orq ins); rewrite H1 in H2; simpl in H2

     | [H: Forall _ (_ :: _) |- _] => inv H
     | [H: Forall _ nil |- _] => clear H

     | [H: idsOf ?ivs = _ :: nil |- _] =>
       destruct ivs; [discriminate|simpl in H; inv H]
     | [H: idsOf ?ivs = nil |- _] => destruct ivs; [|discriminate]
     | [H: nil = nil |- _] => clear H
     end;
     try disc_rule_custom;
     simpl in *; subst).

Ltac solve_rule_conds :=
  repeat red;
  repeat
    (repeat
       match goal with
       | [ |- exists _, _] => eexists
       | [ |- _ /\ _] => split
       end;
     try reflexivity; try eassumption).

Section FootprintInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hitr: GoodRqRsSys dtr sys).

  Definition FootprintUpOkEx (oidx: IdxT) (rqi: RqInfo Msg) :=
    exists rqTo rsFrom rsbTo,
      rqi.(rqi_minds_rss) = [rsFrom] /\
      rqi.(rqi_midx_rsb) = rsbTo /\
      FootprintUpOk dtr oidx rqTo rsFrom rsbTo.

  Definition FootprintDownOkEx (rqi: RqInfo Msg) :=
    exists rqTos rssFrom rsbTo,
      rqi.(rqi_minds_rss) = rssFrom /\
      rqi.(rqi_midx_rsb) = rsbTo /\
      ((exists rqFrom, FootprintUpDownOk dtr rqFrom rqTos rssFrom rsbTo) \/
       FootprintDownDownOk dtr rqTos rssFrom).

  Definition FootprintsOkORqs (orqs: ORqs Msg) :=
    forall oidx,
      orqs@[oidx] >>=[True]
          (fun orq =>
             (orq@[upRq] >>=[True] (fun rqiu => FootprintUpOkEx oidx rqiu)) /\
             (orq@[downRq] >>=[True] (fun rqid => FootprintDownOkEx rqid))).

  Lemma footprints_ok_orqs_add:
    forall orqs,
      FootprintsOkORqs orqs ->
      forall oidx norq,
        norq@[upRq] >>=[True] (fun rqiu => FootprintUpOkEx oidx rqiu) ->
        norq@[downRq] >>=[True] (fun rqid => FootprintDownOkEx rqid) ->
        FootprintsOkORqs (orqs +[oidx <- norq]).
  Proof.
    unfold FootprintsOkORqs; intros.
    mred; simpl; intros; auto.
  Qed.
  
  Definition FootprintsOk (st: MState oifc) :=
    FootprintsOkORqs st.(bst_orqs).

  Ltac disc_rule_custom ::=
    repeat
      match goal with
      | [H1: FootprintsOkORqs ?orqs, H2: ?orqs @[?oidx] = _ |- _] =>
        let Hf := fresh "H" in
        pose proof (H1 oidx) as Hf;
        rewrite H2 in Hf; simpl in Hf; dest;
        clear H2
      end.

  Lemma footprints_ok_init:
    InvInit sys FootprintsOk.
  Proof.
    intros; do 3 red.
    intros; simpl; auto.
  Qed.
  
  Lemma footprints_ok_step:
    InvStep sys step_m FootprintsOk.
  Proof.
    red; intros.
    red in H0; red.
    inv H1; try assumption.

    simpl in *.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      mred.
      apply footprints_ok_orqs_add; auto; try (mred; fail).
    - disc_rule_conds.
      mred.
      apply footprints_ok_orqs_add; auto; try (mred; fail).
      rewrite <-H6; assumption.
    - disc_rule_conds.
      + apply footprints_ok_orqs_add; auto.
        * rewrite H15; simpl.
          do 3 eexists; repeat split; eassumption.
        * rewrite <-H23; assumption.
      + apply footprints_ok_orqs_add; auto.
        * rewrite <-H23; assumption.
        * rewrite H13; simpl.
          do 3 eexists; repeat split.
          left; eexists; eassumption.
      + apply footprints_ok_orqs_add; auto.
        * rewrite <-H22; assumption.
        * rewrite H13; simpl.
          do 3 eexists; repeat split.
          right; eassumption.
    - disc_rule_conds.
      + apply footprints_ok_orqs_add; auto.
        * rewrite H17; simpl; auto.
        * rewrite <-H6; assumption.
      + apply footprints_ok_orqs_add; auto.
        * rewrite <-H6; assumption.
        * rewrite H17; simpl; auto.
    - disc_rule_conds.
      apply footprints_ok_orqs_add; auto.
      + rewrite H22; simpl; auto.
      + rewrite H15; simpl.
        do 3 eexists; repeat split.
        left; eexists; rewrite <-H21 in H6; eassumption.
  Qed.

  Lemma footprints_ok:
    InvReachable sys step_m FootprintsOk.
  Proof.
    eapply inv_reachable.
    - apply footprints_ok_init.
    - apply footprints_ok_step.
  Qed.
  
End FootprintInv.

Section MessageInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hitr: GoodRqRsSys dtr sys).

  Definition RqUpMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    exists cidx rqUp,
      msgs = [rqUp] /\
      msg_type (valOf rqUp) = MRq /\
      parentOf dtr cidx = Some oidx /\
      rqEdgeUpFrom dtr cidx = Some (idOf rqUp).

  Definition RqDownMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    exists rqDown, msgs = [rqDown] /\
                   msg_type (valOf rqDown) = MRq /\
                   edgeDownTo dtr oidx = Some (idOf rqDown).

  Definition RsUpMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    Forall (fun msg => msg_type (valOf msg) = MRs) msgs /\
    SubList (idsOf msgs) (rsEdgesUpTo dtr oidx).

  Definition RsDownMsgs (oidx: IdxT) (msgs: list (Id Msg)): Prop :=
    exists rsDown, msgs = [rsDown] /\
                   msg_type (valOf rsDown) = MRs /\
                   edgeDownTo dtr oidx = Some (idOf rsDown).

  Ltac disc_rule_custom ::= idtac.
  
  Lemma messages_in_cases:
    forall st1 oidx ridx rins routs st2,
      Reachable (steps step_m) sys st1 ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      RqUpMsgs oidx rins \/
      RqDownMsgs oidx rins \/
      RsUpMsgs oidx rins \/
      RsDownMsgs oidx rins.
  Proof.
    intros.

    (* Register some necessary invariants to prove this invariant. *)
    pose proof (footprints_ok Hitr H).
    
    inv H0.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - left.
      disc_rule_conds.
      solve_rule_conds.

    - right; left.
      disc_rule_conds.
      solve_rule_conds.

    - disc_rule_conds.
      + left; solve_rule_conds.
      + left; solve_rule_conds.
      + right; left; solve_rule_conds.

    - admit.
    - admit.

  Admitted.
    
End MessageInv.

(** NOTE: With [LockInv] below we may need some invariants 
 * for [Atomic] histories, such as: if [Atomic hst] and [st1 -(hst)-> st2]
 * then [hst.eouts ⊆ st2.msgs].
 *)

(* Want: between two continuous histories H1 and H2, after H1, related locks are
 * never released until H2; it can be proven by [LockInv] below and
 * [atomic_messages_spec_in] in SerialFacts.v.
 *)
Section LockInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrr: GoodRqRsSys dtr sys).

  Section OnMState.
    Variables (orqs: ORqs Msg)
              (msgs: MessagePool Msg).

    Definition OUpLocked (oidx: IdxT) :=
      orqs@[oidx] >>=[False] (fun orq => UpLockedORq orq).

    Definition ODownLocked (oidx: IdxT) :=
      orqs@[oidx] >>=[False] (fun orq => DownLockedORq orq).

    Definition OUpLockFree (oidx: IdxT) :=
      orqs@[oidx] >>=[True] (fun orq => UpLockFreeORq orq).

    Definition ODownLockFree (oidx: IdxT) :=
      orqs@[oidx] >>=[True] (fun orq => DownLockFreeORq orq).

    Definition rqsQ (midx: IdxT) :=
      filter (fun msg => msg.(msg_type) ==n MRq) (findQ midx msgs).

    Definition rssQ (midx: IdxT) :=
      filter (fun msg => msg.(msg_type) ==n MRs) (findQ midx msgs).

    Definition UpLockFreeInv (oidx: IdxT) :=
      (rqEdgeUpFrom dtr oidx) >>=[True] (fun rqUp => findQ rqUp msgs = nil) /\
      (edgeDownTo dtr oidx) >>=[True] (fun down => rssQ down = nil) /\
      (parentOf dtr oidx) >>=[True] (fun pidx => OUpLockFree pidx).
    
    Definition UpLockedInv (oidx: IdxT) :=
      exists rqUp down pidx,
        rqEdgeUpFrom dtr oidx = Some rqUp /\
        edgeDownTo dtr oidx = Some down /\
        parentOf dtr oidx = Some pidx /\
        xor3 (findQ rqUp msgs <> nil)
             (rssQ down <> nil)
             (OUpLocked pidx).

    Definition DownLockFreeInv (oidx: IdxT) :=
      forall cidx,
        parentOf dtr cidx = Some oidx ->
        ((edgeDownTo dtr cidx) >>=[True] (fun down => rqsQ down = nil) /\
         (rsEdgeUpFrom dtr cidx) >>=[True] (fun rsUp => findQ rsUp msgs = nil)).
    
    Definition DownLockedInv (oidx: IdxT) (rqi: RqInfo Msg) :=
      Forall (fun rsUp =>
                exists down cidx,
                  edgeDownTo dtr cidx = Some down /\
                  rsEdgeUpFrom dtr cidx = Some rsUp /\
                  parentOf dtr cidx = Some oidx /\
                  xor (rqsQ down <> nil) (findQ rsUp msgs <> nil))
             rqi.(rqi_minds_rss).

    Definition UpLockInvORq (oidx: IdxT) (orq: ORq Msg) :=
      match orq@[upRq] with
      | Some _ => UpLockedInv oidx
      | None => UpLockFreeInv oidx
      end.

    Definition DownLockInvORq (oidx: IdxT) (orq: ORq Msg) :=
      match orq@[downRq] with
      | Some downRqi => DownLockedInv oidx downRqi
      | None => DownLockFreeInv oidx
      end.

    Definition LockInvMO :=
      forall oidx,
        In oidx (map (@obj_idx _) sys.(sys_objs)) ->
        let orq := orqs@[oidx] >>=[[]] (fun orq => orq) in
        UpLockInvORq oidx orq /\ DownLockInvORq oidx orq.

  End OnMState.
  
  Definition LockInv (st: MState oifc) :=
    LockInvMO st.(bst_orqs) st.(bst_msgs).

  Lemma lockInv_init:
    sys.(sys_orqs_inits) = [] ->
    InvInit sys LockInv.
  Proof.
    intros; do 3 red; cbn.
    intros; cbn; rewrite H; cbn.
    split.
    - red; cbn; repeat split.
      + destruct (rqEdgeUpFrom dtr oidx); simpl; auto.
      + destruct (edgeDownTo dtr oidx); simpl; auto.
      + destruct (parentOf dtr oidx); simpl; auto.
    - red; cbn; repeat split.
      + destruct (edgeDownTo dtr cidx); simpl; auto.
      + destruct (rsEdgeUpFrom dtr cidx); simpl; auto.
  Qed.

  Lemma lockInv_step_ext_in:
    forall oss orqs msgs eins,
      LockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      eins <> nil ->
      ValidMsgsExtIn sys eins ->
      LockInv {| bst_oss := oss;
                 bst_orqs := orqs;
                 bst_msgs := enqMsgs eins msgs |}.
  Proof.
  Admitted.

  Lemma lockInv_step_ext_out:
    forall oss orqs msgs eouts,
      LockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      eouts <> nil ->
      Forall (FirstMPI msgs) eouts ->
      ValidMsgsExtOut sys eouts ->
      LockInv {| bst_oss := oss;
                 bst_orqs := orqs;
                 bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
  Admitted.
  
  Lemma lockInv_step:
    InvStep sys step_m LockInv.
  Proof.
    red; intros.
    
    inv H1; auto.
    - apply lockInv_step_ext_in; auto.
    - apply lockInv_step_ext_out; auto.
    - 
  Admitted.

End LockInv.

Section RqUpInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: GoodRqRsSys dtr sys)
             (Hrud: RqUpRsUpOkSys dtr sys).
  
  (* Lemma rqUp_reducible: *)
  (*   forall oidx1 ridx1 rins1 routs1 rule1 obj1 *)
  (*          (Hobj1: In obj1 sys.(sys_objs)) (Hoidx1: obj1.(obj_idx) = oidx1) *)
  (*          (Hrule1: In rule1 obj1.(obj_rules)) *)
  (*          (Hridx1: rule1.(rule_idx) = ridx1) *)
  (*          oidx2 ridx2 rins2 routs2 rule2 obj2 *)
  (*          (Hobj2: In obj2 sys.(sys_objs)) (Hoidx2: obj2.(obj_idx) = oidx2) *)
  (*          (Hrule2: In rule2 obj2.(obj_rules)) *)
  (*          (Hridx2: rule2.(rule_idx) = ridx2), *)
  (*     RqToUpRule dtr oidx1 rule1 -> *)
  (*     DisjList routs1 rins2 -> *)
  (*     Reducible sys [RlblInt oidx2 ridx2 rins2 routs2; *)
  (*                      RlblInt oidx1 ridx1 rins1 routs1] *)
  (*               [RlblInt oidx1 ridx1 rins1 routs1; *)
  (*                  RlblInt oidx2 ridx2 rins2 routs2]. *)
  (* Proof. *)
  (* Admitted. *)

End RqUpInv.

Inductive TrsType := RqUp | RqDown | RsUp | RsDown.
(* Object index -> TrsTypes (ordered, head is the oldest one) *)
Definition TrsState := M.t (list TrsType).

Definition addTrsState (oidx: IdxT) (tr: TrsType) (ts: TrsState): TrsState :=
  match ts@[oidx] with
  | Some tts => ts +[oidx <- tr :: tts]
  | None => ts +[oidx <- [tr]]
  end.

Definition rssOfL (lbl: MLabel) :=
  match lbl with
  | RlblInt oidx _ _ mouts =>
    match mouts with
    | nil => Some oidx (* Requests are never ignored. *)
    | (midx, mout) :: _ =>
      if eq_nat_dec (msg_type mout) MRs
      then Some oidx else None
    end
  | _ => None
  end.

Fixpoint rssOf (hst: MHistory): list IdxT :=
  match hst with
  | nil => nil
  | lbl :: hst' => (rssOfL lbl) ::> (rssOf hst')
  end.

(* Definition rqsOfL (lbl: MLabel) := *)
(*   match lbl with *)
(*   | RlblInt oidx _ _ mouts => *)
(*     match mouts with *)
(*     | nil => None (* Requests are never ignored. *) *)
(*     | (midx, mout) :: _ => *)
(*       if eq_nat_dec (msg_type mout) MRq *)
(*       then Some oidx else None *)
(*     end *)
(*   | _ => None *)
(*   end. *)

Definition trsTypeOf (dtr: DTree) (idm: Id Msg):
  option IdxT * option IdxT * TrsType :=
  (findEdge dtr (fst idm))
    >>=[(None, None, RqUp)]
    (fun e =>
       (e.(edge_from),
        e.(edge_to),
        match fst (fst e.(edge_chn)) with
        | CUp => if eq_nat_dec (msg_type (snd idm)) MRq then RqUp else RsUp
        | CDown => if eq_nat_dec (msg_type (snd idm)) MRq then RqDown else RsDown
        end)).

Section AtomicInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hitr: GoodRqRsSys dtr sys).

  Definition subtreeInds (sroot: option IdxT): list IdxT :=
    sroot >>=[nil] (fun sroot => dg_vs (topoOfT (subtree dtr sroot))).

  Definition rsUpCover (idm: Id Msg): list IdxT :=
    let from := fst (fst (trsTypeOf dtr idm)) in
    let to := snd (fst (trsTypeOf dtr idm)) in
    match snd (trsTypeOf dtr idm) with
    | RsUp => subtreeInds from
    | _ => nil
    end.

  Fixpoint rsUpCovers (eouts: list (Id Msg)): list IdxT :=
    match eouts with
    | nil => nil
    | idm :: eouts' => rsUpCover idm ++ rsUpCovers eouts'
    end.

  Definition rsDownCover (idm: Id Msg): list IdxT :=
    let from := fst (fst (trsTypeOf dtr idm)) in
    let to := snd (fst (trsTypeOf dtr idm)) in
    match snd (trsTypeOf dtr idm) with
    | RsDown => subtreeInds to
    | _ => nil
    end.

  Fixpoint rsDownCovers (eouts: list (Id Msg)): list IdxT :=
    match eouts with
    | nil => nil
    | idm :: eouts' => rsDownCover idm ++ rsDownCovers eouts'
    end.

  Definition AtomicInv (inits eouts: list (Id Msg)) (hst: MHistory) :=
    NoDup (rssOf hst) /\
    SubList (rssOf hst) (rsUpCovers eouts) /\
    DisjList (rssOf hst) (rsDownCovers eouts).

  Lemma atomic_inv:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        steps step_m sys s1 hst s2 ->
        AtomicInv inits eouts hst.
  Proof.
  Admitted.
  
End AtomicInv.

Close Scope list.
Close Scope fmap.

