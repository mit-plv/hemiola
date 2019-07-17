Require Import Common Omega List ListSupport HVector FMap.
Require Import Syntax Topology Semantics SemFacts StepM Invariant Serial.

Require Export RqRsTopo RqRsFacts.
Require Export RqRsInvMsg RqRsInvLock RqRsInvSep RqRsInvAtomic.
Require Export RqRsMsgPred.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Definition rootDmc (ridx: IdxT) :=
  {| dmc_me := ridx;
     dmc_ups := nil;
     dmc_downs := nil |}.

Definition StateM oifc :=
  (OState oifc * ORq Msg * list (Id Msg))%type.

Definition StateMTrs oifc :=
  StateM oifc -> StateM oifc.

Definition StateMBind {oifc A}
           (f: StateM oifc -> option A)
           (cont: A -> StateM oifc -> StateM oifc): StateMTrs oifc :=
  fun st => (f st) >>=[st] (fun a => cont a st).

Definition TrsMTrs {oifc} (mtrs: StateMTrs oifc): OTrs oifc :=
  fun ost orq mins => mtrs (ost, orq, mins).

Definition getFirstMsg {oifc} (st: StateM oifc): option Msg :=
  (hd_error (snd st)) >>= (fun idm => Some (valOf idm)).

Definition FirstNatMsg {oifc}: OPrec oifc :=
  fun ost orq mins =>
    (hd_error mins)
      >>=[False]
      (fun idm =>
         match msg_value (valOf idm) with
         | VNat _ => True
         | _ => False
         end).

Definition getFirstNatMsg {oifc} (st: StateM oifc): option nat :=
  (hd_error (snd st))
    >>= (fun idm =>
           match msg_value (valOf idm) with
           | VNat n => Some n
           | _ => None
           end).

Definition UpLockMsgId {oifc} (mty: bool) (mid: IdxT): OPrec oifc :=
  fun ost orq mins =>
    (orq@[upRq])
      >>=[False]
      (fun rqiu =>
         rqiu.(rqi_msg).(msg_type) = mty /\
         rqiu.(rqi_msg).(msg_id) = mid).

Definition getUpLockMsgId {oifc} (st: StateM oifc): option (bool * IdxT) :=
  ((snd (fst st))@[upRq])
    >>= (fun rqiu => Some (rqiu.(rqi_msg).(msg_type),
                           rqiu.(rqi_msg).(msg_id))).

Definition UpLockMsg {oifc}: OPrec oifc :=
  fun ost orq mins =>
    match orq@[upRq] with
    | Some _ => True
    | _ => False
    end.

Definition getUpLockMsg {oifc} (st: StateM oifc): option Msg :=
  ((snd (fst st))@[upRq])
    >>= (fun rqiu => Some (rqi_msg rqiu)).

Definition UpLockNatMsg {oifc}: OPrec oifc :=
  fun ost orq mins =>
    (orq@[upRq])
      >>=[False]
      (fun rqiu =>
         match msg_value (rqi_msg rqiu) with
         | VNat _ => True
         | _ => False
         end).

Definition getUpLockNatMsg {oifc} (st: StateM oifc): option nat :=
  ((snd (fst st))@[upRq])
    >>= (fun rqiu =>
           match msg_value (rqi_msg rqiu) with
           | VNat n => Some n
           | _ => None
           end).

Definition UpLocked {oifc}: OPrec oifc :=
  fun ost orq mins => orq@[upRq] <> None.

Definition getUpLockIdxBack {oifc} (st: StateM oifc): option IdxT :=
  ((snd (fst st))@[upRq])
    >>= (fun rqiu => Some rqiu.(rqi_midx_rsb)).

Definition DownLockMsgId {oifc} (mty: bool) (mid: IdxT): OPrec oifc :=
  fun ost orq mins =>
    (orq@[downRq])
      >>=[False]
      (fun rqiu =>
         rqiu.(rqi_msg).(msg_type) = mty /\
         rqiu.(rqi_msg).(msg_id) = mid).

Definition getDownLockMsgId {oifc} (st: StateM oifc): option (bool * IdxT) :=
  ((snd (fst st))@[downRq])
    >>= (fun rqiu => Some (rqiu.(rqi_msg).(msg_type),
                           rqiu.(rqi_msg).(msg_id))).

Definition DownLockNatMsg {oifc}: OPrec oifc :=
  fun ost orq mins =>
    (orq@[downRq])
      >>=[False]
      (fun rqid =>
         match msg_value (rqi_msg rqid) with
         | VNat _ => True
         | _ => False
         end).

Definition getDownLockNatMsg {oifc} (st: StateM oifc): option nat :=
  ((snd (fst st))@[downRq])
    >>= (fun rqid =>
           match msg_value (rqi_msg rqid) with
           | VNat n => Some n
           | _ => None
           end).

Definition DownLocked {oifc}: OPrec oifc :=
  fun ost orq mins => orq@[downRq] <> None.

Definition getDownLockIndsFrom {oifc} (st: StateM oifc): option (list IdxT) :=
  ((snd (fst st))@[downRq])
    >>= (fun rqid => Some (rqid.(rqi_minds_rss))).

Definition getDownLockIdxBack {oifc} (st: StateM oifc): option IdxT :=
  ((snd (fst st))@[downRq])
    >>= (fun rqid => Some rqid.(rqi_midx_rsb)).

Definition MsgsFrom {oifc} (froms: list IdxT): OPrec oifc :=
  fun _ _ mins => idsOf mins = froms.

Definition MsgIdsFrom {oifc} (msgIds: list IdxT): OPrec oifc :=
  fun _ _ mins => map msg_id (valsOf mins) = msgIds.

Definition MsgsFromORq {oifc} (rqty: IdxT): OPrec oifc :=
  fun _ orq mins =>
    orq@[rqty] >>=[False]
       (fun rqi => idsOf mins = rqi_minds_rss rqi).

Definition MsgsFromRsUp {oifc} (dtr: DTree) (orss: list IdxT): OPrec oifc :=
  fun _ orq mins =>
    orq@[downRq] >>=[False]
       (fun rqid =>
          idsOf mins = rqi_minds_rss rqid /\
          Forall2 (fun rsUp robj =>
                     rsEdgeUpFrom dtr robj = Some rsUp)
                  (rqi_minds_rss rqid) orss).

Definition MsgsTo {oifc} (tos: list IdxT) (rule: Rule oifc): Prop :=
  forall ost orq mins,
    idsOf (snd (rule.(rule_trs) ost orq mins)) = tos.

Hint Unfold StateMBind TrsMTrs getFirstMsg
     FirstNatMsg getFirstNatMsg
     UpLockMsg getUpLockMsg
     UpLockNatMsg getUpLockNatMsg
     UpLockMsgId getUpLockMsgId
     UpLocked getUpLockIdxBack
     DownLockNatMsg getDownLockNatMsg
     DownLockMsgId getDownLockMsgId
     DownLocked getDownLockIndsFrom getDownLockIdxBack
     MsgsFrom MsgIdsFrom MsgsFromORq MsgsFromRsUp MsgsTo : RuleConds.

Module RqRsNotations.
  Notation "'do' ST" := (TrsMTrs ST) (at level 10): trs_scope.
  Notation "N <-- F ; CONT" :=
    (StateMBind F (fun N => CONT)) (at level 84, right associativity): trs_scope.
  Notation "PST --> NST" :=
    (fun PST => NST) (at level 82, only parsing): trs_scope.
  Notation "PST {{ OIFC }} --> NST" :=
    (fun PST: StateM OIFC => NST) (at level 82, only parsing): trs_scope.

  Notation "ST '.ost'" := (fst (fst ST)) (at level 11, only parsing): trs_scope.
  Notation "ST '.orq'" := (snd (fst ST)) (at level 11, only parsing): trs_scope.
  Notation "ST '.msgs'" := (snd ST) (at level 11, only parsing): trs_scope.

  Delimit Scope trs_scope with trs.

  Notation "PREC1 /\ PREC2" := (OPrecAnd PREC1 PREC2): prec_scope.
  Delimit Scope prec_scope with prec.

  Notation "'rule' '[' IDX ']' ':requires' PREC ':transition' TRS" :=
    {| rule_idx := IDX;
       rule_precond := PREC%prec;
       rule_trs := TRS%trs |} (at level 5).
End RqRsNotations.

Definition AtomicMsgOutsInv {oifc} (mp: MsgOutPred oifc)
           (eouts: list (Id Msg)) (nst: MState oifc): Prop :=
  Forall (fun eout => mp eout nst.(bst_oss) nst.(bst_orqs)) eouts.

Definition AtomicInv {oifc} (mp: MsgOutPred oifc):
  list (Id Msg) (* inits *) ->
  MState oifc (* starting state *) ->
  MHistory (* atomic history *) ->
  list (Id Msg) (* eouts *) ->
  MState oifc (* ending state *) -> Prop :=
  fun inits st1 hst eouts st2 =>
    AtomicMsgOutsInv mp eouts st2.

Ltac disc_AtomicInv :=
  repeat
    match goal with
    | [H: AtomicInv _ _ _ _ _ _ |- _] => red in H; dest
    end.

Ltac disc_rule_conds_const_unit :=
  match goal with
  | [H: context [match msg_value ?msg with
                 | VNat _ => True
                 | _ => _
                 end] |- _] =>
    let Hmsg := fresh "Hmsg" in
    destruct (msg_value msg) eqn:Hmsg; try (exfalso; auto; fail); simpl in *
  | [H: ?orq@[?i] <> None |- _] =>
    let rqi := fresh "rqi" in
    let Horq := fresh "Horq" in
    destruct (orq@[i]) as [rqi|] eqn:Horq;
    [clear H; simpl in *|exfalso; auto]

  | [H: (?m@[?i]) >>=[False] (fun _ => _) |- _] =>
    match type of m with
    | M.t (ORq _) =>
      let orq := fresh "orq" in
      let Horq := fresh "Horq" in
      destruct (m@[i]) as [orq|] eqn:Horq;
      [simpl in *|exfalso; auto]
    | ORqs _ =>
      let orq := fresh "orq" in
      let Horq := fresh "Horq" in
      destruct (m@[i]) as [orq|] eqn:Horq;
      [simpl in *|exfalso; auto]
    | M.t (RqInfo _) =>
      let rqi := fresh "rqi" in
      let Hrqi := fresh "Hrqi" in
      destruct (m@[i]) as [rqi|] eqn:Hrqi;
      [simpl in *|exfalso; auto]
    | ORq _ =>
      let rqi := fresh "rqi" in
      let Hrqi := fresh "Hrqi" in
      destruct (m@[i]) as [rqi|] eqn:Hrqi;
      [simpl in *|exfalso; auto]
    | M.t (OState _) =>
      let ost := fresh "ost" in
      let Host := fresh "Host" in
      destruct (m@[i]) as [ost|] eqn:Host;
      [simpl in *|exfalso; auto]
    | OStates _ =>
      let ost := fresh "ost" in
      let Host := fresh "Host" in
      destruct (m@[i]) as [ost|] eqn:Host;
      [simpl in *|exfalso; auto]
    end
  | [H1: ?t = _, H2: context[?t] |- _] =>
    match type of t with
    | option _ => rewrite H1 in H2; simpl in H2
    | Value => rewrite H1 in H2; simpl in H2
    end

  | [H: (_ /\oprec _) _ _ _ |- _] => destruct H
  | [H: rule_precond _ _ _ _ |- _] => progress simpl in H
  | [H: rule_trs _ _ _ _ = _ |- _] => progress simpl in H
  | [H: map msg_id (valsOf ?rins) = [_]%list |- _] =>
    let rin := fresh "rin" in
    let rmsg := fresh "rmsg" in
    destruct rins as [|[rin rmsg] [|]]; try discriminate;
    simpl in H; inv H
  | [H: map msg_id (valsOf [_]%list) = [_]%list |- _] => simpl in H; inv H
  | [H: map _ [_]%list = [_]%list |- _] => progress simpl in H
  | [H: context [hd_error [_]%list] |- _] => progress simpl in H
  | [H: SubList [_] _ |- _] => apply SubList_singleton_In in H
  | [H: [_]%list = rqi_minds_rss _ |- _] => rewrite <-H in *
  | [H: [_]%list = rqi_midx_rsb _ |- _] => rewrite <-H in *
  | [H: Forall2 _ [_]%list [_]%list |- _] => inv H
  | [H: Forall2 _ nil nil |- _] => clear H
  | [H: ?t = ?t -> _ |- _] => specialize (H eq_refl)
  | [H: ?P -> _, Hp: ?P |- _] =>
    match type of P with
    | Prop => specialize (H Hp)
    end
  end.

Ltac disc_rule_conds_const :=
  repeat (try disc_rule_conds_unit_simpl;
          try disc_rule_conds_const_unit;
          subst; simpl in * ).

Ltac disc_minds_const :=
  repeat
    match goal with
    | [H: parentIdxOf ?dtr _ = Some ?oidx |- _] =>
      is_const oidx;
      pose proof (parentIdxOf_child_indsOf _ _ H);
      dest_in; try discriminate; simpl in *; clear H
    | [H: rqEdgeUpFrom ?dtr ?oidx = Some ?midx |- _] =>
      is_const oidx; inv H
    | [H: rsEdgeUpFrom ?dtr ?oidx = Some ?midx |- _] =>
      is_const oidx; inv H
    | [H: edgeDownTo ?dtr ?oidx = Some ?midx |- _] =>
      is_const oidx; inv H
    end.

Ltac solve_rule_conds_const :=
  repeat
    (repeat (autounfold with RuleConds in *; dest); intros;
     disc_rule_conds_const;
     constr_rule_conds).

Ltac disc_rule_conds_ex :=
  repeat (repeat (autounfold with RuleConds in *; dest); intros;
          disc_rule_conds; dest;
          disc_rule_conds_const).

Ltac solve_rule_conds_ex :=
  repeat (repeat (autounfold with RuleConds in *; dest); intros;
          disc_rule_conds; dest;
          solve_rule_conds_const).

Ltac atomic_cont_exfalso_bound msgOutPred :=
  exfalso;
  disc_rule_conds_ex;
  repeat 
    match goal with
    | [H1: AtomicMsgOutsInv _ ?eouts _, H2: In _ ?eouts |- _] =>
      red in H1; rewrite Forall_forall in H1;
      specialize (H1 _ H2); simpl in H1
    | [H: msgOutPred _ _ _ |- _] => red in H
    | [H1: caseDec _ ?sig _ _ |- _] =>
      match sig with
      | sigOf (?midx, ?msg) =>
        match goal with
        | [H2: msg_id ?msg = ?mid, H3: msg_type ?msg = ?mty |- _] =>
          progress replace sig with (midx, (mty, mid)) in H1
            by (unfold sigOf; simpl; rewrite H2, H3; reflexivity);
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

Ltac disc_sig_caseDec :=
  match goal with
  | [H1: caseDec _ ?sig _ _ |- _] =>
    match sig with
    | sigOf (?midx, ?msg) =>
      match goal with
      | [H2: msg_id ?msg = ?mid, H3: msg_type ?msg = ?mty |- _] =>
        progress replace sig with (midx, (mty, mid)) in H1
          by (unfold sigOf; simpl; rewrite H2, H3; reflexivity);
        simpl in H1
      end
    end
  end.

Ltac disc_msg_preds_with Hl Hin :=
  match type of Hl with
  | AtomicMsgOutsInv _ ?eouts _ =>
    red in Hl; rewrite Forall_forall in Hl;
    specialize (Hl _ Hin); simpl in Hl;
    red in Hl; disc_sig_caseDec
  end.

Ltac disc_msg_preds Hin :=
  match goal with
  | [H: AtomicMsgOutsInv _ _ _ |- _] =>
    let Hl := fresh "H" in
    pose proof H as Hl;
    disc_msg_preds_with Hl Hin
  end.

Ltac solve_in_mp :=
  repeat
    match goal with
    | [ |- InMP _ _ _] => eassumption
    | [H: FirstMPI _ (?midx, _) |- InMP ?midx _ _] =>
      apply FirstMP_InMP; eassumption

    | [ |- InMP ?midx _ (enqMP ?midx _ _) ] =>
      apply InMP_or_enqMP; left; eauto; fail
    | [ |- InMP ?midx _ (enqMP _ _ _) ] =>
      apply InMP_or_enqMP; right
    | [ |- InMP _ _ (deqMP _ _) ] =>
      eapply deqMP_InMP; try eassumption; try discriminate
    end.

Ltac exfalso_uplock_rq_rs upidx urqUp udown :=
  progress
    match goal with
    | [H: UpLockInvORq _ _ _ _ _ |- _] =>
      eapply upLockInvORq_rqUp_down_rssQ_False
        with (pidx:= upidx) (rqUp:= urqUp) (down:= udown) in H;
      try reflexivity; auto
    end;
  repeat
    match goal with
    | [ |- Datatypes.length (findQ _ _) >= 1] =>
      eapply findQ_length_ge_one; solve_in_mp; fail
    | [ |- Datatypes.length (rssQ _ _) >= 1] =>
      eapply rssQ_length_ge_one; [|solve_in_mp; fail]
    | [ |- msg_type _ = _] => try reflexivity; try eassumption
    end.

Ltac exfalso_uplock_rq_two upidx urqUp m1 m2 :=
  progress
    match goal with
    | [H: UpLockInvORq _ _ _ _ _ |- _] =>
      eapply upLockInvORq_rqUp_length_two_False
        with (pidx:= upidx) (rqUp:= urqUp) in H;
      try reflexivity; auto
    end;
  repeat
    match goal with
    | [ |- Datatypes.length (findQ _ _) >= 2] =>
      eapply findQ_length_two with (msg1:= m1) (msg2:= m2); auto
    | [ |- InMP _ _ _] => solve_in_mp; fail
    | [ |- _ <> _] => intro Hx; subst; simpl in *; discriminate
    end.

Ltac exfalso_uplock_rs_two upidx udown m1 m2 :=
  progress
    match goal with
    | [H: UpLockInvORq _ _ _ _ _ |- _] =>
      eapply upLockInvORq_down_rssQ_length_two_False
        with (pidx:= upidx) (down:= udown) in H;
      try reflexivity; auto
    end;
  repeat
    match goal with
    | [ |- Datatypes.length (rssQ _ _) >= 2] =>
      eapply rssQ_length_two with (msg1:= m1) (msg2:= m2);
      try solve_in_mp; try reflexivity; try eassumption
    | [ |- _ <> _] => intro Hx; subst; simpl in *; discriminate
    end.

Ltac get_child_uplock_from_parent :=
  repeat
    match goal with
    | [H: UpLockInvORq _ _ _ _ _ |- _] =>
      eapply upLockInvORq_parent_locked_locked in H;
      try reflexivity; dest;
      [|red; simpl; disc_rule_conds_const; eauto; fail]
    | [H: (?oorq >>=[[]] _)@[upRq] <> None |- _] =>
      destruct oorq; simpl in H; [|exfalso; auto]
    end.

Ltac rule_immd := left.
Ltac rule_immu := right; left.
Ltac rule_rquu := do 2 right; left; split; [|left].
Ltac rule_rqud := do 2 right; left; split; [|right; left].
Ltac rule_rqdd := do 2 right; left; split; [|right; right].
Ltac rule_rsdd := do 3 right; left; split; [left|].
Ltac rule_rsu := do 3 right; left; split; [right|].
Ltac rule_rsrq := do 4 right.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

