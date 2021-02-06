Require Import Common Lia List ListSupport HVector FMap.
Require Import Syntax Topology Semantics SemFacts StepM Invariant Serial.

Require Import RqRsTopo RqRsFacts RqRsInvLock.

Set Implicit Arguments.

Import MonadNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Definition rootDmc (ridx: IdxT) :=
  {| dmc_me := ridx;
     dmc_ups := nil;
     dmc_downs := nil |}.

Section DecValue.
  Context `{DecValue}.

  Record StateM `{OStateIfc} :=
    { ost: OState;
      orq: ORq Msg;
      msgs: list (Id Msg) }.

  Definition StateMTrs `{OStateIfc} :=
    StateM -> option StateM.

  Definition TrsMTrs `{OStateIfc} (mtrs: StateMTrs): OTrs :=
    fun post porq pmsgs =>
      match mtrs (Build_StateM _ post porq pmsgs) with
      | Some st => (st.(ost), st.(orq), st.(msgs))
      | None => (post, porq, pmsgs)
      end.

  Definition FirstMsg `{OStateIfc}: OPrec :=
    fun ost orq mins => hd_error mins <> None.

  Definition nilMsg : Msg :=
    {| msg_id := ii; msg_type := MRq; msg_addr := tt; msg_value := t_default |}.

  Definition nilIdMsg : Id Msg := (ii, nilMsg).
  Definition getFirstMsg  (msgs: list (Id Msg)): option Msg :=
    idm <-- (hd_error msgs); Some (valOf idm).
  Definition getFirstMsgI (msgs: list (Id Msg)): Msg :=
    (hd_error msgs) >>=[nilMsg] (fun idm => valOf idm).
  Definition getFirstIdMsg (msgs: list (Id Msg)): option (Id Msg) :=
    idm <-- (hd_error msgs); Some idm.
  Definition getFirstIdMsgI (msgs: list (Id Msg)): Id Msg :=
    (hd_error msgs) >>=[nilIdMsg] (fun idm => idm).

  Definition UpLockMsgId `{OStateIfc} (mty: bool) (mid: IdxT): OPrec :=
    fun ost orq mins =>
      (orq@[upRq])
        >>=[False]
        (fun rqiu =>
           rqiu.(rqi_msg)
                  >>=[False] (fun rq => rq.(msg_type) = mty /\ rq.(msg_id) = mid)).
  Definition getUpLockMsgId (orq: ORq Msg): option (bool * IdxT) :=
    rqiu <-- orq@[upRq];
      rq <-- rqiu.(rqi_msg);
      Some (rq.(msg_type), rq.(msg_id)).

  Definition UpLockMsg `{OStateIfc}: OPrec :=
    fun ost orq mins =>
      match orq@[upRq] with
      | Some _ => True
      | _ => False
      end.
  Definition getUpLockMsg (orq: ORq Msg): option Msg :=
    rqiu <-- orq@[upRq]; rqi_msg rqiu.

  Definition UpLockIdxBack `{OStateIfc}: OPrec :=
    fun ost orq mins =>
      (orq@[upRq])
        >>=[False]
        (fun rqiu => rqiu.(rqi_midx_rsb) >>=[False] (fun _ => True)).
  Definition getUpLockIdxBack (orq: ORq Msg): option IdxT :=
    rqiu <-- orq@[upRq]; rqi_midx_rsb rqiu.
  Definition getUpLockIdxBackI (orq: ORq Msg): IdxT :=
    (getUpLockIdxBack orq) >>=[ii] (fun idx => idx).

  Definition UpLockBackNone `{OStateIfc}: OPrec :=
    fun ost orq mins =>
      (orq@[upRq])
        >>=[False] (fun rqiu => rqiu.(rqi_midx_rsb) = None /\
                                rqiu.(rqi_msg) = None).

  Definition DownLockMsgId `{OStateIfc} (mty: bool) (mid: IdxT): OPrec :=
    fun ost orq mins =>
      (orq@[downRq])
        >>=[False]
        (fun rqid =>
           rqid.(rqi_msg)
                  >>=[False] (fun rq => rq.(msg_type) = mty /\ rq.(msg_id) = mid)).
  Definition getDownLockMsgId (orq: ORq Msg): option (bool * IdxT) :=
    rqid <-- orq@[downRq];
      rq <-- rqid.(rqi_msg);
      Some (rq.(msg_type), rq.(msg_id)).

  Definition DownLockMsg `{OStateIfc}: OPrec :=
    fun ost orq mins =>
      match orq@[downRq] with
      | Some _ => True
      | _ => False
      end.
  Definition getDownLockMsg (orq: ORq Msg): option Msg :=
    rqid <-- orq@[downRq]; rqi_msg rqid.

  Definition DownLockIdxBack `{OStateIfc}: OPrec :=
    fun ost orq mins =>
      (orq@[downRq])
        >>=[False]
        (fun rqid =>
           rqid.(rqi_midx_rsb) >>=[False] (fun _ => True)).
  Definition getDownLockIndsFrom (orq: ORq Msg): option (list IdxT) :=
    rqid <-- orq@[downRq]; Some (map fst (rqi_rss rqid)).
  Definition getDownLockIdxBack (orq: ORq Msg): option IdxT :=
    rqid <-- orq@[downRq]; rqi_midx_rsb rqid.
  Definition getDownLockIdxBackI (orq: ORq Msg): IdxT :=
    (getDownLockIdxBack orq) >>=[ii] (fun idx => idx).

  Definition DownLockBackNone `{OStateIfc}: OPrec :=
    fun ost orq mins =>
      (orq@[downRq])
        >>=[False] (fun rqid => rqid.(rqi_midx_rsb) = None /\
                                rqid.(rqi_msg) = None).

  Definition getFirstIdxFromI (inds: list IdxT): IdxT :=
    (hd_error inds) >>=[ii] (fun idx => idx).

  Definition MsgsFrom `{OStateIfc} (froms: list IdxT): OPrec :=
    fun _ _ mins => idsOf mins = froms.

  Definition MsgIdsFrom `{OStateIfc} (msgIds: list IdxT): OPrec :=
    fun _ _ mins => map msg_id (valsOf mins) = msgIds.

  Definition MsgIdFromEach `{OStateIfc} (msgId: IdxT): OPrec :=
    fun _ _ mins => Forall (fun idm => msg_id (valOf idm) = msgId) mins.

  Definition MsgsFromORq `{OStateIfc} (rqty: IdxT): OPrec :=
    fun _ orq mins =>
      orq@[rqty] >>=[False]
         (fun rqi => idsOf mins = map fst (rqi_rss rqi)).

End DecValue.

Hint Unfold TrsMTrs FirstMsg getFirstMsg getFirstMsgI getFirstIdMsg getFirstIdMsgI
     UpLockMsgId getUpLockMsgId UpLockMsg getUpLockMsg
     UpLockIdxBack getUpLockIdxBack getUpLockIdxBackI UpLockBackNone
     DownLockMsgId getDownLockMsgId DownLockMsg getDownLockMsg
     DownLockIdxBack DownLockBackNone getDownLockIndsFrom getDownLockIdxBack getDownLockIdxBackI
     getFirstIdxFromI MsgsFrom MsgIdsFrom MsgIdFromEach MsgsFromORq : RuleConds.

Definition initORqs `{DecValue} (oinds: list IdxT): ORqs Msg :=
  fold_right (fun i m => m +[i <- []]) [] oinds.

Lemma initORqs_GoodORqsInit:
  forall `{DecValue} oinds, GoodORqsInit (initORqs oinds).
Proof.
  red; intros.
  induction oinds; simpl; intros; mred.
Qed.

Lemma initORqs_value:
  forall `{DecValue} oinds oidx,
    In oidx oinds ->
    (initORqs oinds)@[oidx] = Some [].
Proof.
  induction oinds; intros; [exfalso; auto|].
  simpl; icase oidx; mred; auto.
Qed.

Lemma initORqs_None:
  forall `{DecValue} oinds oidx,
    ~ In oidx oinds ->
    (initORqs oinds)@[oidx] = None.
Proof.
  induction oinds; intros; [reflexivity|].
  simpl; mred.
  - elim H0; left; reflexivity.
  - apply IHoinds.
    intro Hx; elim H0; right; assumption.
Qed.

Declare Scope trs_scope.
Declare Scope prec_scope.

Module RqRsNotations.
  Include MonadNotations.
  Delimit Scope monad_scope with monad.

  Notation "'do' ST" := (TrsMTrs ST%monad) (at level 10): trs_scope.
  Notation "v ::= e ; c" :=
    (let v := e in c) (at level 84, right associativity): trs_scope.
  Notation "PST --> NST" :=
    (fun PST => NST) (at level 82, only parsing): trs_scope.
  Notation "'!|' PST1 ',' PST2 '|' --> NST" :=
    (fun PST1 PST2 => NST) (at level 82, only parsing): trs_scope.
  Notation "'!|' PST1 ',' PST2 ',' PST3 '|' --> NST" :=
    (fun PST1 PST2 PST3 => NST) (at level 82, only parsing): trs_scope.
  Notation "'!|' PST1 ',' PST2 ',' PST3 ',' PST4 '|' --> NST" :=
    (fun PST1 PST2 PST3 PST4 => NST) (at level 82, only parsing): trs_scope.
  Notation "'!|' PST1 ',' PST2 ',' PST3 ',' PST4 ',' PST5 '|' --> NST" :=
    (fun PST1 PST2 PST3 PST4 PST5 => NST) (at level 82, only parsing): trs_scope.
  Notation "'return' v" :=
    (Some v) (at level 80, only parsing): trs_scope.
  Notation "'{{' OST ',' ORQ ',' MSGS '}}'" :=
    {| ost:= OST; orq:= ORQ; msgs:= MSGS |} (at level 80): trs_scope.
  Delimit Scope trs_scope with trs.

  Notation "PREC1 /\ PREC2" := (OPrecAnd PREC1 PREC2): prec_scope.
  Notation "PREC1 -> PREC2" := (OPrecImp PREC1 PREC2): prec_scope.
  Notation "⊤" := (fun _ _ _ => True): prec_scope.
  Notation "⊥" := (fun _ _ _ => False): prec_scope.
  Delimit Scope prec_scope with prec.

  Notation "'rule' '[' IDX ']' ':requires' PREC ':transition' TRS" :=
    {| rule_idx := IDX;
       rule_precond := PREC%prec;
       rule_trs := TRS%trs |} (at level 5).
End RqRsNotations.

Ltac disc_rule_conds_const_unit :=
  match goal with
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
    | M.t (@OState _) =>
      let ost := fresh "ost" in
      let Host := fresh "Host" in
      destruct (m@[i]) as [ost|] eqn:Host;
      [simpl in *|exfalso; auto]
    | @OStates _ =>
      let ost := fresh "ost" in
      let Host := fresh "Host" in
      destruct (m@[i]) as [ost|] eqn:Host;
      [simpl in *|exfalso; auto]
    end
  | [H: ?ov >>=[False] (fun _ => _) |- _] =>
    match type of ov with
    | option Msg =>
      let msg := fresh "msg" in
      let Hmsg := fresh "Hmsg" in
      destruct ov as [msg|] eqn:Hmsg;
      [simpl in *|exfalso; auto]
    | option IdxT =>
      let idx := fresh "idx" in
      let Hidx := fresh "Hidx" in
      destruct ov as [idx|] eqn:Hidx;
      [simpl in *|exfalso; auto]
    end

  | [H1: ?t = _, H2: context[?t] |- _] =>
    match type of t with
    | option _ => rewrite H1 in H2; simpl in H2
    end
  | [H1: ?t = _ |- context[?t] ] =>
    match type of t with
    | option _ => rewrite H1; simpl
    end

  | [H: (_ /\oprec _) _ _ _ |- _] => destruct H
  | [H: rule_precond _ _ _ _ |- _] => progress simpl in H
  | [H: rule_trs _ _ _ _ = _ |- _] => progress simpl in H
  | [H: map msg_id (valsOf ?rins) = [_]%list |- _] =>
    let rin := fresh "rin" in
    let rmsg := fresh "rmsg" in
    destruct rins as [|[rin rmsg] [|]]; try discriminate;
    simpl in H; inv H

  | [H: idsOf _ = nil |- _] => rewrite H in *
  | [H: [_]%list = [_]%list |- _] => inv H
  | [H: map msg_id (valsOf [_]%list) = [_]%list |- _] => simpl in H; inv H
  | [H: map _ [_]%list = [_]%list |- _] => progress simpl in H
  | [H: context [hd_error [_]%list] |- _] => progress simpl in H
  | [H: SubList [_] _ |- _] => apply SubList_singleton_In in H
  | [H: [_]%list = map fst (rqi_rss _) |- _] => rewrite <-H in *
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
