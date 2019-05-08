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
     UpLockNatMsg getUpLockNatMsg UpLocked getUpLockIdxBack
     DownLockNatMsg getDownLockNatMsg DownLocked getDownLockIdxBack
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
  end.

Ltac disc_rule_conds_const :=
  repeat (try disc_rule_conds_unit_simpl;
          try disc_rule_conds_const_unit;
          subst; simpl in * ).

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

