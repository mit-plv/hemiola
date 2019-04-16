Require Import Common List ListSupport HVector FMap.
Require Import Syntax RqRsTopo RqRsFacts.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

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

Hint Unfold StateMBind TrsMTrs getFirstMsg
     FirstNatMsg getFirstNatMsg
     UpLockNatMsg getUpLockNatMsg UpLocked getUpLockIdxBack
     DownLockNatMsg getDownLockNatMsg DownLocked getDownLockIdxBack
  : RuleConds.

Notation "'do' ST" := (TrsMTrs ST) (at level 10): trs_scope.
Notation "N <-- F ; CONT" :=
  (StateMBind F (fun N => CONT)) (at level 15, right associativity): trs_scope.
Notation "PST --> NST" :=
  (fun PST => NST) (at level 12, only parsing): trs_scope.
Notation "PST {{ OIFC }} --> NST" :=
  (fun PST: StateM OIFC => NST) (at level 12, only parsing): trs_scope.

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

Ltac disc_rule_conds_const_step :=
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
  | [H: context [(?orq@[?i]) >>=[False] (fun _ => _)] |- _] =>
    let rqiu := fresh "rqiu" in
    let Horq := fresh "Horq" in
    destruct (orq@[i]) as [rqiu|] eqn:Horq;
    [simpl in *|exfalso; auto]
  | [H1: ?t = _, H2: context[?t] |- _] =>
    match type of t with
    | option _ => rewrite H1 in H2; simpl in H2
    | Value => rewrite H1 in H2; simpl in H2
    end
      
  | [H: (_ /\oprec _) _ _ _ |- _] => destruct H
  | [H: rule_precond _ _ _ _ |- _] => progress simpl in H
  | [H: rule_trs _ _ _ _ = _ |- _] => progress simpl in H
  | [H: (_, _) = (_, _) |- _] => inv H
  | [H: idsOf ?rins = [_]%list |- _] =>
    let rin := fresh "rin" in
    let rmsg := fresh "rmsg" in
    destruct rins as [|[rin rmsg] [|]]; try discriminate;
    simpl in H; inv H
  | [H: idsOf [_] = [_]%list |- _] => simpl in H; inv H
  | [H: map msg_id (valsOf ?rins) = [_]%list |- _] =>
    let rin := fresh "rin" in
    let rmsg := fresh "rmsg" in
    destruct rins as [|[rin rmsg] [|]]; try discriminate;
    simpl in H; inv H
  | [H: map msg_id (valsOf [_]%list) = [_]%list |- _] => simpl in H; inv H
  | [H: map _ [_]%list = [_]%list |- _] => progress simpl in H
  | [H: context [hd_error [_]%list] |- _] => progress simpl in H
  | [H: [_]%list = [_]%list |- _] => inv H
  | [H: Forall _ [_]%list |- _] => inv H
  | [H: Forall _ nil |- _] => clear H
  end.

Ltac disc_rule_conds_const :=
  repeat (disc_rule_conds_const_step; subst; simpl in * ).

Ltac disc_rule_conds_ex :=
  repeat (
      repeat (autounfold with RuleConds in *; dest);
      disc_rule_conds_const;
      disc_rule_conds; dest).
      
Ltac solve_rule_conds_const :=
  repeat
    (repeat autounfold with RuleConds in *; intros;
     disc_rule_conds_const;
     constr_rule_conds).

Ltac solve_rule_conds_ex :=
  repeat 
    (repeat (autounfold with RuleConds in *; dest);
     disc_rule_conds; dest; solve_rule_conds_const).

Close Scope list.
Close Scope hvec.
Close Scope fmap.

