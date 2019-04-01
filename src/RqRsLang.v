Require Import Common List ListSupport HVector FMap.
Require Import Syntax RqRsTopo.

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

Notation "'do' ST" := (TrsMTrs ST) (at level 10): trs_scope.
Notation "N <-- F ; CONT" :=
  (StateMBind F (fun N => CONT)) (at level 15, right associativity): trs_scope.
Notation "PST --> NST" :=
  (fun PST => NST) (at level 12, only parsing): trs_scope.
Notation "PST {{ OIFC }} --> NST" :=
  (fun PST: StateM OIFC => NST) (at level 12, only parsing): trs_scope.

Notation "ST '.ost'" := (fst (fst ST)) (at level 11): trs_scope.
Notation "ST '.orq'" := (snd (fst ST)) (at level 11): trs_scope.
Notation "ST '.msgs'" := (snd ST) (at level 11): trs_scope.

Delimit Scope trs_scope with trs.

Notation "PREC1 /\ PREC2" := (OPrecAnd PREC1 PREC2): prec_scope.
Delimit Scope prec_scope with prec.

Notation "'rule' '[' IDX ']' ':requires' PREC ':transition' TRS" :=
  {| rule_idx := IDX;
     rule_precond := PREC%prec;
     rule_trs := TRS%trs |} (at level 5).

Close Scope list.
Close Scope hvec.
Close Scope fmap.

