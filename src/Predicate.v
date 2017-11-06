Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.

Set Implicit Arguments.

(** Notion of ordinary invariants *)

Definition OInv := OState (* object state *) -> Prop.
Definition Inv := M.t (* object index *) OInv.

Definition InvSat (inv: Inv) (oss: ObjectStates) :=
  forall oidx oinv,
    inv@[oidx] = Some oinv ->
    match oss@[oidx] with
    | Some os => oinv os
    | None => False
    end.

Record InvO :=
  { io_idx: IdxT;
    io_st: OState;
    io_inv: OInv;
    io_sat: io_inv io_st }.

Record InvOs :=
  { ios_oss: ObjectStates;
    ios_inv: Inv;
    ios_sat: InvSat ios_inv ios_oss }.

Definition Pred := Inv.

(** Notion of transaction predicates *)

Inductive VLoc :=
| VFromState: forall (oidx kidx: IdxT), VLoc
| VFromMsg: VLoc.

Inductive StateDiff :=
| ConstDiff:
    forall (target: VLoc) (const: Value), StateDiff
| FuncDiff:
    forall (target: VLoc)
           (operands: list VLoc)
           (* Note that [Value] can take multiple [Value]s inductively *)
           (func: Value -> Value), StateDiff.

Definition VMoved (from to: VLoc) := FuncDiff to (from :: nil) id.

Definition SimR := ObjectStates -> ObjectStates -> Prop.

Definition LiftCond (oidx: IdxT) (cond: Cond) :=
  fun oss: ObjectStates =>
    oss@[oidx] >>=[False]
       (fun ost => cond ost).

Definition Invertible {A} := @id A.

Inductive StateSimCond (sim: SimR) (soss: ObjectStates) (oidx: IdxT) (cond: Cond): Prop :=
| SSPIntro:
    forall ioss,
      (Invertible sim) ioss soss ->
      LiftCond oidx cond ioss ->
      StateSimCond sim soss oidx cond.

Definition TrsPred :=
  Value (* request *) -> ObjectStates (* prestate *) -> 
  ObjectStates (* poststate *) -> Value (* response *) -> Prop.

(** Related tactics *)

Ltac mv_rewriter :=
  repeat
    match goal with
    | [H: Some _ = M.find _ _ |- _] => apply eq_sym in H
    | [H: None = M.find _ _ |- _] => apply eq_sym in H
    | [H1: M.find ?m ?k = Some _, H2: M.find ?m ?k = Some _ |- _] =>
      rewrite H1 in H2; inv H2
    | [H1: M.find ?m ?k = Some _, H2: M.find ?m ?k = None |- _] =>
      rewrite H1 in H2; discriminate
    end.

Ltac inv_invertible :=
  repeat
    match goal with
    | [H: context[Invertible] |- _] => inv H
    end.

Ltac inv_lprec :=
  repeat
    match goal with
    | [H: LiftCond _ _ _ |- _] => unfold LiftCond in H
    | [H: context[tbind False ?ov _] |- _] =>
      let o := fresh "o" in
      remember ov as o; destruct o; simpl in H; [|intuition idtac]
    end.

Ltac inv_ssp :=
  repeat
    match goal with
    | [H: StateSimCond _ _ _ _ |- _] => inv H
    end.

Ltac ssp := intros; inv_ssp; inv_lprec; inv_invertible; mv_rewriter.

Ltac no_vloc_st oss oidx kidx :=
  lazymatch goal with
  | [vloc := (oss, VFromState oidx kidx, _) |- _] => fail
  | _ => idtac
  end.

(* NOTE: there's only one [VFromMsg] information per a transaction. *)
Ltac no_vloc_msg :=
  lazymatch goal with
  | [vloc := (VFromMsg, _) |- _] => fail
  | _ => idtac
  end.

Ltac collect_vloc :=
  repeat
    match goal with
    | [H1: M.find ?oidx ?oss = Some ?ost, H2: M.find ?kidx (ost_st ?ost) = Some ?v |- _] =>
      no_vloc_st oss oidx kidx;
      let vloc := fresh "vloc" in
      set (oss, VFromState oidx kidx, v) as vloc
    | [H: pmsg_postcond _ _ ?v _ |- _] =>
      no_vloc_msg;
      let vloc := fresh "vloc" in
      set (VFromMsg, v) as vloc
    end.

Ltac simpl_postcond :=
  repeat
    match goal with
    | [H: pmsg_postcond _ _ _ _ |- _] => simpl in H; mv_rewriter
    end.

Ltac no_diff sdf :=
  lazymatch goal with
  | [df := sdf |- _] => fail
  | _ => idtac
  end.

Ltac collect_diff oss1 oss2 :=
  repeat
    match goal with
    | [vloc := (oss2, ?wh, ?v) |- _] =>
      is_pure_const v;
      no_diff (ConstDiff wh v);
      let df := fresh "df" in
      pose (ConstDiff wh v) as df
    | [vloc1 := (oss1, ?wh1, ?v), vloc2 := (oss2, ?wh2, ?v) |- _] =>
      not_pure_const v;
      first [is_equal wh1 wh2 |
             no_diff (VMoved wh1 wh2);
             let df := fresh "df" in
             pose (VMoved wh1 wh2) as df]
    end.
