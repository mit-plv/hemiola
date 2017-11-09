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

Inductive VDiff :=
| ConstDiff:
    forall (target: VLoc) (const: Value), VDiff
| FuncDiff:
    forall (target: VLoc)
           (operands: list VLoc)
           (* Note that [Value] can take multiple [Value]s inductively *)
           (func: Value -> Value), VDiff.

Definition VMoved (from to: VLoc): VDiff :=
  FuncDiff to (from :: nil) id.

Definition SimR := ObjectStates -> ObjectStates -> Prop.

Definition LiftCond (oidx: IdxT) (cond: Cond) :=
  fun oss: ObjectStates =>
    oss@[oidx] >>=[False]
       (fun ost => cond ost).

Definition TrsPred :=
  Value (* request *) -> ObjectStates (* prestate *) -> 
  ObjectStates (* poststate *) -> Value (* response *) -> Prop.

