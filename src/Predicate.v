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

Definition TrsPred :=
  Value (* request *) -> ObjectStates (* prestate *) -> 
  ObjectStates (* poststate *) -> Value (* response *) -> Prop.

