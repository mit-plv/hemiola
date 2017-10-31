Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.

Set Implicit Arguments.

Definition OInv := OState (* object state *) -> Value -> Prop.
Definition Inv := M.t (* object index *) OInv.

Definition InvSat (inv: Inv) (val: Value) (oss: ObjectStates) :=
  forall oidx oinv,
    inv@[oidx] = Some oinv ->
    match oss@[oidx] with
    | Some os => oinv os val
    | None => False
    end.

Record InvO :=
  { io_idx: IdxT;
    io_st: OState;
    io_inv: OInv;
    io_val: Value;
    io_sat: io_inv io_st io_val }.

Record InvOs :=
  { ios_oss: ObjectStates;
    ios_inv: Inv;
    ios_val: Value;
    ios_sat: InvSat ios_inv ios_val ios_oss }.

Definition Pred := Inv.

