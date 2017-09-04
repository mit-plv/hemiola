Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.

Definition OInvariant := M.t (StateT -> Prop).

Definition OInvariantHolds (inv: OInvariant) (oss: ObjectStates) :=
  forall idx,
    match inv@[idx], oss@[idx] with
    | Some oinv, Some os => oinv os
    | _, _ => True
    end.

Record OInvariants (sys: System) :=
  { oinv_inv : OInvariant;
    oinv_init : OInvariantHolds oinv_inv (getObjectStatesInit (sys_objs sys)) }.

Section Synthesis.

  (** Requirements *)
  Variables (sys: System) (* a topology among objects *)
            (invs: OInvariants sys).

End Synthesis.

