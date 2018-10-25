Set Implicit Arguments.

Require Import List String Arith Vector.
Require Import Program.Equality.
Import VectorNotations.

Section HVector.

  Fixpoint hvec {n} (ifc: Vector.t Type n) : Type :=
    match ifc with
    | [] => unit
    | t :: ifc' => (t * hvec ifc')%type
    end.

  Definition hvnil: hvec [] := tt.

  Definition hvcons
             {A} (a: A)
             {n} {ifc: Vector.t Type n}
             (vec: hvec ifc): hvec (A :: ifc) :=
    (a, vec).

  Fixpoint hvec_ith {n} {ifc: Vector.t Type n}
           (vec: hvec ifc) (i: Fin.t n):
    Vector.nth ifc i.
  Proof.
    destruct i.
    - dependent destruction ifc.
      exact (fst vec).
    - dependent destruction ifc.
      exact (hvec_ith _ ifc (snd vec) i).
  Defined.

  Fixpoint hvec_upd {n} {ifc: Vector.t Type n}
           (vec: hvec ifc) (i: Fin.t n) (v: Vector.nth ifc i)
           {struct ifc}:
    hvec ifc.
  Proof.
    destruct i.
    - dependent destruction ifc.
      exact (v, snd vec).
    - dependent destruction ifc.
      exact (fst vec, hvec_upd _ ifc (snd vec) i v).
  Defined.

End HVector.

