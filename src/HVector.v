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

  Definition hvhead
             {n} {ifc: Vector.t Type (S n)}
             (vec: hvec ifc): Vector.nth ifc (@Fin.F1 n) :=
    Vector.caseS (fun n ifc => hvec ifc -> Vector.nth ifc (@Fin.F1 n))
                 (fun h n t => fst) ifc vec.

  Definition hvtail
             {A} {n} {ifc: Vector.t Type (S n)}
             (vec: hvec (A :: ifc)): hvec ifc :=
    snd vec.
  
  Definition Vector_caseS'
             {A'} (Q : nat -> Type)
             (P : forall {n} (v : Vector.t A' (S n)), Q n -> Type)
             (H : forall h {n} t q, @P n (h :: t) q) {n} (v: Vector.t A' (S n))
             (q : Q n)
    : P v q.
  Proof.
    specialize (fun h t => H h _ t q).
    change n with (pred (S n)) in H, q |- *.
    set (Sn := S n) in *.
    pose (fun Sn (v : Vector.t A' Sn) (q : Q (pred Sn)) =>
            match Sn return Vector.t A' Sn -> Q (pred Sn) -> Type with
            | S n' => P n'
            | 0 => fun _ _ => True
            end v q) as P'.
    change (match Sn return Type with
            | 0 => True
            | _ => P' Sn v q
            end).
    change (forall h (t : match Sn with
                          | S n' => Vector.t A' n'
                          | 0 => Vector.t A' Sn
                          end),
               P' Sn (match Sn return match Sn with
                                      | S n' => Vector.t A' n'
                                      | 0 => Vector.t A' Sn
                                      end -> Vector.t A' Sn
                      with
                      | S _ => fun t => h :: t
                      | 0 => fun t => t
                      end t) q) in H.
    clearbody P'; clear P.
    clearbody Sn.
    destruct v as [|h ? t].
    { constructor. }
    { apply H. }
  Defined.

  Fixpoint hvec_ith {n} {ifc: Vector.t Type n}
           (vec: hvec ifc) (i: Fin.t n): Vector.nth ifc i :=
    match i in Fin.t n return
          forall (ifc: Vector.t Type n),
            hvec ifc -> Vector.nth ifc i
    with
    | Fin.F1 =>
      fun ifc =>
        Vector.caseS (fun n ifc => hvec ifc -> Vector.nth ifc (@Fin.F1 n))
                     (fun h n t => fst) ifc
    | Fin.FS i' =>
      fun ifc =>
        Vector_caseS' Fin.t
                      (fun n ifc n' => hvec ifc -> Vector.nth ifc (@Fin.FS n n'))
                      (fun h n t m vec => hvec_ith (snd vec) m)
                      ifc i'
    end ifc vec.

  Fixpoint hvec_upd {n} {ifc: Vector.t Type n}
           (vec: hvec ifc) (i: Fin.t n) (v: Vector.nth ifc i): hvec ifc :=
    match i in Fin.t n return
          forall (ifc: Vector.t Type n),
            hvec ifc -> Vector.nth ifc i -> hvec ifc
    with
    | Fin.F1 =>
      fun ifc =>
        Vector.caseS (fun n ifc => hvec ifc -> Vector.nth ifc (@Fin.F1 n) -> hvec ifc)
                     (fun h n t vec v => (v, snd vec)) ifc
    | Fin.FS i' =>
      fun ifc =>
        Vector_caseS' Fin.t
                      (fun n ifc n' => hvec ifc -> Vector.nth ifc (@Fin.FS n n') -> hvec ifc)
                      (fun h n t m vec v => (fst vec, @hvec_upd _ _ (snd vec) m v))
                      ifc i'
    end ifc vec v.

End HVector.

Notation F1 := (Fin.F1).
Notation F2 := (Fin.FS Fin.F1).
Notation F3 := (Fin.FS (Fin.FS Fin.F1)).
Notation F4 := (Fin.FS (Fin.FS (Fin.FS Fin.F1))).
Notation F5 := (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))).
Notation F6 := (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))).
Notation F7 := (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))).
Notation F8 := (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))).

Declare Scope hvec_scope.
Notation "HVEC #[ I ]" := (hvec_ith HVEC I) (at level 0): hvec_scope.
Notation "HVEC +#[ I <- V ]" := (hvec_upd HVEC I V) (at level 0): hvec_scope.

Delimit Scope hvec_scope with hvec.

