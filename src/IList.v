(** Borrowed from the Fiat project
 * (merged with VectorFacts.v in the same directory):
 * https://github.mit.edu/plv/fiat/blob/master/src/Common/ilist.v
 *)

Generalizable All Variables.
Set Implicit Arguments.

Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Arith.Arith.
Require Vector.

Import Vectors.VectorDef.VectorNotations.

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

Section ilist.

  (* Lists of elements whose types depend on an indexing set (CPDT's hlists).
     These lists are a convenient way to implement finite maps
     whose elements depend on their keys. The data structures used
     by our ADT notations uses these to implement notation-friendly
     method lookups.  *)

  Context {A : Type}. (* The indexing type. *)
  Context {B : A -> Type}. (* The type of indexed elements. *)

  Record prim_prod A B : Type :=
    { prim_fst : A;
      prim_snd : B }.

  Fixpoint ilist {n} (l : Vector.t A n) : Type :=
    match l with
    | [] => unit
    | a :: l => @prim_prod (B a) (ilist l)
    end.

  Definition icons
             (a : A)
             {n}
             {l : Vector.t A n}
             (b : B a)
             (il : ilist l)
    : ilist (a :: l)
    := {| prim_fst := b; prim_snd := il |}.

  Definition inil : ilist [] := tt.

  (* Get the car of an ilist. *)
  Definition ilist_hd {n} {As : Vector.t A n} (il : ilist As) :
    match As return ilist As -> Type with
    | a :: As' => fun il => B a
    | [] => fun _ => unit
    end il :=
    match As return
          forall (il : ilist As),
            match As return ilist As -> Type with
            | a :: As' => fun il => B a
            | [] => fun _ => unit
            end il with
    | a :: As => fun il => prim_fst il
    | [] => fun il => tt
    end il.

  Definition ilist_hd' {n} {As : Vector.t A (S n)} (il : ilist As) :
    B (Vector.hd As)
    := Vector.caseS (fun n As => ilist As -> B (Vector.hd As))
                    (fun a As m => ilist_hd) As il.

  (* Get the cdr of an ilist. *)
  Definition ilist_tl {n} {As : Vector.t A n} (il : ilist As) :
    match As return ilist As -> Type with
    | a :: As' => fun il => ilist As'
    | [] => fun _ => unit
    end il :=
    match As return
          forall (il : ilist As),
            match As return ilist As -> Type with
            | a :: As' => fun il => ilist As'
            | [] => fun _ => unit
            end il with
    | a :: As => fun il => prim_snd il
    | [] => fun il => tt
    end il.

  Definition ilist_tl'
             {n} {As : Vector.t A (S n)} (il : ilist As)
    : ilist (Vector.tl As) :=
    Vector.caseS (fun n As => ilist As -> ilist (Vector.tl As))
                 (fun a As m => ilist_tl) As il.

  Infix "++" := Vector.append : vector_scope.

  (* Appending ilists *)
  Fixpoint ilist_app {n} {As : Vector.t A n}
    : forall {n'} {As' : Vector.t A n'},  ilist As -> ilist As' -> ilist (As ++ As') :=
    match As return
          forall {n'} (As' : Vector.t A n'),
            ilist As -> ilist As' -> ilist (As ++ As') with
    | [] =>
      fun n' As' il il' => il'
    | a :: As'' =>
      fun n' As' il il' =>
        {| prim_fst := ilist_hd il;
           prim_snd := ilist_app (ilist_tl il) il' |}
    end.

  (* Membership in an indexed list. *)

  Inductive ilist_In {a : A} (b : B a)
    : forall {n} {As : Vector.t A n} (il : ilist As), Prop :=
  | In_hd : forall n' As' (il : ilist (n := n') As'),
      ilist_In b (icons b il)
  | In_tl : forall {n'} a' (b' : B a') As' (il : ilist (n := n') As'),
      ilist_In b il ->
      ilist_In b (icons b' il).

  (* Looking up the ith value, returning None for indices not in the Vector.t *)

  Fixpoint ith
           {m : nat}
           {As : Vector.t A m}
           (il : ilist As)
           (n : Fin.t m)
    : B (Vector.nth As n) :=
    match n in Fin.t m return
          forall (As : Vector.t A m),
            ilist As
            -> B (Vector.nth As n) with
    | Fin.F1 =>
      fun As =>
        Vector.caseS (fun n As => ilist As
                                  -> B (Vector.nth As (@Fin.F1 n)))
                     (fun h n t => ilist_hd) As
    | Fin.FS n' =>
      fun As =>
        Vector_caseS' Fin.t
                      (fun n As n' => ilist As
                                      -> B (Vector.nth As (@Fin.FS n n')))
                      (fun h n t m il => ith (ilist_tl il) m)
                      As n'
    end As il.

  Lemma ilist_invert {n} (As : Vector.t A n) (il : ilist As) :
    match As as As' return ilist As' -> Prop with
    | a :: As' => fun il => exists b il', il = icons b il'
    | [] => fun il => il = inil
    end il.
  Proof.
    destruct As; destruct il; simpl; unfold icons; eauto.
  Qed.

  Lemma ilist_invert' {n} (As : Vector.t A n) (il : ilist As) :
    match As as As' return ilist As' -> Type with
    | a :: As' => fun il => sigT (fun b => sigT (fun il' => il = icons b il'))
    | [] => fun il => il = inil
    end il.
  Proof.
    destruct As; destruct il; unfold icons; eauto.
  Qed.

(* The [ith_induction] tactic is for working with lookups of bounded indices.
     It first inducts on n, then destructs the index Vector.t [As] and eliminates
     the contradictory cases, then finally destructs any indexed Vector.t in the
     context with Bounds of [As]. *)

End ilist.

