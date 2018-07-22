Require Import Bool Ascii String List Eqdep Omega.

Require Export ProofIrrelevance.

Definition option_dec {A}
           (eq_dec: forall a1 a2: A, {a1 = a2} + {a1 <> a2}):
  forall oa1 oa2: option A, {oa1 = oa2} + {oa1 <> oa2}.
Proof.
  decide equality.
Defined.

Definition IdxT := nat.

Definition Id (A: Type) := (IdxT * A)%type.

Definition idOf {A} (ida: Id A) := fst ida.
Definition valOf {A} (ida: Id A) := snd ida.
Definition idsOf {A} (ias: list (Id A)) := map fst ias.
Definition valsOf {A} (ias: list (Id A)) := map snd ias.

Definition liftI {A B: Type} (f: A -> B) (ida: Id A): Id B :=
  (idOf ida, f (valOf ida)).

Definition imap {A B: Type} (f: A -> B) (ias: list (Id A)): list (Id B) :=
  map (liftI f) ias.
Definition ifilterI {A} (ias: list (Id A)) (f: IdxT -> bool): list (Id A) :=
  filter (fun ia => f (idOf ia)) ias.
Definition ifilterV {A} (ias: list (Id A)) (f: A -> bool): list (Id A) :=
  filter (fun ia => f (valOf ia)) ias.

Definition id_dec {A} (a_dec: forall (a1 a2: A), {a1 = a2} + {a1 <> a2}):
  forall (ida1 ida2: Id A), {ida1 = ida2} + {ida1 <> ida2}.
Proof.
  intros.
  decide equality.
  apply eq_nat_dec.
Defined.

Notation "[ ]" := nil (format "[ ]").
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Theorem tautology_0:
  forall (P Q: Prop), (P -> Q) -> P -> Q.
Proof.
  tauto.
Qed.

Ltac nothing := idtac.

Ltac assert_later asrt :=
  apply tautology_0 with (P:= asrt); [intros|].

Ltac inv H := inversion H; subst; clear H.
Ltac dest :=
  repeat (match goal with
            | H: _ /\ _ |- _ => destruct H
            | H: exists _, _ |- _ => destruct H
          end).
Ltac dest_in :=
  repeat
    match goal with
    | [H: In _ _ |- _] => inv H
    end.
Ltac find_if_inside :=
  match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
    | [ H : context[if ?X then _ else _] |- _ ]=> destruct X
  end.

Ltac is_equal t1 t2 :=
  let Heq := fresh "Heq" in
  assert (Heq: t1 = t2) by reflexivity;
  clear Heq.

Ltac is_pure_const t :=
  tryif is_var t
  then fail
  else lazymatch t with
       | ?t1 ?t2 =>
         tryif is_pure_const t1
         then is_pure_const t2 else fail
       | _ => idtac
       end.

Ltac not_pure_const t :=
  tryif is_var t
  then idtac
  else lazymatch t with
       | ?t1 ?t2 =>
         tryif not_pure_const t1
         then idtac else not_pure_const t2
       | _ => fail
       end.

Ltac collect_of_type_helper ty ls :=
  match goal with
  | [v: ty |- _]
    => lazymatch ls with
       | context[cons v _] => fail
       | _ => collect_of_type_helper ty (cons v ls)
       end
  | _ => ls
  end.
Ltac collect_of_type ty := collect_of_type_helper ty (@nil ty).

Infix "==n" := eq_nat_dec (at level 30).
Infix "<=n" := le_dec (at level 30).
Infix "<n" := lt_dec (at level 30).
Infix ">=n" := ge_dec (at level 30).
Infix ">n" := gt_dec (at level 30).
Infix "?<n" := (in_dec eq_nat_dec) (at level 30).

Definition bind {A B} (oa: option A) (f: A -> option B): option B :=
  match oa with
  | Some a => f a
  | None => None
  end.
Infix ">>=" := bind (at level 0).

Definition lift {A B} (f: A -> B): option A -> option B :=
  fun oa =>
    match oa with
    | Some a => Some (f a)
    | None => None
    end.

Lemma lift_hd_error:
  forall {A B} (f: A -> B) (l: list A),
    lift f (hd_error l) = hd_error (map f l).
Proof.
  induction l; simpl; intros; auto.
Qed.

Definition tbind {A B} (nb: B) (oa: option A) (f: A -> B): B :=
  match oa with
  | Some a => f a
  | None => nb
  end.
Notation "OA >>=[ NB ] F" :=
  (tbind NB OA F) (at level 0, format "OA  '>>=[' NB ] '/' F").

Fixpoint replicate {A} (a: A) (sz: nat): list A :=
  match sz with
  | O => nil
  | S sz' => a :: replicate a sz'
  end.

Definition trues (sz: nat) := replicate true sz.
Definition falses (sz: nat) := replicate false sz.

Fixpoint findAt (v: nat) (l: list nat) :=
  match l with
  | nil => None
  | n :: l' =>
    if v ==n n then Some O
    else (findAt v l') >>=[None] (fun o => Some (S o))
  end.

Axiom cheat: forall t, t.

