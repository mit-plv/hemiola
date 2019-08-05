Require Import Bool Ascii List Omega.
Require Import Common.

Local Open Scope list.

Definition IdxT := list nat.

Definition ii: IdxT := nil.
Definition natToIdx (n: nat): IdxT := n :: nil.
Coercion natToIdx: nat >-> IdxT.

Definition idx_dec: forall (idx1 idx2: IdxT), {idx1 = idx2} + {idx1 <> idx2}.
Proof.
  intros.
  decide equality.
  apply eq_nat_dec.
Defined.

Fixpoint idx_lt (idx1 idx2: IdxT): Prop :=
  match idx1 with
  | nil => match idx2 with
           | nil => False
           | _ => True
           end
  | e1 :: t1 =>
    match idx2 with
    | nil => False
    | e2 :: t2 =>
      if lt_dec e1 e2 then True
      else if lt_dec e2 e1 then False
           else idx_lt t1 t2
    end
  end.

Fixpoint idx_lt_dec (idx1 idx2: IdxT): {idx_lt idx1 idx2} + {~ idx_lt idx1 idx2}.
Proof.
  destruct idx1.
  - destruct idx2.
    + right; auto.
    + left; simpl; auto.
  - destruct idx2.
    + right; auto.
    + simpl.
      destruct (lt_dec n n0); auto.
      destruct (lt_dec n0 n); auto.
Defined.

Definition idx_total:
  forall idx1 idx2, idx1 <> idx2 -> idx_lt idx1 idx2 \/ idx_lt idx2 idx1.
Proof.
  induction idx1 as [|n1 idx1]; simpl; intros;
    [destruct idx2; [exfalso; auto|auto]|].

  destruct idx2 as [|n2 idx2]; [right; simpl; auto|].
  simpl; destruct (lt_dec n2 n1); [right; simpl; auto|].
  pose proof (Nat.lt_total n2 n1) as Ht.
  destruct Ht as [|[|]].
  - exfalso; auto.
  - subst.
    destruct (lt_dec n1 n1); [exfalso; omega|clear n0].
    apply IHidx1.
    intro Hx; subst; auto.
  - destruct (lt_dec n1 n2); auto.
Qed.

Definition idx_lt_trans:
  forall idx1 idx2 idx3: IdxT,
    idx_lt idx1 idx2 -> idx_lt idx2 idx3 -> idx_lt idx1 idx3.
Proof.
  induction idx1 as [|n1 idx1]; simpl; intros.
  - destruct idx2 as [|n2 idx2]; [exfalso; auto|].
    destruct idx3 as [|n3 idx3]; [inv H0|].
    auto.
  - destruct idx2 as [|n2 idx2]; [exfalso; auto|].
    destruct idx3 as [|n3 idx3]; [inv H0|].
    simpl in H0.
    destruct (lt_dec n1 n2).
    + destruct (lt_dec n2 n3).
      * destruct (lt_dec n1 n3); auto.
        exfalso; omega.
      * destruct (lt_dec n3 n2); [exfalso; auto|].
        destruct (lt_dec n1 n3); auto.
        exfalso; omega.
    + destruct (lt_dec n2 n3).
      * destruct (lt_dec n2 n1); [exfalso; auto|].
        destruct (lt_dec n1 n3); auto.
        exfalso; omega.
      * destruct (lt_dec n2 n1); [exfalso; auto|].
        destruct (lt_dec n3 n2); [exfalso; auto|].
        destruct (lt_dec n1 n3); auto.
        destruct (lt_dec n3 n1); [omega|].
        eapply IHidx1; eassumption.
Qed.

Definition idx_lt_not_eq:
  forall idx1 idx2: IdxT, idx_lt idx1 idx2 -> idx1 <> idx2.
Proof.
  intros.
  intro Hx; subst.
  induction idx2 as [|n2 idx2]; [inv H|].
  simpl in H.
  destruct (lt_dec n2 n2); [omega|auto].
Qed.

Definition Id (A: Type) := (IdxT * A)%type.

Definition idOf {A} (ida: Id A) := fst ida.
Definition valOf {A} (ida: Id A) := snd ida.
Definition idsOf {A} (ias: list (Id A)) := List.map fst ias.
Definition valsOf {A} (ias: list (Id A)) := List.map snd ias.

Definition liftI {A B: Type} (f: A -> B) (ida: Id A): Id B :=
  (idOf ida, f (valOf ida)).

Definition imap {A B: Type} (f: A -> B) (ias: list (Id A)): list (Id B) :=
  List.map (liftI f) ias.
Definition ifilterI {A} (ias: list (Id A)) (f: IdxT -> bool): list (Id A) :=
  filter (fun ia => f (idOf ia)) ias.
Definition ifilterV {A} (ias: list (Id A)) (f: A -> bool): list (Id A) :=
  filter (fun ia => f (valOf ia)) ias.

Definition id_dec {A} (a_dec: forall (a1 a2: A), {a1 = a2} + {a1 <> a2}):
  forall (ida1 ida2: Id A), {ida1 = ida2} + {ida1 <> ida2}.
Proof.
  intros.
  decide equality.
  apply idx_dec.
Defined.

Definition extendIdx (ext: nat) (idx: IdxT): IdxT :=
  ext :: idx.

Notation "i ~> e" :=
  (extendIdx e i) (at level 7, left associativity, format "i '~>' e").

Definition extendInds (ext: nat) (inds: list IdxT): list IdxT :=
  map (extendIdx ext) inds.

Definition liftInds (ns: list nat): list IdxT :=
  map natToIdx ns.

Definition idxHd (idx: IdxT): nat :=
  List.hd 0 idx.
Definition idxTl (idx: IdxT): IdxT :=
  List.tl idx.

Definition IdxPrefix (i1 i2: IdxT) :=
  exists ri, i2 = ri ++ i1.
Infix "~<" := IdxPrefix (at level 8).

Definition IdxDisj (i1 i2: IdxT) :=
  ~ IdxPrefix i1 i2 /\ ~ IdxPrefix i2 i1.
Infix "~*~" := IdxDisj (at level 8).

Definition IndsDisj (is1 is2: list IdxT) :=
  forall i1 i2, In i1 is1 -> In i2 is2 -> i1 ~*~ i2.

