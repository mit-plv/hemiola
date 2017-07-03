Require Import String List.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Section FnMap.
  Variables (K A: Type).
  Hypothesis (K_dec: forall (k1 k2: K), {k1 = k2} + {k1 <> k2}).

  Definition Map := K -> option A.

  Definition empty: Map := fun _ => None.

  Definition unionL (m1 m2: Map) k :=
    match m1 k with
    | Some _ => m1 k
    | None => m2 k
    end.

  Definition unionR m1 m2 := unionL m2 m1.

  Definition add (k: K) (v: A) (m: Map) :=
    fun k' =>
      match K_dec k k' with
      | left _ => Some v
      | _ => m k'
      end.

  Definition union := unionL.

  Definition disjUnion (m1 m2: Map) (d: list K) k :=
    if in_dec K_dec k d then m1 k else m2 k.

  Definition find k (m: Map) := m k.

  Definition remove k (m: Map) :=
    fun k' =>
      match K_dec k k' with
      | left _ => None
      | _ => m k'
      end.

  Definition subtract (m1 m2: Map) k :=
    match m2 k with
    | Some _ => None
    | None => m1 k
    end.

  Definition update (m1 m2: Map) := unionL m2 m1.

  Definition restrict (m: Map) (l: list K) k :=
    match in_dec K_dec k l with
    | left _ => m k
    | right _ => None
    end.

  Definition complement (m: Map) (l: list K) k :=
    match in_dec K_dec k l with
    | left _ => None
    | right _ => m k
    end.

  Definition MapsTo k v (m: Map) := m k = Some v.

  Definition InMap k (m: Map) := find k m <> None.

  Definition Equal (m1 m2: Map) := forall k, find k m1 = find k m2.

  Definition Disj (m1 m2: Map) := forall k, find k m1 = None \/ find k m2 = None.
  Definition Sub (m1 m2: Map) := forall k, InMap k m1 -> m1 k = m2 k.

  Definition InDomain (m: Map) (d: list K) := forall k, InMap k m -> In k d.
  Definition DomainOf (m: Map) (d: list K) := forall k, InMap k m <-> In k d.

  Lemma Equal_eq: forall m1 m2, Equal m1 m2 -> m1 = m2.
  Proof. intros; apply functional_extensionality; assumption. Qed.

  Lemma Equal_val: forall (m1 m2: Map) k, m1 = m2 -> m1 k = m2 k.
  Proof. intros; subst; reflexivity. Qed.
  
End FnMap.

