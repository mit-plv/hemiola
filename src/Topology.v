Require Import Peano_dec List ListSupport.
Require Import Common FMap.

Set Implicit Arguments.

Open Scope list.

Section FindSome.
  Context {A B: Type}.
  Variable f: A -> option B.

  Fixpoint findSome (trs: list A): option B :=
    match trs with
    | nil => None
    | tr :: trs' =>
      match f tr with
      | None => findSome trs'
      | Some b => Some b
      end
    end.

End FindSome.

Section Collect.
  Context {A B: Type}.
  Variable f: A -> list B.

  Fixpoint collect (trs: list A): list B :=
    match trs with
    | nil => nil
    | tr :: trs' =>
      f tr ++ collect trs'
    end.

End Collect.

Section DTree.

  Inductive DTree :=
  | Leaf: DTree
  | Node: IdxT -> list (list IdxT (* upward edges *) *
                        list IdxT (* downward edges *) *
                        DTree (* child *)) -> DTree.

  Section DTree_ind'.
    Variable P: DTree -> Prop.
    Hypotheses (H0: P Leaf)
               (H1: forall i cs,
                   Forall (fun ic => P (snd ic)) cs ->
                   P (Node i cs)).

    Fixpoint DTree_ind' (dtr: DTree): P dtr :=
      match dtr with
      | Leaf => H0
      | Node i cs =>
        H1 i (list_ind
                (fun cs => Forall (fun ic => P (snd ic)) cs)
                (Forall_nil _)
                (fun ic _ IH =>
                   Forall_cons ic (DTree_ind' (snd ic)) IH) cs)
      end.
  End DTree_ind'.

  Definition rootOf (dtr: DTree): option IdxT :=
    match dtr with
    | Leaf => None
    | Node root _ => Some root
    end.

  Definition childrenOf (dtr: DTree): list DTree :=
    match dtr with
    | Leaf => nil
    | Node _ cs => map snd cs
    end.

  Definition childrenIndsOf (dtr: DTree): list (option IdxT) :=
    map rootOf (childrenOf dtr).

  Fixpoint parentOf (dtr: DTree) (idx: IdxT): option DTree :=
    match dtr with
    | Leaf => None
    | Node root cs =>
      if in_dec (option_dec eq_nat_dec) (Some idx)
                (map rootOf (map snd cs))
      then Some dtr
      else findSome (fun ic => parentOf (snd ic) idx) cs
    end.

  Definition childChnsOf
             (cs: list (list IdxT * list IdxT * DTree))
             (idx: IdxT):
    option (list IdxT * list IdxT * DTree) :=
    find (fun ic =>
            if option_dec eq_nat_dec (Some idx) (rootOf (snd ic))
            then true
            else false) cs.
  
  Fixpoint parentChnsOf (dtr: DTree) (idx: IdxT):
    option (list IdxT * list IdxT * IdxT (* parent index *)) :=
    match dtr with
    | Leaf => None
    | Node root cs =>
      match childChnsOf cs idx with
      | Some ic => Some (fst ic, root)
      | None => findSome (fun ic => parentChnsOf (snd ic) idx) cs
      end
    end.
  
  Fixpoint indsOf (dtr: DTree): list IdxT :=
    match dtr with
    | Leaf => nil
    | Node root cs =>
      root :: collect (fun ic => indsOf (snd ic)) cs
    end.

  Fixpoint subtree (dtr: DTree) (idx: IdxT): option DTree :=
    match dtr with
    | Leaf => None
    | Node root cs =>
      if eq_nat_dec root idx then (Some dtr)
      else findSome (fun ic => subtree (snd ic) idx) cs
    end.

  Definition upEdgesFrom (dtr: DTree) (idx: IdxT): list IdxT :=
    (parentChnsOf dtr idx)
      >>=[nil]
      (fun udp => fst (fst udp)).
         
  Definition downEdgesTo (dtr: DTree) (idx: IdxT): list IdxT :=
    (parentChnsOf dtr idx)
      >>=[nil]
      (fun udp => snd (fst udp)).

  Definition parentIdxOf (dtr: DTree) (idx: IdxT): option IdxT :=
    (parentChnsOf dtr idx)
      >>= (fun udp => Some (snd udp)).
  
End DTree.

Close Scope list.

