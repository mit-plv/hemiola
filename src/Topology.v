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

  Fixpoint indsOf (dtr: DTree): list IdxT :=
    match dtr with
    | Leaf => nil
    | Node root cs =>
      root :: collect (fun ic => indsOf (snd ic)) cs
    end.

  Fixpoint chnsOf (dtr: DTree): list IdxT :=
    match dtr with
    | Leaf => nil
    | Node _ cs =>
      (concat (map (fun ic => fst (fst ic)) cs))
        ++ (concat (map (fun ic => snd (fst ic)) cs))
        ++ collect (fun ic => chnsOf (snd ic)) cs
    end.

  Fixpoint subtree (dtr: DTree) (idx: IdxT): option DTree :=
    match dtr with
    | Leaf => None
    | Node root cs =>
      if eq_nat_dec root idx then (Some dtr)
      else findSome (fun ic => subtree (snd ic) idx) cs
    end.

  Definition subtreeIndsOf (dtr: DTree) (idx: IdxT): list IdxT :=
    (subtree dtr idx) >>=[nil] (fun tr => indsOf tr).

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

  (** Well-formedness *)

  Definition UniqueInds (dtr: DTree): Prop :=
    NoDup (indsOf dtr).

  Definition UniqueChns (dtr: DTree): Prop :=
    NoDup (chnsOf dtr).

  Definition WfDTree (dtr: DTree): Prop :=
    UniqueInds dtr /\
    UniqueChns dtr.
  
End DTree.

Section Facts.
  Variable dtr: DTree.
  Hypothesis Hwf: WfDTree dtr.
  
  Lemma parentIdxOf_not_eq:
    forall idx pidx,
      parentIdxOf dtr idx = Some pidx ->
      idx <> pidx.
  Proof.
  Admitted.
  
  Lemma parentChnsOf_NoDup:
    forall idx ups downs pidx,
      parentChnsOf dtr idx = Some (ups, downs, pidx) ->
      NoDup (ups ++ downs).
  Proof.
  Admitted.

  Lemma parentChnsOf_DisjList:
    forall idx1 ups1 downs1 pidx1 idx2 ups2 downs2 pidx2,
      idx1 <> idx2 ->
      parentChnsOf dtr idx1 = Some (ups1, downs1, pidx1) ->
      parentChnsOf dtr idx2 = Some (ups2, downs2, pidx2) ->
      DisjList (ups1 ++ downs1) (ups2 ++ downs2).
  Proof.
  Admitted.

  Lemma subtreeIndsOf_composed:
    forall oidx roidx,
      In oidx (subtreeIndsOf dtr roidx) ->
      oidx = roidx \/
      (exists cidx,
          parentIdxOf dtr cidx = Some roidx /\
          In oidx (subtreeIndsOf dtr cidx)).
  Proof.
  Admitted.

  Lemma parentChnsOf_subtreeIndsOf_self_in:
    forall oidx,
      parentChnsOf dtr oidx <> None ->
      In oidx (subtreeIndsOf dtr oidx).
  Proof.
  Admitted.

  Lemma parent_not_in_subtree:
    forall oidx pidx,
      parentIdxOf dtr oidx = Some pidx ->
      ~ In pidx (subtreeIndsOf dtr oidx).
  Proof.
  Admitted.

  Lemma inside_parent_out:
    forall cidx pidx oidx poidx,
      parentIdxOf dtr cidx = Some pidx ->
      In oidx (subtreeIndsOf dtr cidx) ->
      parentIdxOf dtr oidx = Some poidx ->
      In poidx (pidx :: subtreeIndsOf dtr cidx).
  Proof.
  Admitted.
  
  Lemma inside_child_in:
    forall cidx pidx oidx coidx,
      parentIdxOf dtr cidx = Some pidx ->
      In oidx (subtreeIndsOf dtr cidx) ->
      parentIdxOf dtr coidx = Some oidx ->
      In coidx (subtreeIndsOf dtr cidx).
  Proof.
  Admitted.

  Lemma outside_parent_out:
    forall oidx cidx pidx,
      ~ In cidx (subtreeIndsOf dtr oidx) ->
      parentIdxOf dtr cidx = Some pidx ->
      ~ In pidx (subtreeIndsOf dtr oidx).
  Proof.
  Admitted.

  Lemma outside_child_in:
    forall oidx cidx pidx,
      ~ In pidx (subtreeIndsOf dtr oidx) ->
      parentIdxOf dtr cidx = Some pidx ->
      cidx = oidx \/ ~ In cidx (subtreeIndsOf dtr oidx).
  Proof.
  Admitted.

End Facts.

Close Scope list.

