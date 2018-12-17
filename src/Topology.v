Require Import Peano_dec List ListSupport.
Require Import Common FMap.

Set Implicit Arguments.

Open Scope list.

Section Digraph.
  Variables (ChnT: Set)
            (chn_dec: forall c1 c2: ChnT, {c1 = c2} + {c1 <> c2}).
  
  (* NOTE: each object or queue is represented as a vertex. *)
  Definition vertices := list IdxT.

  (* NOTE: each channel id ([edge_chn]) should be unique through the entire graph.
   * See [WfDigraph] below for details. *)
  Record edge :=
    { edge_from: option IdxT;
      edge_chn: ChnT;
      edge_to: option IdxT
    }.

  Definition createEdge (v1: IdxT) (c: ChnT) (v2: IdxT) :=
    Build_edge (Some v1) c (Some v2).
  
  Definition edge_dec: forall e1 e2:edge, {e1 = e2} + {e1 <> e2}.
  Proof.
    decide equality.
    - apply (option_dec eq_nat_dec).
    - apply (option_dec eq_nat_dec).
  Defined.

  Definition edge_eq (e1 e2: edge): bool :=
    if edge_dec e1 e2 then true else false.
  
  Definition edges := list edge.

  Record digraph :=
    { dg_vs: vertices;
      dg_es: edges
    }.

  Definition emptyDigraph :=
    {| dg_vs := nil; dg_es := nil |}.
  
  Definition WfDigraph (dg: digraph) :=
    NoDup (dg_vs dg) /\
    NoDup (map edge_chn (dg_es dg)).

  Definition singleton (v: IdxT) :=
    {| dg_vs := [v]; dg_es := nil |}.
  
  Definition connect (dg1: digraph) (ces: edges) (dg2: digraph) :=
    {| dg_vs := dg_vs dg1 ++ dg_vs dg2;
       dg_es := dg_es dg1 ++ dg_es dg2 ++ ces |}.

  Fixpoint connectMany (dg: digraph) (conns: list (edges * digraph)) :=
    match conns with
    | nil => dg
    | conn :: conns' =>
      connectMany (connect dg (fst conn) (snd conn)) conns'
    end.

  Definition isEdgeOf (e: edge) (from to: option IdxT) :=
    if option_dec eq_nat_dec (edge_from e) from
    then if option_dec eq_nat_dec (edge_to e) to
         then true
         else false
    else false.

  Definition edgesOf (di: digraph) (from to: option IdxT) :=
    filter (fun e => isEdgeOf e from to) (dg_es di).

End Digraph.

Section DTree.

  Inductive DTree :=
  | Leaf: DTree
  | Node: IdxT -> list ((list IdxT (* upward edges *) *
                         list IdxT (* downward edges *)) *
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

  Section FindNonLeaf.
    Context {A: Type}.
    Variable f: A -> DTree.

    Fixpoint findNonLeaf (trs: list A): DTree :=
      match trs with
      | nil => Leaf
      | tr :: trs' =>
        match f tr with
        | Leaf => findNonLeaf trs'
        | _ => f tr
        end
      end.

  End FindNonLeaf.
  
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
  
  Fixpoint subtree (dtr: DTree) (idx: IdxT): DTree :=
    match dtr with
    | Leaf => Leaf
    | Node root cs =>
      if eq_nat_dec root idx then dtr
      else findNonLeaf (fun ic => subtree (snd ic) idx) cs
    end.

  Inductive CDir := CUp | CDown.
  Definition DChn := (CDir * nat * IdxT)%type.

  Definition dchn_dec: forall c1 c2: DChn, {c1 = c2} + {c1 <> c2}.
  Proof.
    repeat decide equality.
  Defined.

  Fixpoint edgesUp (pidx: IdxT) (cidx: option IdxT) 
           (ups: list IdxT) (i: nat): list (edge DChn) :=
    match ups with
    | nil => nil
    | up :: ups' =>
      (Build_edge cidx (CUp, i, up) (Some pidx))
        :: edgesUp pidx cidx ups' (S i)
    end.

  Fixpoint edgesDown (pidx: IdxT) (cidx: option IdxT) 
           (downs: list IdxT) (i: nat): list (edge DChn) :=
    match downs with
    | nil => nil
    | down :: downs' =>
      (Build_edge cidx (CDown, i, down) (Some pidx))
        :: edgesDown pidx cidx downs' (S i)
    end.

  Definition edgesUpDowns (pidx: IdxT) (cidx: option IdxT)
             (updowns: (list IdxT * list IdxT)): list (edge DChn) :=
    (edgesUp pidx cidx (fst updowns) O)
      ++ (edgesDown pidx cidx (snd updowns) O).
  
  Fixpoint topoOfT (dtr: DTree): digraph DChn :=
    match dtr with
    | Leaf => emptyDigraph DChn
    | Node root cs =>
      connectMany
        (singleton DChn root)
        (map (fun eec =>
                (edgesUpDowns root (rootOf (snd eec)) (fst eec),
                 topoOfT (snd eec))) cs)
    end.

  Variable (dtr: DTree).

  Local Notation topo := (topoOfT dtr).

  Definition EdgeIn (e: edge DChn) :=
    In e (dg_es topo).

  Definition findEdge (cidx: IdxT): option (edge DChn) :=
    find (fun e => snd e.(edge_chn) ==n cidx) (dg_es topo).

  Definition upEdges: list (edge DChn) :=
    filter (fun e =>
              match fst (fst (e.(edge_chn))) with
              | CUp => true
              | CDown => false
              end) (dg_es topo).

  Definition downEdges: list (edge DChn) :=
    filter (fun e =>
              match fst (fst (e.(edge_chn))) with
              | CUp => false
              | CDown => true
              end) (dg_es topo).

  Definition parentOf (idx: IdxT): option IdxT :=
    (find (fun e =>
             match e.(edge_from) with
             | Some from => from ==n idx
             | None => false
             end) upEdges)
      >>= (fun ue => ue.(edge_to)).
  
  Definition isUpEdge (e: edge DChn) :=
    match fst (fst e.(edge_chn)) with
    | CUp => true
    | CDown => false
    end.

  Definition isDownEdge (e: edge DChn) :=
    match fst (fst e.(edge_chn)) with
    | CUp => false
    | CDown => true
    end.

  Definition idxUpEdge (cidx: IdxT) :=
    (findEdge cidx) >>=[false] (fun e => isUpEdge e).
                
  Definition idxDownEdge (cidx: IdxT) :=
    (findEdge cidx) >>=[false] (fun e => isDownEdge e).
  
  Definition upEdgesFrom (oidx: IdxT) :=
    filter (fun e =>
              if option_dec eq_nat_dec e.(edge_from) (Some oidx)
              then isUpEdge e
              else false) (dg_es topo).

  Definition upEdgesTo (oidx: IdxT) :=
    filter (fun e =>
              if option_dec eq_nat_dec e.(edge_to) (Some oidx)
              then isUpEdge e
              else false) (dg_es topo).

  Definition downEdgesFrom (oidx: IdxT) :=
    filter (fun e =>
              if option_dec eq_nat_dec e.(edge_from) (Some oidx)
              then isDownEdge e
              else false) (dg_es topo).

  Definition downEdgesTo (oidx: IdxT) :=
    filter (fun e =>
              if option_dec eq_nat_dec e.(edge_to) (Some oidx)
              then isDownEdge e
              else false) (dg_es topo).
  
End DTree.

Close Scope list.

