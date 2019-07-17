Require Import List.
Require Import Common Index Topology Syntax.

Set Implicit Arguments.

Local Open Scope list.

Inductive tree :=
| Node: list tree -> tree.

Definition rqUpIdx: nat := 0.
Definition rsUpIdx: nat := 1.
Definition downIdx: nat := 2.

Section IncMap.
  Context {A B: Type}.
  Variable f: A -> IdxT -> B.

  Fixpoint incMap (avs: list A) (baseIdx: IdxT) (ext: nat): list B :=
    match avs with
    | nil => nil
    | av :: avs' =>
      f av (baseIdx~>ext) :: incMap avs' baseIdx (S ext)
    end.

End IncMap.

Record CIfc :=
  { c_indices: list IdxT;
    c_minds: list IdxT;
    c_merqs: list IdxT;
    c_merss: list IdxT
  }.

Definition emptyCIfc :=
  {| c_indices := nil; c_minds := nil;
     c_merqs := nil; c_merss := nil |}.

Definition mergeCIfc (ci1 ci2: CIfc) :=
  {| c_indices := ci1.(c_indices) ++ ci2.(c_indices);
     c_minds := ci1.(c_minds) ++ ci2.(c_minds);
     c_merqs := ci1.(c_merqs) ++ ci2.(c_merqs);
     c_merss := ci1.(c_merss) ++ ci2.(c_merss) |}.

Definition singletonDNode (idx: IdxT): DTree * CIfc :=
  let eidx := idx~>0 in
  (DNode {| dmc_me := idx;
            dmc_ups := [idx~>rqUpIdx; idx~>rsUpIdx];
            dmc_downs := [idx~>downIdx] |}
         [DNode {| dmc_me := eidx;
                   dmc_ups := [eidx~>rqUpIdx; eidx~>rsUpIdx];
                   dmc_downs := [eidx~>downIdx] |} nil],
   {| c_indices := [idx];
      c_minds := [idx~>rqUpIdx; idx~>rsUpIdx; idx~>downIdx];
      c_merqs := [eidx~>rqUpIdx];
      c_merss := [eidx~>downIdx] |}).
      
Fixpoint tree2Topo (tr: tree) (curIdx: IdxT): DTree * CIfc :=
  match tr with
  | Node nil => singletonDNode curIdx
  | Node ctrs =>
    let stp := incMap tree2Topo ctrs curIdx 0 in
    let strs := map fst stp in
    let sci := fold_left mergeCIfc (map snd stp) emptyCIfc in
    (DNode {| dmc_me := curIdx;
              dmc_ups := [curIdx~>rqUpIdx; curIdx~>rsUpIdx];
              dmc_downs := [curIdx~>downIdx] |} strs,
     mergeCIfc
       {| c_indices := [curIdx];
          c_minds := [curIdx~>rqUpIdx; curIdx~>rsUpIdx; curIdx~>downIdx];
          c_merqs := nil;
          c_merss := nil |}
       sci)
  end.

(* Eval compute in (tree2Topo (Node [Node nil; Node nil]) 0). *)

