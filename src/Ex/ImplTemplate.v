Require Import List.
Require Import Common Index Topology Syntax.

Set Implicit Arguments.

Local Open Scope list.

Inductive tree :=
| Node: list tree -> tree.

Definition rqUpIdx: nat := 0.
Definition rsUpIdx: nat := 1.
Definition downIdx: nat := 2.

Definition singletonDNode (idx: IdxT): DTree :=
  let eidx := extendIdx 0 idx in
  DNode {| dmc_me := idx;
           dmc_ups := [extendIdx rqUpIdx idx; extendIdx rsUpIdx idx];
           dmc_downs := [extendIdx downIdx idx] |}
        [DNode {| dmc_me := eidx;
                  dmc_ups := [extendIdx rqUpIdx eidx; extendIdx rsUpIdx eidx];
                  dmc_downs := [extendIdx downIdx eidx] |} nil].

Section IncFold.
  Context {A B: Type}.
  Variable f: A -> IdxT -> B.

  Fixpoint incFold (avs: list A) (baseIdx: IdxT) (ext: nat): list B :=
    match avs with
    | nil => nil
    | av :: avs' =>
      f av (extendIdx ext baseIdx) :: incFold avs' baseIdx (S ext)
    end.

End IncFold.

Fixpoint tree2Topo (tr: tree) (curIdx: IdxT): DTree :=
  match tr with
  | Node nil => singletonDNode curIdx
  | Node ctrs =>
    DNode {| dmc_me := curIdx;
             dmc_ups := [extendIdx rqUpIdx curIdx; extendIdx rsUpIdx curIdx];
             dmc_downs := [extendIdx downIdx curIdx] |}
          (incFold tree2Topo ctrs curIdx 0)
  end.

