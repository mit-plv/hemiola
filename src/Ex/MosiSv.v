Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport Syntax Semantics Topology.
Require Import RqRsLang.

Require Import Ex.Spec Ex.SpecSv Ex.Mosi.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Inductive tree: Set :=
| TLeaf: tree
| TNode: list tree -> tree.

Section Topo.

End Topo.

Section Impl.

End Impl.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

