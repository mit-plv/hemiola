Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport Syntax Semantics Topology.
Require Import RqRsTopo RqRsLang.

Require Import Spec SpecSv Mosi.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Inductive tree: Set :=
| TLeaf: tree
| TNode: list tree -> tree.

Section Topo.

  Fixpoint topoFromTree (curIdx: IdxT) (tr: tree): (DTree * IdxT) :=
    match tr with
    | TLeaf => (leaf curIdx
                     [3 * (S curIdx); 3 * (S curIdx) + 1]
                     [3 * (S curIdx) + 2]
                     (S curIdx), curIdx + 2)
    | TNode strs =>
      let (dstrs, nextIdx) :=
          List.fold_left
            (fun (acc: (list (list IdxT * list IdxT * DTree) * IdxT)) str =>
               let (adstrs, anextIdx) := acc in
               let (ndstr, nnextIdx) := topoFromTree anextIdx str in
               (adstrs ++ [([3 * anextIdx; 3 * anextIdx + 1],
                            [3 * anextIdx + 2],
                            ndstr)], nnextIdx))
            strs (nil, S curIdx) in
      (Node curIdx dstrs, nextIdx)
    end.

  (* Definition tester := *)
  (*   fst (topoFromTree 0 (TNode [TLeaf; TLeaf; TLeaf])). *)

  (* Lemma tester_wf: WfDTree tester. *)
  (* Proof. *)
  (*   split. *)
  (*   - compute; repeat constructor; firstorder. *)
  (*   - compute; repeat constructor; firstorder. *)
  (* Qed. *)

  (* Lemma tester_RqRsChnsOnDTree: RqRsChnsOnDTree tester. *)
  (* Proof. *)
  (*   red; intros. *)
  (*   pose proof (parentChnsOf_Some_in_tree tester_wf _ _ H). *)
  (*   dest_in; try (inv H; eauto). *)
  (* Qed. *)

End Topo.

Section Impl.

End Impl.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

