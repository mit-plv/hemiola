Require Import Peano_dec List ListSupport.
Require Import Common FMap.

Set Implicit Arguments.

Section Tree.
  Variable (t: Type).

  Inductive Tree :=
  | Node: IdxT -> t -> list Tree -> Tree.

  Fixpoint trIndicesOf (tr: Tree) :=
    match tr with
    | Node i _ chd => i :: concat (map trIndicesOf chd)
    end.

  Definition trCurIdxOf (tr: Tree) :=
    match tr with
    | Node i _ _ => i
    end.

  Definition trValueOf (tr: Tree) :=
    match tr with
    | Node _ v _ => v
    end.

  Definition trChildrenOf (tr: Tree) :=
    match tr with
    | Node _ _ chd => chd
    end.

  Definition WfTree (tr: Tree) := NoDup (trIndicesOf tr).

  Fixpoint trIterate (f: Tree -> bool) (tr: Tree) :=
    if f tr
    then Some tr
    else match tr with
         | Node i v chd =>
           (fix trIterateL (trs: list Tree) :=
              match trs with
              | nil => None
              | tr :: trs' =>
                if f tr then Some tr else trIterateL trs'
              end) chd
         end.

  Fixpoint getThis (tr: Tree) (idx: IdxT): option Tree :=
    trIterate (fun tr =>
                 if trCurIdxOf tr ==n idx
                 then true else false) tr.

  Fixpoint getParent (tr: Tree) (idx: IdxT): option Tree :=
    trIterate (fun tr =>
                 if idx ?<n (map trCurIdxOf (trChildrenOf tr))
                 then true else false) tr.

  Definition getParentFwds (tr: Tree) (this: IdxT): list (IdxT * list IdxT) :=
    match getThis tr this with
    | Some ttr =>
      match getParent tr this with
      | Some ptr => (trCurIdxOf ptr, removeL eq_nat_dec (trIndicesOf tr) (trIndicesOf ttr)) :: nil
      | None => nil
      end
    | None => nil
    end.

  Definition getChildrenFwds (tr: Tree) (fch this: IdxT): list (IdxT * list IdxT) :=
    match getThis tr this with
    | Some ttr =>
      match ttr with
      | Node _ _ chd =>
        filter (fun ii => if fst ii ==n fch then false else true)
               (map (fun tr => (trCurIdxOf tr, trIndicesOf tr)) chd)
      end
    | None => nil
    end.

  Definition getFwds (tr: Tree) (fch this: IdxT): list (IdxT * list IdxT) :=
    getParentFwds tr this ++ getChildrenFwds tr fch this.

End Tree.

