Require Import Peano_dec List ListSupport.
Require Import Common FMap.

Set Implicit Arguments.

(** Tree structure with (possibly-)multiple channels between nodes. *)
Section CTree.
  Variable (t: Type).

  Record Channel :=
    { chn_up: list IdxT;
      chn_down: list IdxT
    }.

  Inductive CTree :=
  | CNode: IdxT -> t -> list (Channel * CTree) -> CTree.

  Fixpoint trOIndsOf (tr: CTree) :=
    match tr with
    | CNode i _ chd =>
      i :: concat (map (fun cc => trOIndsOf (snd cc)) chd)
    end.

  Definition trCurOIdxOf (tr: CTree) :=
    match tr with
    | CNode i _ _ => i
    end.

  Definition trValueOf (tr: CTree) :=
    match tr with
    | CNode _ v _ => v
    end.

  Definition trChildrenOf (tr: CTree) :=
    match tr with
    | CNode _ _ chd => map snd chd
    end.

  Definition CTreeWfOInds (tr: CTree) := NoDup (trOIndsOf tr).

  Fixpoint trIterate (f: CTree -> bool) (tr: CTree) :=
    if f tr
    then Some tr
    else match tr with
         | CNode i v chd =>
           (fix trIterateL (trs: list CTree) :=
              match trs with
              | nil => None
              | tr :: trs' =>
                if f tr then Some tr else trIterateL trs'
              end) (map snd chd)
         end.

  Fixpoint getThis (tr: CTree) (idx: IdxT): option CTree :=
    trIterate (fun tr =>
                 if trCurOIdxOf tr ==n idx
                 then true else false) tr.

  Fixpoint getParent (tr: CTree) (idx: IdxT): option CTree :=
    trIterate (fun tr =>
                 if idx ?<n (map trCurOIdxOf (trChildrenOf tr))
                 then true else false) tr.

  Definition getParentFwds (tr: CTree) (this: IdxT): list (IdxT * list IdxT) :=
    match getThis tr this with
    | Some ttr =>
      match getParent tr this with
      | Some ptr => (trCurOIdxOf ptr, removeL eq_nat_dec (trOIndsOf tr) (trOIndsOf ttr)) :: nil
      | None => nil
      end
    | None => nil
    end.

  Definition getChildrenFwds (tr: CTree) (fch this: IdxT): list (IdxT * list IdxT) :=
    match getThis tr this with
    | Some ttr =>
      match ttr with
      | CNode _ _ chd =>
        filter (fun ii => if fst ii ==n fch then false else true)
               (map (fun cc => (trCurOIdxOf (snd cc), trOIndsOf (snd cc))) chd)
      end
    | None => nil
    end.

  Definition getFwds (tr: CTree) (fch this: IdxT): list (IdxT * list IdxT) :=
    getParentFwds tr this ++ getChildrenFwds tr fch this.

  Definition fromParent (tr: CTree) (this: IdxT): list IdxT := cheat _.
  Definition isFromParent (tr: CTree) (this: IdxT) (midx: IdxT): bool := cheat _.
  Definition fromChildren (tr: CTree) (this: IdxT): list IdxT := cheat _.
  Definition isFromChild (tr: CTree) (this: IdxT) (midx: IdxT): bool := cheat _.

End CTree.

