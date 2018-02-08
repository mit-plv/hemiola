Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepDet Serial.
Require Import Synthesis TrsInv TrsSim.

Set Implicit Arguments.

(* Want:
 * 1) [AtomicRules] -> [Atomic] -> [steps_det] -> [CompAtomic].
 * 2) [CompAtomic] is compositional.
 *)

Definition DisjSys (sys1 sys2: System) :=
  DisjList (map obj_idx sys1) (map obj_idx sys2).

Definition DisjSyss (syss: list System) :=
  forall sys1 sys2,
    In sys1 syss -> In sys2 syss -> sys1 <> sys2 ->
    DisjSys sys1 sys2.

Section AtomicRules.
  
  Variable (tid: IdxT).

  Inductive AtomicRules: MsgId -> System -> Prop :=
  | ARImm:
      forall oidx oinit prec rqFrom postc valOut immr,
        immr = synImm tid oidx prec rqFrom postc valOut ->
        AtomicRules (rule_mid immr)
                    [{| obj_idx := oidx;
                        obj_state_init := oinit;
                        obj_rules := immr :: nil |}]
                    
  | ARRqRs:
      forall oidx oinit locker rqFrom fwds rqPre rsPost rsOut rqf rss syss,
        rqf = synRq tid oidx locker rqFrom fwds rqPre ->
        rss = synRss tid oidx fwds rqFrom rsPost rsOut ->
        DisjSyss syss ->
        Forall (fun systo => AtomicRules (buildMsgId tid oidx (snd systo) rqChn)
                                         (fst systo))
               (combine syss fwds) ->
        AtomicRules (rule_mid rqf)
                    ({| obj_idx := oidx;
                        obj_state_init := oinit;
                        obj_rules := rqf :: rss |}
                       :: concat syss).

End AtomicRules.

Section GTree.

  Inductive GTree :=
  | GTreeEmpty
  | GTreeNode: IdxT (* index *) ->
               bool (* growing? *) ->
               list GTree (* children *) ->
               GTree.
  
  Fixpoint elementsOf (tr: GTree): list IdxT :=
    match tr with
    | GTreeEmpty => nil
    | GTreeNode idx _ chd => idx :: (concat (map elementsOf chd))
    end.

  Definition WfGTree (tr: GTree) := NoDup (elementsOf tr).

  Definition bud (idx: IdxT) :=
    GTreeNode idx true nil.
  Definition buds (inds: list IdxT) :=
    map bud inds.

  Definition deadleaf (idx: IdxT) :=
    GTreeNode idx false nil.
  Definition deadleaves (inds: list IdxT) :=
    map deadleaf inds.

  Fixpoint isLeaf (idx: IdxT) (tr: GTree): bool :=
    match tr with
    | GTreeEmpty => false
    | GTreeNode a gr nil =>
      if a ==n idx then true else false
    | GTreeNode a gr chd =>
      if a ==n idx then false
      else
        (fix isLeafL (trs: list GTree) :=
           match trs with
           | nil => false
           | tr :: trs' => (isLeaf idx tr) || (isLeafL trs')
           end) chd
    end.

  Fixpoint sprout (to: IdxT) (inds: list IdxT) (tr: GTree): option GTree :=
    match tr with
    | GTreeEmpty => None
    | GTreeNode a gr chd =>
      if a ==n to then
        if gr then
          match chd with
          | nil => Some (GTreeNode a gr (buds inds))
          | _ => None
          end
        else None
      else
        (fix sproutL (trs: list GTree) :=
           match trs with
           | nil => None
           | tr :: trs' =>
             match sprout to inds tr with
             | Some ntr => Some ntr
             | None => sproutL trs'
             end
           end) chd
    end.

  Fixpoint prune (trs: list GTree) :=
    match trs with
    | nil => nil
    | GTreeEmpty :: trs' => prune trs'
    | tr :: trs' => tr :: prune trs'
    end.

  Fixpoint pruneIdx (idx: IdxT) (tr: GTree): option GTree :=
    match tr with
    | GTreeEmpty => None
    | GTreeNode a gr nil =>
      if a ==n idx
      then if gr then None else Some GTreeEmpty
      else None
    | GTreeNode a gr chd =>
      let ortrs := (fix pruneIdxL (trs: list GTree): option (list GTree) :=
                      match trs with
                      | nil => None
                      | tr :: trs' =>
                        match pruneIdx idx tr with
                        | Some rtr => Some (rtr :: trs')
                        | None =>
                          match pruneIdxL trs' with
                          | Some rtrs' => Some (tr :: rtrs')
                          | None => None
                          end
                        end
                      end) chd in
      match ortrs with
      | Some rtrs =>
        Some (match prune rtrs with
              | nil => GTreeNode a false nil
              | _ => GTreeNode a gr rtrs
              end)
      | None => None
      end
    end.

  Fixpoint hinder (idx: IdxT) (tr: GTree): GTree :=
    match tr with
    | GTreeEmpty => GTreeEmpty
    | GTreeNode a gr chd =>
      GTreeNode a (if a ==n idx then false else gr)
                 (map (hinder idx) chd)
    end.

  Example sprout_hinder_prune:
    match sprout 1 (2 :: nil) (bud 1) with
    | Some atr => pruneIdx 2 (hinder 2 atr)
    | None => None
    end = Some (GTreeNode 1 false nil) := eq_refl.
  
End GTree.

Definition DualMsg {MsgT} `{HasMsg MsgT} (rq rs: MsgT) :=
  mid_tid (msg_id (getMsg rq)) = mid_tid (msg_id (getMsg rs)) /\
  mid_from (msg_id (getMsg rq)) = mid_to (msg_id (getMsg rs)) /\
  mid_to (msg_id (getMsg rq)) = mid_from (msg_id (getMsg rs)).

Inductive Combined {A}: list A -> list (list A) -> Prop :=
| CombinedNil: Combined nil nil
| CombinedCons:
    forall a cmb l ll1 ll2,
      Combined cmb (ll1 ++ l :: ll2) ->
      Combined (a :: cmb) (ll1 ++ (a :: l) :: ll2).

Section CompAtomic.

  (* Thanks to [GTree], we get following properties:
   * 1) (TODO!) No external output messages are generated until the transaction
   *    ends.
   * 2) (TODO!) When the transaction ends, it outputs a single external message,
   *    which is the response of the original request.
   * 3) When the transaction ends, no internal messages about the transaction 
   *    are left. We ensure this by checking if the [GTree] is empty in 
   *    [CAtomicDone].
   *)

  (** Wants (informally):
   * 1) [AtomicRules sys] -> [Atomic hst] -> [steps_det hst] ->
   *    [CompAtomic sys (rqin.to :: nil) hst].
   * 2) [CompAtomic] is compositional.
   *)

  Inductive CompAtomic:
    GTree ->
    History (* head is the _oldest_; 
             * reverse of a history defined in [steps]. *) ->
    GTree ->
    Prop :=
  | CAtomicNil:
      forall tid, CompAtomic (bud tid) nil (bud tid)
  | CAtomicImm:
      forall tid rqin rsout,
        tid = mid_to (msg_id (tmsg_msg rqin)) ->
        DualMsg rqin rsout ->
        CompAtomic (bud tid)
                   (IlblOuts (Some rqin) (rsout :: nil) :: nil)
                   (deadleaf tid)
  | CAtomicRqF:
      forall tid fwds rqin rqfwds hst ltr,
        tid = mid_to (msg_id (tmsg_msg rqin)) ->
        fwds = map (fun tmsg => mid_to (msg_id (tmsg_msg tmsg))) rqfwds ->
        CompAtomic (GTreeNode tid true (buds fwds)) hst ltr ->
        CompAtomic (bud tid) (IlblOuts (Some rqin) rqfwds :: hst) ltr
  | CAtomicRqCont:
      forall tid fwds shsts rqhst rqtrs hst ltr,
        Forall (fun tht => CompAtomic (bud (fst (fst tht)))
                                      (snd (fst tht))
                                      (snd tht))
               (combine (combine fwds shsts) rqtrs) ->
        CompAtomic (GTreeNode tid true rqtrs) hst ltr ->
        Combined rqhst shsts ->
        CompAtomic (GTreeNode tid true (buds fwds)) (rqhst ++ hst) ltr.
  (* | CAtomicRsB: *)
  (*     forall tid, *)
  (*       CompAtomic (GTreeNode tid true (deadleaves rss)) *)
  (*                  (IlblOuts (rss) (rsout :: nil) :: nil) *)
  (*                  (deadleaf tid). *)

  (** TODO: add the concept of external invariants, pre/postconditions 
   * to [CompAtomic]. *)

End CompAtomic.

Section Compositionality.

End Compositionality.

