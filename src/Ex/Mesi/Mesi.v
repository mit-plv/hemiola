Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector IndexSupport Syntax Semantics.
Require Import Topology RqRsTopo.
Require Import RqRsLang. Import RqRsNotations.

Require Import Ex.Spec Ex.SpecSv Ex.Template Ex.Mesi.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

(** Design choices:
 * - Multi-level (for arbitrary tree structure)
 * - MESI
 * - Directory (not snooping)
 * - Invalidate (not update)
 * - Write-back (not write-through)
 *)

(* - Distinguishing I (Invalid) and NP (Not Present):
 *     It is _not_ required to distinguish an invalid line and a non-presented
 *   line if a protocol never employes the invalid value. However, in a MESI
 *   protocol, especially if the protocol is non-inclusive, the two lines should
 *   be distinguished. For instance, when an L2 cache has a summary status of E
 *   but has its own status of I, it needs to know if it still has the (clean) 
 *   line so it updates its status appropriately when the exclusive child evicts
 *   the line (without write-back).
 *)

(* - Non-inclusive caches and ownership bits:
 *     In order to implement non-inclusive caches, each cache line has an
 *   "ownership" bit, whether this line is responsible for write-back. For
 *   example, an L2 cache and its children could have a dirty data if one of the
 *   children has the M status. They "still" have the "dirty" data after sharing
 *   it, i.e., when the L2 cache and some of the children get S. Now at the time
 *   the L2 wants to evict this dirty data, even if its status is S it needs to
 *   know the data is dirty or not (if dirty, must written back to its parent).
 *   The ownership bit of the L2 is, in this case, true so it knows that the
 *   data should be written back.
 *     For a typical MSI protocol, there always exists a unique owner in the
 *   entire memory subsystem so it's pretty easy to maintain the ownership.
 *   However, for a MESI protocol, we have an exceptional case when a line with
 *   the Exclusive (E) status silently goes to M. In this case we have two
 *   owners, the "origin" cache that previously had M and the new cache that
 *   just got M (from E). But at this moment the origin cache has an Invalid (I)
 *   data, thus write-back has no meaning.
 *     For simplicity we decided _not_ to allow any evictions of such data 
 *   (owned but invalid). We could design a protocol which allows such cases,
 *   but this optimization requires so many sophisticated corner cases, e.g.,
 *   request-from-the-exclusive-cache.
 *
 * - A further remark about write-back: there can be 4 (= 2*2) writeback types,
 *   based on whether 1) it is an invaliation or not and 2) it writes the dirty
 *   data back. (1) happens when a cache has data and its directory status is I.
 *   (2) happens when a cache has dirty data.
 *     Both a child and the parent should be able to distinguish four writeback
 *   types so they can do state transitions appropriately. For example, let's
 *   say an L1 cache previously had the E status and silently changed its status
 *   to M to make the cache line dirty. When this line is evicted, the parent
 *   (L2) has no idea whether it needs to update the line. In this case the
 *   child (L1) should send the dirty data with an appropriate message id, in
 *   order for the parent to recognize the update is required.
 *)

Section System.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo := fst (tree2Topo tr 0).
  Let cifc := snd (tree2Topo tr 0).

  Definition val: Fin.t 4 := F1.
  Definition owned: Fin.t 4 := F2.
  Definition status: Fin.t 4 := F3.
  Definition dir: Fin.t 4 := F4.

  Section Directory.
    
    Record DirT: Set :=
      { dir_st: MESI; (* the summary status of children *)
        dir_excl: IdxT;
        dir_sharers: list IdxT
      }.

    Definition dirInit: DirT :=
      {| dir_st := mesiI;
         dir_excl := ii;
         dir_sharers := nil |}.

    Import CaseNotations.
    Definition getDir (oidx: IdxT) (dir: DirT): MESI :=
      match case dir.(dir_st) on eq_nat_dec default mesiI with
      | mesiM: if idx_dec oidx dir.(dir_excl) then mesiM else mesiI
      | mesiE: if idx_dec oidx dir.(dir_excl) then mesiE else mesiI
      | mesiS: if in_dec idx_dec oidx dir.(dir_sharers)
               then mesiS else mesiI
      | mesiI: mesiI
      end.

    Definition setDirM (oidx: IdxT) :=
      {| dir_st := mesiM;
         dir_excl := oidx;
         dir_sharers := nil |}.

    Definition setDirE (oidx: IdxT) :=
      {| dir_st := mesiE;
         dir_excl := oidx;
         dir_sharers := nil |}.

    Definition setDirS (oinds: list IdxT) :=
      {| dir_st := mesiS;
         dir_excl := 0;
         dir_sharers := oinds |}.
    
    Definition setDirI :=
      {| dir_st := mesiI;
         dir_excl := 0;
         dir_sharers := nil |}.

    Definition addSharer (oidx: IdxT) (dir: DirT): DirT :=
      {| dir_st := dir.(dir_st);
         dir_excl := dir.(dir_excl);
         dir_sharers := oidx :: dir.(dir_sharers) |}.

    Definition removeSharer (oidx: IdxT) (dir: DirT): DirT :=
      {| dir_st := dir.(dir_st);
         dir_excl := dir.(dir_excl);
         dir_sharers := removeOnce idx_dec oidx dir.(dir_sharers) |}.

    Definition LastSharer (dir: DirT) (cidx: IdxT) :=
      dir.(dir_sharers) = [cidx].

    Definition NotLastSharer (dir: DirT) :=
      2 <= List.length dir.(dir_sharers).

  End Directory.

  Instance ImplOStateIfc: OStateIfc :=
    {| ost_ty := [nat:Type; bool:Type; MESI:Type; DirT:Type]%vector |}.

  Definition implOStateInit: OState :=
    (0, (false, (mesiNP, (dirInit, tt)))).

  Definition implOStateInitRoot: OState :=
    (0, (true, (mesiM, (dirInit, tt)))).

  Definition implOStatesInit: OStates :=
    (fold_right (fun i m => m +[i <- implOStateInit]) []
                (tl cifc.(c_li_indices) ++ cifc.(c_l1_indices)))
    +[rootOf topo <- implOStateInitRoot].

  Lemma implOStatesInit_value_non_root:
    forall oidx,
      In oidx (tl (c_li_indices cifc) ++ c_l1_indices cifc) ->
      implOStatesInit@[oidx] = Some implOStateInit.
  Proof.
    intros; unfold implOStatesInit; fold cifc.
    assert (~ In (rootOf topo) (tl (c_li_indices cifc) ++ c_l1_indices cifc)).
    { pose proof (c_li_indices_head_rootOf 0 Htr).
      pose proof (tree2Topo_WfCIfc tr 0); destruct H1 as [? _].
      rewrite H0 in H1; inv H1; assumption.
    }
    induction (tl (c_li_indices cifc) ++ c_l1_indices cifc); [dest_in|].
    simpl; icase oidx; [mred|].
    mred.
    - elim H0; right; assumption.
    - apply IHl; auto.
      intro; elim H0; right; assumption.
  Qed.

  Lemma implOStatesInit_value_root:
    implOStatesInit@[rootOf topo] = Some implOStateInitRoot.
  Proof.
    intros; unfold implOStatesInit; fold cifc.
    assert (~ In (rootOf topo) (tl (c_li_indices cifc) ++ c_l1_indices cifc)).
    { pose proof (c_li_indices_head_rootOf 0 Htr).
      pose proof (tree2Topo_WfCIfc tr 0); destruct H0 as [? _].
      rewrite H in H0; inv H0; assumption.
    }
    induction (tl (c_li_indices cifc) ++ c_l1_indices cifc); mred.
  Qed.

  Definition implORqsInit: ORqs Msg :=
    initORqs (cifc.(c_li_indices) ++ cifc.(c_l1_indices)).

  Section Rules.
    Variables (oidx cidx: IdxT).

    Section L1.

      Definition l1GetSImm: Rule :=
        rule.immd[0~>0]
        :accepts Spec.getRq
        :from cidx
        :requires (fun ost orq mins => mesiS <= ost#[status])
        :transition
           (!|ost, _| --> (ost, {| miv_id := Spec.getRs;
                                   miv_value := ost#[val]
                                |})).

      Definition l1GetSRqUpUp: Rule :=
        rule.rquu[0~>1]
        :accepts Spec.getRq
        :from cidx
        :me oidx
        :requires (fun ost mins => ost#[status] <= mesiI)
        :transition
           (!|ost, msg| --> {| miv_id := mesiRqS;
                               miv_value := O |}).

      Definition l1GetSRsDownDownS: Rule :=
        rule.rsdd[0~>2~>0]
        :accepts mesiRsS
        :holding Spec.getRq
        :requires ⊤
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[val <- msg_value min]
                     +#[status <- mesiS],
                 {| miv_id := Spec.getRs;
                    miv_value := msg_value min |})).

      Definition l1GetSRsDownDownE: Rule :=
        rule.rsdd[0~>2~>1]
        :accepts mesiRsE
        :holding Spec.getRq
        :requires ⊤
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[val <- msg_value min]
                     +#[status <- mesiE],
                 {| miv_id := Spec.getRs;
                    miv_value := msg_value min |})).

      Definition l1DownSImm: Rule :=
        rule.immu[0~>3]
        :accepts mesiDownRqS
        :me oidx
        :requires (fun ost orq mins => mesiS <= ost#[status])
        :transition
           (!|ost, min| --> (ost +#[status <- mesiS],
                             {| miv_id := mesiDownRsS;
                                miv_value := ost#[val] |})).

      Definition l1GetMImmE: Rule :=
        rule.immd[1~>0~>0]
        :accepts Spec.setRq
        :from cidx
        :requires (fun ost orq mins => ost#[status] = mesiE)
        :transition
           (!|ost, msg|
            --> (ost +#[owned <- true]
                     +#[status <- mesiM]
                     +#[val <- msg_value msg],
                 {| miv_id := Spec.setRs;
                    miv_value := O |})).

      Definition l1GetMImmM: Rule :=
        rule.immd[1~>0~>1]
        :accepts Spec.setRq
        :from cidx
        :requires (fun ost orq mins => ost#[status] = mesiM)
        :transition
           (!|ost, msg|
            --> (ost +#[val <- msg_value msg],
                 {| miv_id := Spec.setRs;
                    miv_value := O |})).

      Definition l1GetMRqUpUp: Rule :=
        rule.rquu[1~>1]
        :accepts Spec.setRq
        :from cidx
        :me oidx
        :requires (fun ost mins => ost#[status] <= mesiS)
        :transition
           (!|ost, msg| --> {| miv_id := mesiRqM;
                               miv_value := O |}).

      Definition l1GetMRsDownDown: Rule :=
        rule.rsdd[1~>2]
        :accepts mesiRsM
        :holding Spec.setRq
        :requires ⊤
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[status <- mesiM]
                     +#[owned <- true]
                     +#[val <- msg_value rq],
                 {| miv_id := Spec.setRs;
                    miv_value := O |})).

      Definition l1DownIImm: Rule :=
        rule.immu[1~>3]
        :accepts mesiDownRqI
        :me oidx
        :requires (fun ost orq mins => mesiS <= ost#[status])
        :transition
           (!|ost, min| --> (ost +#[status <- mesiI],
                             {| miv_id := mesiDownRsI;
                                miv_value := O |})).

      Definition l1InvRqUpUp: Rule :=
        rule.rqu[2~>0]
        :me oidx
        :requires (fun ost mins => mesiNP < ost#[status] < mesiM)
        :transition
           (ost --> {| miv_id := mesiInvRq; miv_value := O |}).

      (** NOTE: L1 writes back only when it is an owner, but here the
       * precondition allows to write back regardless of its ownership.
       * It is to ensure serializability of the system, and a cache controller
       * in a real implementation should fire this rule only when the status
       * is M. Thus this design has more behavior, but still correct. The parent
       * should distinguish whether the data is valid or not by looking at its
       * directory status.
       *)
      Definition l1InvRqUpUpWB: Rule :=
        rule.rqu[2~>1]
        :me oidx
        :requires (fun ost mins => mesiNP < ost#[status])
        :transition
           (ost --> {| miv_id := mesiInvWRq; miv_value := ost#[val] |}).

      Definition l1InvRsDownDown: Rule :=
        rule.rsd[2~>2]
        :accepts mesiInvRs
        :requires ⊤
        :transition (!|ost, _| --> (ost +#[owned <- false]
                                        +#[status <- mesiNP])).

    End L1.

    Section Li.

      Definition liGetSImmS: Rule :=
        rule.immd[0~>0~>0~~cidx]
        :accepts mesiRqS
        :from cidx
        :requires (fun ost orq mins => ost#[status] = mesiS)
        :transition
           (!|ost, _| --> (ost +#[dir <- addSharer cidx ost#[dir]],
                           {| miv_id := mesiRsS;
                              miv_value := ost#[val]
                           |})).

      (** NOTE: it is important to note that the "owned" bit is not changed. *)
      Definition liGetSImmME: Rule :=
        rule.immd[0~>0~>1~~cidx]
        :accepts mesiRqS
        :from cidx
        :requires (fun ost orq mins => mesiE <= ost#[status])
        :transition
           (!|ost, _| --> (ost +#[status <- mesiI]
                               +#[dir <- setDirE cidx],
                           {| miv_id := mesiRsE;
                              miv_value := ost#[val]
                           |})).

      Definition liGetSRqUpUp: Rule :=
        rule.rquu[0~>1~~cidx]
        :accepts mesiRqS
        :from cidx
        :me oidx
        :requires (fun ost mins =>
                     and (ost#[status] <= mesiI)
                         (ost#[dir].(dir_st) = mesiI))
        :transition
           (!|ost, msg| --> {| miv_id := mesiRqS;
                               miv_value := O |}).

      Definition liGetSRsDownDownS: Rule :=
        rule.rsdd[0~>2~>0]
        :accepts mesiRsS
        :holding mesiRqS
        :requires ⊤
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[val <- msg_value min]
                     +#[owned <- false]
                     +#[status <- mesiS]
                     +#[dir <- setDirS [objIdxOf rsbTo]],
                 {| miv_id := mesiRsS;
                    miv_value := msg_value min |})).

      Definition liGetSRsDownDownE: Rule :=
        rule.rsdd[0~>2~>1]
        :accepts mesiRsE
        :holding mesiRqS
        :requires ⊤
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[val <- msg_value min]
                     +#[owned <- false]
                     +#[status <- mesiI]
                     +#[dir <- setDirE (objIdxOf rsbTo)],
                 {| miv_id := mesiRsE;
                    miv_value := msg_value min |})).

      Definition liGetSRqUpDownME: Rule :=
        rule.rqud[0~>3~>0~~cidx]
        :accepts mesiRqS
        :from cidx
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[status] <= mesiI)
                  (mesiE <= ost#[dir].(dir_st)))
        :transition
           (!|ost, msg| --> ([ost#[dir].(dir_excl)],
                             {| miv_id := mesiDownRqS;
                                miv_value := O |})).

      (** NOTE: this case is possible when a parent evicted the cache line 
       * whereas some children are sharers. In this case pick a representative
       * among sharers to get a clean value.
       *)
      Definition liGetSRqUpDownS: Rule :=
        rule.rqud[0~>3~>1~~cidx]
        :accepts mesiRqS
        :from cidx
        :me oidx
        :requires
           ((fun ost mins =>
               and (ost#[status] <= mesiI)
                   (ost#[dir].(dir_st) = mesiS)))
        :transition
           (!|ost, msg| --> ([hd ii (ost#[dir].(dir_sharers))],
                             {| miv_id := mesiDownRqS;
                                miv_value := O |})).

      Definition liDownSRsUpDownME: Rule :=
        rule.rsud[0~>4~>0]
        :accepts mesiDownRsS
        :holding mesiRqS
        :requires (FirstMsg /\ (fun ost orq mins => mesiE <= ost#[dir].(dir_st)))
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
            --> (msg ::= getFirstMsgI mins;
                           (ost +#[val <- msg_value msg]
                                +#[status <- mesiS]
                                +#[dir <- setDirS ((objIdxOf rsbTo)
                                                     :: map objIdxOf rssFrom)],
                            {| miv_id := mesiRsS;
                               miv_value := msg_value msg |}))).

      Definition liDownSRsUpDownS: Rule :=
        rule.rsud[0~>4~>1]
        :accepts mesiDownRsS
        :holding mesiRqS
        :requires (FirstMsg /\ (fun ost orq mins => ost#[dir].(dir_st) = mesiS))
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
            --> (msg ::= getFirstMsgI mins;
                           (ost +#[val <- msg_value msg]
                                +#[status <- mesiS]
                                +#[dir <- addSharer (objIdxOf rsbTo) ost#[dir]],
                            {| miv_id := mesiRsS;
                               miv_value := msg_value msg |}))).

      (** NOTE: data should be sent along with [mesiDownRsS], even when the status 
       * is S or E, since the parent might not have the up-to-date data (e.g., 
       * when the line is evicted).
       *)
      Definition liDownSImm: Rule :=
        rule.immu[0~>5]
        :accepts mesiDownRqS
        :me oidx
        :requires
           (fun ost orq mins => mesiS <= ost#[status])
        :transition
           (!|ost, min| --> (ost +#[owned <- false]
                                 +#[status <- mesiS],
                             {| miv_id := mesiDownRsS;
                                miv_value := ost#[val] |})).

      Definition liDownSRqDownDownME: Rule :=
        rule.rqdd[0~>6~>0]
        :accepts mesiDownRqS
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[status] <= mesiI)
                  (mesiE <= ost#[dir].(dir_st)))
        :transition
           (!|ost, msg| --> ([ost#[dir].(dir_excl)],
                             {| miv_id := mesiDownRqS;
                                miv_value := O |})).

      Definition liDownSRqDownDownS: Rule :=
        rule.rqdd[0~>6~>1]
        :accepts mesiDownRqS
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[status] <= mesiI)
                  (ost#[dir].(dir_st) = mesiS))
        :transition
           (!|ost, msg|
            --> ([hd ii (ost#[dir].(dir_sharers))],
                 {| miv_id := mesiDownRqS;
                    miv_value := O |})).

      Definition liDownSRsUpUp: Rule :=
        rule.rsuu[0~>7]
        :accepts mesiDownRsS
        :holding mesiDownRqS
        :requires FirstMsg
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
            --> (msg ::= getFirstMsgI mins;
                           (ost +#[val <- msg_value msg]
                                +#[owned <- false]
                                +#[status <- mesiS]
                                +#[dir <- setDirS (map objIdxOf rssFrom)],
                            {| miv_id := mesiDownRsS;
                               miv_value := msg_value msg |}))).

      Definition liGetMImm: Rule :=
        rule.immd[1~>0~>0~~cidx]
        :accepts mesiRqM
        :from cidx
        :requires (fun ost orq mins => mesiE <= ost#[status])
        :transition
           (!|ost, msg| --> (ost +#[status <- mesiI]
                                 +#[dir <- setDirM cidx],
                             {| miv_id := mesiRsM;
                                miv_value := O |})).

      Definition liGetMRqUpUp: Rule :=
        rule.rquu[1~>1~~cidx]
        :accepts mesiRqM
        :from cidx
        :me oidx
        :requires (fun ost mins =>
                     and (ost#[status] <= mesiS)
                         (ost#[dir].(dir_st) <= mesiS))
        :transition
           (!|ost, msg| --> {| miv_id := mesiRqM;
                               miv_value := O |}).

      (** This is the case where it's possible to directly respond a [mesiRsM]
       * message back since there are no internal sharers to invalidate.
       *)
      Definition liGetMRsDownDownDirI: Rule :=
        rule.rsdd[1~>2]
        :accepts mesiRsM
        :holding mesiRqM
        :requires (fun ost orq mins => ost#[dir].(dir_st) = mesiI)
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- mesiI] (** TODO: may want to preserve [mesiNP] if it was *)
                     +#[dir <- setDirM (objIdxOf rsbTo)],
                 {| miv_id := mesiRsM;
                    miv_value := O |})).

      (** This is the case where internal invalidation is required 
       * due to sharers.
       *)
      Definition liGetMRsDownRqDownDirS: Rule :=
        rule.rsrq[1~>3]
        :accepts mesiRsM
        :holding mesiRqM
        :me oidx
        :requires (fun ost orq mins => ost#[dir].(dir_st) = mesiS)
        :transition
           (!|ost, rq| --> (ost#[dir].(dir_sharers),
                            {| miv_id := mesiDownRqI;
                               miv_value := O |})).

      Definition liGetMRqUpDownME: Rule :=
        rule.rqud[1~>4~~cidx]
        :accepts mesiRqM
        :from cidx
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[status] <= mesiI)
                  (mesiE <= ost#[dir].(dir_st)))
        :transition
           (!|ost, msg| --> ([ost#[dir].(dir_excl)],
                             {| miv_id := mesiDownRqI;
                                miv_value := O |})).

      Definition liGetMRqUpDownS: Rule :=
        rule.rqud[1~>5~~cidx]
        :accepts mesiRqM
        :from cidx
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[status] <= mesiI)
                  (ost#[dir].(dir_st) = mesiS))
        :transition
           (!|ost, msg| --> (ost#[dir].(dir_sharers),
                             {| miv_id := mesiDownRqI;
                                miv_value := O |})).

      Definition liDownIRsUpDown: Rule :=
        rule.rsud[1~>6]
        :accepts mesiDownRsI
        :holding mesiRqM
        :requires ⊤
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- mesiI] (** TODO: may want to preserve [mesiNP] if it was *)
                     +#[dir <- setDirM (objIdxOf rsbTo)],
                 {| miv_id := mesiRsM;
                    miv_value := O |})).

      Definition liDownIImm: Rule :=
        rule.immu[1~>7]
        :accepts mesiDownRqI
        :me oidx
        :requires (fun ost orq mins => ost#[dir].(dir_st) = mesiI)
        :transition
           (!|ost, min| --> (ost +#[owned <- false]
                                 +#[status <- mesiI],
                             {| miv_id := mesiDownRsI;
                                miv_value := O |})).

      Definition liDownIRqDownDownDirS: Rule :=
        rule.rqdd[1~>9~>0]
        :accepts mesiDownRqI
        :me oidx
        :requires (fun ost mins => ost#[dir].(dir_st) = mesiS)
        :transition
           (!|ost, msg| --> (ost#[dir].(dir_sharers),
                             {| miv_id := mesiDownRqI;
                                miv_value := O |})).

      Definition liDownIRqDownDownDirME: Rule :=
        rule.rqdd[1~>9~>1]
        :accepts mesiDownRqI
        :me oidx
        :requires (fun ost mins => mesiE <= ost#[dir].(dir_st))
        :transition
           (!|ost, msg| --> ([ost#[dir].(dir_excl)],
                             {| miv_id := mesiDownRqI;
                                miv_value := O |})).

      Definition liDownIRsUpUp: Rule :=
        rule.rsuu[1~>10]
        :accepts mesiDownRsI
        :holding mesiDownRqI
        :requires ⊤
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- mesiI]
                     +#[dir <- setDirI],
                 {| miv_id := mesiDownRsI;
                    miv_value := O |})).

      Definition liInvRqUpUp: Rule :=
        rule.rqu[2~>0]
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[owned] = false)
                  (ost#[dir].(dir_st) = mesiI))
        :transition
           (ost --> {| miv_id := mesiInvRq; miv_value := O |}).

      (** NOTE: ditto [l1InvRqUpUpWB]; a cache controller should not use this
       * rule when [owned = false]; it's meaningless.
       *)
      Definition liInvRqUpUpWB: Rule :=
        rule.rqu[2~>1]
        :me oidx
        :requires (fun ost mins => ost#[dir].(dir_st) = mesiI)
        :transition
           (ost --> {| miv_id := mesiInvWRq; miv_value := ost#[val] |}).

      Definition liInvRsDownDown: Rule :=
        rule.rsd[2~>2]
        :accepts mesiInvRs
        :requires ⊤
        :transition (!|ost, _| --> (ost +#[owned <- false]
                                        +#[status <- mesiNP])).

      Definition liPushRqUpUp: Rule :=
        rule.rqu[2~>3]
        :me oidx
        :requires (fun ost mins =>
                     and (ost#[owned] = false)
                         (ost#[dir].(dir_st) <> mesiE))
        :transition
           (ost --> {| miv_id := mesiPushRq; miv_value := O |}).

      (** NOTE: ditto [liInvRqUpUpWB]; a cache controller should not use this
       * rule when [owned = false]. Furthermore, we should not allow the case
       * where the directory status is E or M, in order for the cache to 
       * maintain the clean copy.
       *)
      Definition liPushRqUpUpWB: Rule :=
        rule.rqu[2~>4]
        :me oidx
        :requires (fun ost mins => ost#[dir].(dir_st) < mesiE)
        :transition
           (ost --> {| miv_id := mesiPushWRq; miv_value := ost#[val] |}).

      Definition liInvImmI: Rule :=
        rule.immd[2~>5~~cidx]
        :accepts mesiInvRq
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[dir] = mesiI)
        :transition
           (!|ost, _| --> (ost, {| miv_id := mesiInvRs; miv_value := O |})).

      Definition liInvImmS0: Rule :=
        rule.immd[2~>6~>0~~cidx]
        :accepts mesiInvRq
        :from cidx
        :requires
           (fun ost orq mins =>
              and (getDir cidx ost#[dir] = mesiS)
                  (LastSharer ost#[dir] cidx))
        :transition
           (!|ost, _| --> (ost +#[dir <- setDirI],
                           {| miv_id := mesiInvRs; miv_value := O |})).

      Definition liInvImmS1: Rule :=
        rule.immd[2~>6~>1~~cidx]
        :accepts mesiInvRq
        :from cidx
        :requires
           (fun ost orq mins =>
              and (getDir cidx ost#[dir] = mesiS)
                  (NotLastSharer ost#[dir]))
        :transition
           (!|ost, _| --> (ost +#[dir <- removeSharer cidx ost#[dir]],
                           {| miv_id := mesiInvRs; miv_value := O |})).

      (** NOTE: using [mesiInvRq] to evict an E line implies the line is not
       * dirty, thus the parent can just use its data to upgrade to E.
       *)
      Definition liInvImmE: Rule :=
        rule.immd[2~>7~~cidx]
        :accepts mesiInvRq
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[dir] = mesiE)
        :transition
           (!|ost, msg| --> (ost +#[status <- mesiE]
                                 +#[dir <- setDirI],
                             {| miv_id := mesiInvRs; miv_value := O |})).

      Definition liInvImmWBI: Rule :=
        rule.immd[2~>8~~cidx]
        :accepts mesiInvWRq
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[dir] = mesiI)
        :transition
           (!|ost, _| --> (ost, {| miv_id := mesiInvRs; miv_value := O |})).

      Definition liInvImmWBS0: Rule :=
        rule.immd[2~>9~>0~~cidx]
        :accepts mesiInvWRq
        :from cidx
        :requires
           (fun ost orq mins =>
              and (getDir cidx ost#[dir] = mesiS)
                  (LastSharer ost#[dir] cidx))
        :transition
           (!|ost, _| --> (ost +#[dir <- setDirI],
                           {| miv_id := mesiInvRs; miv_value := O |})).

      Definition liInvImmWBS1: Rule :=
        rule.immd[2~>9~>1~~cidx]
        :accepts mesiInvRq
        :from cidx
        :requires
           (fun ost orq mins =>
              and (getDir cidx ost#[dir] = mesiS)
                  (NotLastSharer ost#[dir]))
        :transition
           (!|ost, _| --> (ost +#[dir <- removeSharer cidx ost#[dir]],
                           {| miv_id := mesiInvRs; miv_value := O |})).

      (** NOTE: using [mesiInvWRq] to evict an E line implies the line is dirty,
       * thus the parent should take the value and upgrade its status to M.
       *)
      Definition liInvImmWBME: Rule :=
        rule.immd[2~>10~~cidx]
        :accepts mesiInvWRq
        :from cidx
        :requires (fun ost orq mins => mesiE <= getDir cidx ost#[dir])
        :transition
           (!|ost, msg| --> (ost +#[dir <- setDirI]
                                 +#[owned <- true]
                                 +#[status <- mesiM]
                                 +#[val <- msg_value msg],
                             {| miv_id := mesiInvRs; miv_value := O |})).

      Definition liPushImm: Rule :=
        rule.immd[2~>11~~cidx]
        :accepts mesiPushRq
        :from cidx
        :requires ⊤
        :transition
           (!|ost, _| --> (ost, {| miv_id := mesiInvRs; miv_value := O |})).

      Definition liPushImmWB0: Rule :=
        rule.immd[2~>12~>0~~cidx]
        :accepts mesiPushWRq
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[dir] < mesiE)
        :transition
           (!|ost, msg| --> (ost, {| miv_id := mesiInvRs; miv_value := O |})).

      Definition liPushImmWB1: Rule :=
        rule.immd[2~>12~>1~~cidx]
        :accepts mesiPushWRq
        :from cidx
        :requires (fun ost orq mins => mesiE <= getDir cidx ost#[dir])
        :transition
           (!|ost, msg| --> (ost +#[owned <- true]
                                 +#[status <- mesiS]
                                 +#[val <- msg_value msg]
                                 +#[dir <- setDirS [cidx]],
                             {| miv_id := mesiInvRs; miv_value := O |})).

    End Li.

  End Rules.

  Section Objects.
    Variable (oidx: IdxT).

    Section L1.
      Let eidx := l1ExtOf oidx.

      Program Definition l1: Object :=
        {| obj_idx := oidx;
           obj_rules :=
             [(** rules involved with [GetS] *)
               l1GetSImm eidx; l1GetSRqUpUp oidx eidx;
                 l1GetSRsDownDownS; l1GetSRsDownDownE; l1DownSImm oidx;
                   (** rules involved with [GetM] *)
                   l1GetMImmE eidx; l1GetMImmM eidx;
                     l1GetMRqUpUp oidx eidx;
                     l1GetMRsDownDown; l1DownIImm oidx;
                       (** rules involved with [Put] *)
                       l1InvRqUpUp oidx; l1InvRqUpUpWB oidx; l1InvRsDownDown];
           obj_rules_valid := _ |}.
      Next Obligation.
        inds_valid_tac.
      Qed.

    End L1.

    Definition liRulesFromChild (cidx: IdxT): list Rule :=
      [liGetSImmS cidx; liGetSImmME cidx; liGetSRqUpUp oidx cidx;
         liGetSRqUpDownME oidx cidx; liGetSRqUpDownS oidx cidx;
           liGetMImm cidx; liGetMRqUpUp oidx cidx;
             liGetMRqUpDownME oidx cidx; liGetMRqUpDownS oidx cidx;
               liInvImmI cidx; liInvImmS0 cidx; liInvImmS1 cidx; liInvImmE cidx;
                 liInvImmWBI cidx; liInvImmWBS0 cidx; liInvImmWBS1 cidx;
                   liInvImmWBME cidx; liPushImm cidx;
                     liPushImmWB0 cidx; liPushImmWB1 cidx].

    Definition liRulesFromChildren (coinds: list IdxT): list Rule :=
      List.concat (map liRulesFromChild coinds).

    Hint Unfold liRulesFromChild liRulesFromChildren: RuleConds.

    Ltac disc_child_inds_disj :=
      pose proof (tree2Topo_TreeTopo tr 0);
      try match goal with
          | [Hn: ?n1 <> ?n2,
             H1: nth_error (subtreeChildrenIndsOf ?topo ?sidx) ?n1 = Some _,
             H2: nth_error (subtreeChildrenIndsOf ?topo ?sidx) ?n2 = Some _ |- _] =>
            eapply TreeTopo_children_inds_disj in Hn; eauto; destruct Hn
          end.
    
    Program Definition li: Object :=
      {| obj_idx := oidx;
         obj_rules :=
           (liRulesFromChildren (subtreeChildrenIndsOf topo oidx))
             (** rules involved with [GetS] *)
             ++ [liGetSRsDownDownS; liGetSRsDownDownE; liDownSRsUpDownME;
                   liDownSRsUpDownS; liDownSImm oidx;
                     liDownSRqDownDownME oidx; liDownSRqDownDownS oidx;
                       liDownSRsUpUp]
             (** rules involved with [GetM] *)
             ++ [liGetMRsDownDownDirI; liGetMRsDownRqDownDirS oidx; liDownIRsUpDown;
                   liDownIImm oidx; liDownIRqDownDownDirS oidx; liDownIRqDownDownDirME oidx;
                       liDownIRsUpUp]
             (** rules involved with [Put] *)
             ++ [liInvRqUpUp oidx; liInvRqUpUpWB oidx; liInvRsDownDown;
                   liPushRqUpUp oidx; liPushRqUpUpWB oidx];
         obj_rules_valid := _ |}.
    Next Obligation.
      solve_inds_NoDup disc_child_inds_disj.
    Qed.

    Definition memRulesFromChild (cidx: IdxT): list Rule :=
      [liGetSImmS cidx; liGetSImmME cidx;
         liGetSRqUpDownME oidx cidx; liGetMImm cidx;
           liGetMRqUpDownME oidx cidx; liGetMRqUpDownS oidx cidx;
             liInvImmI cidx; liInvImmS0 cidx; liInvImmS1 cidx; liInvImmE cidx;
               liInvImmWBI cidx; liInvImmWBS0 cidx; liInvImmWBS1 cidx;
                 liInvImmWBME cidx; liPushImm cidx;
                   liPushImmWB0 cidx; liPushImmWB1 cidx].

    Definition memRulesFromChildren (coinds: list IdxT): list Rule :=
      List.concat (map memRulesFromChild coinds).

    Hint Unfold memRulesFromChild memRulesFromChildren: RuleConds.

    Program Definition mem: Object :=
      {| obj_idx := oidx;
         obj_rules :=
           (memRulesFromChildren (subtreeChildrenIndsOf topo oidx))
             ++ [liDownSRsUpDownME; liDownIRsUpDown];
         obj_rules_valid := _ |}.
    Next Obligation.
      solve_inds_NoDup disc_child_inds_disj.
    Qed.
    
  End Objects.

  Program Definition impl: System :=
    {| sys_objs :=
         ((mem (rootOf topo) :: map li (tl cifc.(c_li_indices)))
            ++ map l1 cifc.(c_l1_indices));
       sys_oinds_valid := _;
       sys_minds := cifc.(c_minds);
       sys_merqs := cifc.(c_merqs);
       sys_merss := cifc.(c_merss);
       sys_msg_inds_valid := _;
       sys_oss_inits := implOStatesInit;
       sys_orqs_inits := implORqsInit |}.
  Next Obligation.
    unfold mem, li, l1.
    rewrite map_app.
    do 2 rewrite map_trans.
    do 2 rewrite map_id.
    unfold topo, cifc.
    rewrite app_comm_cons.
    rewrite <-c_li_indices_head_rootOf by assumption.
    apply tree2Topo_WfCIfc.
  Qed.
  Next Obligation.
    apply tree2Topo_WfCIfc.
  Qed.
  
End System.

Hint Unfold l1GetSImm l1GetSRqUpUp l1GetSRsDownDownS l1GetSRsDownDownE
     l1DownSImm l1GetMImmE l1GetMImmM l1GetMRqUpUp l1GetMRsDownDown
     l1DownIImm l1InvRqUpUp l1InvRqUpUpWB l1InvRsDownDown: MesiRules.

Hint Unfold liGetSImmS liGetSImmME
     liGetSRqUpUp liGetSRsDownDownS liGetSRsDownDownE
     liGetSRqUpDownME liGetSRqUpDownS liDownSRsUpDownME liDownSRsUpDownS
     liDownSImm liDownSRqDownDownME liDownSRqDownDownS liDownSRsUpUp
     liGetMImm liGetMRqUpUp liGetMRsDownDownDirI liGetMRsDownRqDownDirS
     liGetMRqUpDownME liGetMRqUpDownS liDownIRsUpDown
     liDownIImm liDownIRqDownDownDirS liDownIRqDownDownDirME liDownIRsUpUp
     liInvRqUpUp liInvRqUpUpWB liInvRsDownDown
     liPushRqUpUp liPushRqUpUpWB
     liInvImmI liInvImmS0 liInvImmS1 liInvImmE
     liInvImmWBI liInvImmWBS0 liInvImmWBS1 liInvImmWBME
     liPushImm liPushImmWB0 liPushImmWB1: MesiRules.

