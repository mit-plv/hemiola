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
 *
 * - Non-inclusive: 
 *     In order to implement non-inclusive caches, each cache has a "summary"
 *   status, the status from the viewpoint of others. For example, an L2 cache
 *   and its children could have a dirty data if one of the children has the M
 *   status. They "still" can have the dirty data after sharing it, i.e., the L2
 *   cache and some of the children now have S.
 *     Now at the time the L2 wants to evict this dirty data, even if its status
 *   is S it needs to know the data is dirty (must written back to its parent).
 *   The summary status of the L2 is, in this case, still M so it knows that the
 *   data should be written back.
 *     Note that for an L1 cache the summary status is not used since it does
 *   not have any children. The main memory does not use the summary status
 *   either since it never evicts data.
 *
 * - A further remark about the summary status: if cache inclusion policy is
 *   inclusive, then we do not need such a summary status, since evicting a 
 *   cache line always requires back invalidation of its children. It implies
 *   the eviction always makes the summary status invalid (I).
 *)

Section System.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo := fst (tree2Topo tr 0).
  Let cifc := snd (tree2Topo tr 0).
  
  Definition val: Fin.t 4 := F1.
  Definition summary: Fin.t 4 := F2.
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

  End Directory.

  Instance ImplOStateIfc: OStateIfc :=
    {| ost_ty := [nat:Type; MESI:Type; MESI:Type; DirT:Type]%vector |}.

  Definition implOStateInit: OState :=
    (0, (mesiI, (mesiI, (dirInit, tt)))).

  Definition implOStateInitRoot: OState :=
    (0, (mesiM, (mesiM, (dirInit, tt)))).

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

  (* Definition summaryOf (ost: OState): MESI := *)
  (*   if Compare_dec.le_gt_dec mesiS ost#[status] *)
  (*   then ost#[status] *)
  (*   else ost#[dir].(dir_st). *)

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
        :requires (fun ost mins => ost#[status] = mesiI)
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
            --> (ost +#[status <- mesiM]
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

      (** NOTE: An L1 cache does not have a case to send [mesiPutRqS] when
       * evicting a line, since it does not have any children that might have
       * the dirty line.
       *)
      Definition l1InvRqUpUp: Rule :=
        rule.rqu[2~>0]
        :me oidx
        :requires (fun ost mins => ost#[status] < mesiM)
        :transition
           (ost --> {| miv_id := mesiInvRq;
                       miv_value := O |}).

      (** NOTE: L1 writes back only when the status is M, but here the
       * precondition allows to write back regardless of its status.
       * It is to ensure serializability of the system, and a cache controller
       * in a real implementation should fire this rule only when the status
       * is M. Thus this design has more behavior, but still correct. The parent
       * should distinguish whether the data is valid or not by looking at its
       * directory status.
       *)
      Definition l1InvRqUpUpM: Rule :=
        rule.rqu[2~>1]
        :me oidx
        :requires (fun ost mins => ost#[status] <= mesiM)
        :transition
           (ost --> {| miv_id := mesiInvRq;
                       miv_value := ost#[val] |}).

      Definition l1InvRsDownDown: Rule :=
        rule.rsd[2~>2]
        :accepts mesiInvRs
        :requires ⊤
        :transition (!|ost, _| --> ost +#[status <- mesiI]).

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

      (** Note that here the summary status is not changed (it should be E or M
       * for this case). If the summary status is M, for instance, it implies that
       * the data is dirty.
       *)
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
        :requires (fun ost mins => ost#[summary] = mesiI)
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
                     +#[summary <- mesiS]
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
            --> (ost +#[summary <- mesiE]
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
              and (ost#[status] = mesiI)
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
               and (ost#[status] = mesiI)
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

      Definition liDownSImm: Rule :=
        rule.immu[0~>5]
        :accepts mesiDownRqS
        :me oidx
        :requires
           (fun ost orq mins =>
              and (mesiS <= ost#[status])
                  (ost#[dir].(dir_st) = mesiI))
        :transition
           (!|ost, min| --> (ost +#[summary <- mesiS]
                                 +#[status <- mesiS],
                             {| miv_id := mesiDownRsS;
                                miv_value := ost#[val] |})).

      Definition liDownSRqDownDownME: Rule :=
        rule.rqdd[0~>6~>0]
        :accepts mesiDownRqS
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[status] = mesiI)
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
              and (ost#[status] = mesiI)
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
                                +#[summary <- mesiS]
                                +#[status <- mesiS]
                                +#[dir <- setDirS (map objIdxOf rssFrom)],
                            {| miv_id := mesiDownRsS;
                               miv_value := msg_value msg |}))).

      Definition liGetMImm: Rule :=
        rule.immd[1~>0~~cidx]
        :accepts mesiRqM
        :from cidx
        :requires (fun ost orq mins => mesiE <= ost#[status])
        :transition
           (!|ost, msg| --> (ost +#[summary <- mesiM]
                                 +#[status <- mesiI]
                                 +#[dir <- setDirM cidx],
                             {| miv_id := mesiRsM;
                                miv_value := O |})).

      Definition liGetMRqUpUp: Rule :=
        rule.rquu[1~>1~~cidx]
        :accepts mesiRqM
        :from cidx
        :me oidx
        :requires (fun ost mins => ost#[summary] <= mesiS)
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
            --> (ost +#[summary <- mesiM]
                     +#[status <- mesiI]
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

      Definition liDownIRsUpDownDirS: Rule :=
        rule.rsud[1~>4]
        :accepts mesiDownRsI
        :holding mesiRqM
        :requires ⊤
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
            --> (ost +#[summary <- mesiM]
                     +#[status <- mesiI]
                     +#[dir <- setDirM (objIdxOf rsbTo)],
                 {| miv_id := mesiRsM;
                    miv_value := O |})).

      Definition liGetMRqUpDownME: Rule :=
        rule.rqud[1~>5~~cidx]
        :accepts mesiRqM
        :from cidx
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[status] = mesiI)
                  (mesiE <= ost#[dir].(dir_st)))
        :transition
           (!|ost, msg| --> ([ost#[dir].(dir_excl)],
                             {| miv_id := mesiDownRqI;
                                miv_value := O |})).

      Definition liGetMRqUpDownS: Rule :=
        rule.rqud[1~>6~~cidx]
        :accepts mesiRqM
        :from cidx
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[status] = mesiI)
                  (ost#[dir].(dir_st) = mesiS))
        :transition
           (!|ost, msg| --> (ost#[dir].(dir_sharers),
                             {| miv_id := mesiDownRqI;
                                miv_value := O |})).

      Definition liDownIRsUpDown: Rule :=
        rule.rsud[1~>7]
        :accepts mesiDownRsI
        :holding mesiRqM
        :requires ⊤
        :transition
           (!|ost, mins, rq, rssFrom, rsbTo|
            --> (ost +#[summary <- mesiM]
                     +#[status <- mesiI]
                     +#[dir <- setDirM (objIdxOf rsbTo)],
                 {| miv_id := mesiRsM;
                    miv_value := O |})).

      Definition liDownIImm: Rule :=
        rule.immu[1~>8]
        :accepts mesiDownRqI
        :me oidx
        :requires (fun ost orq mins => ost#[dir].(dir_st) = mesiI)
        :transition
           (!|ost, min| --> (ost +#[summary <- mesiI]
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
            --> (ost +#[summary <- mesiI]
                     +#[status <- mesiI]
                     +#[dir <- setDirI],
                 {| miv_id := mesiDownRsI;
                    miv_value := O |})).

      Definition liInvRqUpUp: Rule :=
        rule.rqu[2~>0]
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[status] <= mesiE)
                  (ost#[dir].(dir_st) = mesiI))
        :transition
           (ost --> {| miv_id := mesiInvRq;
                       miv_value := O |}).

      (** NOTE: ditto [l1InvRqUpUpM]; a cache controller should not use this
       * rule when [st <= E] 
       *)
      Definition liInvRqUpUpM: Rule :=
        rule.rqu[2~>1]
        :me oidx
        :requires
           (fun ost mins =>
              and (ost#[status] <= mesiM)
                  (ost#[dir].(dir_st) = mesiI))
        :transition
           (ost --> {| miv_id := mesiInvRq;
                       miv_value := ost#[val] |}).

      Definition liInvRsDownDown: Rule :=
        rule.rsd[2~>2]
        :accepts mesiInvRs
        :requires ⊤
        :transition (!|ost, _| --> (ost +#[summary <- mesiI]
                                        +#[status <- mesiI])).

      Definition liPushRqUpUp: Rule :=
        rule.rqu[2~>3]
        :me oidx
        :requires (fun ost mins => ost#[summary] <= mesiE)
        :transition
           (ost --> {| miv_id := mesiPushRq;
                       miv_value := O |}).

      (** NOTE: ditto [liInvRqUpUpM]; a cache controller should not use this
       * rule when [sum <= E] 
       *)
      Definition liPushRqUpUpM: Rule :=
        rule.rqu[2~>4]
        :me oidx
        :requires
           (fun ost mins =>
              (and (ost#[summary] = mesiM) (ost#[status] = mesiS)) \/
              (ost#[summary] <= mesiE))
        :transition
           (ost --> {| miv_id := mesiPushRq;
                       miv_value := ost#[val] |}).

      (** NOTE: no summary change; this is the case where the cache is just
       * writing a line back (not doing the whole invalidation).
       *)
      Definition liPushRsDownDown: Rule :=
        rule.rsd[2~>5]
        :accepts mesiInvRs
        :requires ⊤
        :transition (!|ost, _| --> (ost +#[status <- mesiI])).

      Definition liInvImmI: Rule :=
        rule.immd[2~>6~~cidx]
        :accepts mesiInvRq
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[dir] = mesiI)
        :transition
           (!|ost, _| --> (ost, {| miv_id := mesiInvRs; miv_value := O |})).
      
      Definition liInvImmS: Rule :=
        rule.immd[2~>7~~cidx]
        :accepts mesiInvRq
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[dir] = mesiS)
        :transition
           (!|ost, _| --> (ost +#[dir <- removeSharer cidx ost#[dir]],
                           {| miv_id := mesiInvRs; miv_value := O |})).

      Definition liInvImmE: Rule :=
        rule.immd[2~>8~~cidx]
        :accepts mesiInvRq
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[dir] = mesiE)
        :transition
           (!|ost, msg| --> (ost +#[status <- mesiE]
                                 +#[dir <- setDirI],
                             {| miv_id := mesiInvRs; miv_value := O |})).

      Definition liInvImmM: Rule :=
        rule.immd[2~>9~~cidx]
        :accepts mesiInvRq
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[dir] = mesiM)
        :transition
           (!|ost, msg| --> (ost +#[status <- mesiM]
                                 +#[val <- msg_value msg]
                                 +#[dir <- setDirI],
                             {| miv_id := mesiInvRs; miv_value := O |})).

      Definition liPushImmESI: Rule :=
        rule.immd[2~>10~~cidx]
        :accepts mesiPushRq
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[dir] <= mesiE)
        :transition
           (!|ost, _| --> (ost, {| miv_id := mesiPushRs; miv_value := O |})).

      Definition liPushImmM: Rule :=
        rule.immd[2~>11~~cidx]
        :accepts mesiPushRq
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[dir] = mesiM)
        :transition
           (!|ost, msg| --> (ost +#[status <- mesiS]
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
                       l1InvRqUpUp oidx; l1InvRqUpUpM oidx; l1InvRsDownDown];
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
               liInvImmI cidx; liInvImmS cidx; liInvImmE cidx; liInvImmM cidx;
                 liPushImmESI cidx; liPushImmM cidx].

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
             ++ [liGetMRsDownDownDirI; liGetMRsDownRqDownDirS oidx; liDownIRsUpDownDirS;
                   liDownIRsUpDown; liDownIImm oidx;
                     liDownIRqDownDownDirS oidx; liDownIRqDownDownDirME oidx;
                       liDownIRsUpUp]
             (** rules involved with [Put] *)
             ++ [liInvRqUpUp oidx; liInvRqUpUpM oidx; liInvRsDownDown;
                   liPushRqUpUp oidx; liPushRqUpUpM oidx; liPushRsDownDown];
         obj_rules_valid := _ |}.
    Next Obligation.
      solve_inds_NoDup disc_child_inds_disj.
    Qed.

    Definition memRulesFromChild (cidx: IdxT): list Rule :=
      [liGetSImmS cidx; liGetSImmME cidx;
         liGetSRqUpDownME oidx cidx; liGetMImm cidx;
             liGetMRqUpDownME oidx cidx; liGetMRqUpDownS oidx cidx;
               liInvImmI cidx; liInvImmS cidx; liInvImmE cidx; liInvImmM cidx;
                 liPushImmESI cidx; liPushImmM cidx].

    Definition memRulesFromChildren (coinds: list IdxT): list Rule :=
      List.concat (map memRulesFromChild coinds).

    Hint Unfold memRulesFromChild memRulesFromChildren: RuleConds.

    Program Definition mem: Object :=
      {| obj_idx := oidx;
         obj_rules :=
           (memRulesFromChildren (subtreeChildrenIndsOf topo oidx))
             ++ [liDownSRsUpDownME; liDownIRsUpDownDirS; liDownIRsUpDown];
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
     l1DownIImm l1InvRqUpUp l1InvRqUpUpM l1InvRsDownDown: MesiRules.

Hint Unfold liGetSImmS liGetSImmME liGetSRqUpUp liGetSRsDownDownS liGetSRsDownDownE
     liGetSRqUpDownME liGetSRqUpDownS liDownSRsUpDownME liDownSRsUpDownS
     liDownSImm liDownSRqDownDownME liDownSRqDownDownS liDownSRsUpUp
     liGetMImm liGetMRqUpUp liGetMRsDownDownDirI liGetMRsDownRqDownDirS
     liDownIRsUpDownDirS liGetMRqUpDownME liGetMRqUpDownS liDownIRsUpDown
     liDownIImm liDownIRqDownDownDirS liDownIRqDownDownDirME liDownIRsUpUp
     liInvRqUpUp liInvRqUpUpM liInvRsDownDown liPushRqUpUp liPushRqUpUpM liPushRsDownDown
     liInvImmI liInvImmS liInvImmE liInvImmM liPushImmESI liPushImmM: MesiRules.

