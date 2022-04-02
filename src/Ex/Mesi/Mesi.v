Require Import Bool Vector List String Peano_dec Lia.
Require Import Common FMap HVector IndexSupport Syntax Semantics.
Require Import Topology RqRsTopo.
Require Import RqRsLang. Import RqRsNotations.

Require Import Ex.Spec Ex.SpecInds Ex.Template Ex.Mesi.
Import RuleTemplateNotations.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

(** Design choices:
 * - Hierarchical (for an arbitrary tree topology)
 * - MESI
 * - Directory (not snooping)
 * - Invalidate (not update)
 * - Write-back (not write-through)
 * - Non-inclusive
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
 * - A further remark about write-back: there are two writeback types, based on
 *   whether it writes the dirty data back or not.
 *     Both a child and the parent should be able to distinguish these writeback
 *   types so they can do state transitions appropriately. For example, let's
 *   say an L1 cache previously had the E status and silently changed its status
 *   to M to make the cache line dirty. When this line is evicted, the parent
 *   (L2) has no idea whether it needs to update the line. In this case the
 *   child (L1) should send the dirty data with an appropriate message id, in
 *   order for the parent to recognize the update is required.
 *)

Section Invalidate.
  Definition invalidate (st: MESI) :=
    if eq_nat_dec st mesiNP then mesiNP else mesiI.

  Lemma invalidate_sound:
    forall st, invalidate st <= mesiI.
  Proof. unfold invalidate; cbv; intros; find_if_inside; lia. Qed.

  Lemma invalidate_I:
    forall st, mesiI <= st -> invalidate st = mesiI.
  Proof. unfold invalidate; cbv; intros; find_if_inside; lia. Qed.

  Lemma invalidate_NP:
    forall st, st = mesiNP -> invalidate st = mesiNP.
  Proof. unfold invalidate; cbv; intros; find_if_inside; lia. Qed.
End Invalidate.

#[global] Hint Resolve invalidate_sound.

Ltac solve_mesi :=
  unfold mesiM, mesiE, mesiS, mesiI, mesiNP in *; solve [auto|lia].

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
      {| dir_st := mesiS;
         dir_excl := dir.(dir_excl);
         dir_sharers :=
           if eq_nat_dec dir.(dir_st) mesiS
           then oidx :: dir.(dir_sharers) else [oidx] |}.

    Definition removeSharer (oidx: IdxT) (dir: DirT): DirT :=
      {| dir_st := mesiS;
         dir_excl := dir.(dir_excl);
         dir_sharers := removeOnce idx_dec oidx dir.(dir_sharers) |}.

    Definition LastSharer (dir: DirT) (cidx: IdxT) :=
      dir.(dir_sharers) = [cidx].

    Definition NotLastSharer (dir: DirT) :=
      2 <= List.length dir.(dir_sharers).

    Definition OtherSharerExists (dir: DirT) (cidx: IdxT) :=
      remove idx_dec cidx dir.(dir_sharers) <> nil.

    Section Facts.

      Ltac dir_crush :=
        cbv [getDir addSharer removeSharer
                    setDirI setDirS setDirE setDirM];
        simpl; intros;
        repeat find_if_inside;
        repeat
          (try match goal with
               | [H: ~ In ?oidx (?oidx :: _) |- _] => elim H; left; reflexivity
               | [Ht: In ?oidx ?l, Hn: ~ In ?oidx (_ :: ?l) |- _] => elim Hn; right; assumption
               | [H: In _ (_ :: _) |- _] => inv H
               | [H: _ |- _] => exfalso; auto; fail
               end; try subst; try reflexivity; try assumption; try solve_mesi).

      Lemma getDir_M_imp:
        forall oidx dir,
          getDir oidx dir = mesiM ->
          dir.(dir_st) = mesiM /\ dir.(dir_excl) = oidx.
      Proof.
        unfold getDir, caseDec; intros.
        find_if_inside; [find_if_inside; [auto|discriminate]|].
        repeat (find_if_inside; [find_if_inside; discriminate|]).
        discriminate.
      Qed.

      Lemma getDir_E_imp:
        forall oidx dir,
          getDir oidx dir = mesiE ->
          dir.(dir_st) = mesiE /\ dir.(dir_excl) = oidx.
      Proof.
        unfold getDir, caseDec; intros.
        find_if_inside; [find_if_inside; discriminate|].
        find_if_inside; [find_if_inside; [auto|discriminate]|].
        find_if_inside; [find_if_inside; discriminate|].
        discriminate.
      Qed.

      Lemma getDir_ME_imp:
        forall oidx dir,
          mesiE <= getDir oidx dir ->
          mesiE <= dir.(dir_st) <= mesiM /\ dir.(dir_excl) = oidx.
      Proof.
        unfold getDir, caseDec; intros.
        do 2 (find_if_inside; [find_if_inside;
                               [repeat split; [..|auto]; rewrite e; solve_mesi
                               |solve_mesi]|]).
        find_if_inside; [find_if_inside; solve_mesi|].
        solve_mesi.
      Qed.

      Lemma getDir_S_imp:
        forall oidx dir,
          getDir oidx dir = mesiS ->
          dir.(dir_st) = mesiS /\ In oidx dir.(dir_sharers).
      Proof.
        unfold getDir, caseDec; intros.
        repeat (find_if_inside; [find_if_inside; discriminate|]).
        find_if_inside; [find_if_inside; [auto|discriminate]|].
        discriminate.
      Qed.

      Lemma getDir_addSharer_spec:
        forall dir,
          dir.(dir_st) <= mesiS ->
          forall oidx sidx,
            getDir oidx (addSharer sidx dir) =
            if idx_dec sidx oidx
            then mesiS else getDir oidx dir.
      Proof. dir_crush. Qed.

      Lemma getDir_removeSharer_sound:
        forall oidx sidx dir,
          getDir oidx (removeSharer sidx dir) <= mesiS.
      Proof. dir_crush. Qed.

      Lemma getDir_removeSharer_neq:
        forall oidx sidx dir,
          getDir sidx dir = mesiS ->
          oidx <> sidx ->
          getDir oidx (removeSharer sidx dir) = getDir oidx dir.
      Proof.
        dir_crush.
        - exfalso; apply removeOnce_In_2 in i; auto.
        - exfalso; elim n.
          apply removeOnce_In_1; assumption.
      Qed.

      Lemma getDir_LastSharer_eq:
        forall sidx dir,
          dir_st dir = mesiS ->
          LastSharer dir sidx ->
          getDir sidx dir = mesiS.
      Proof.
        unfold LastSharer; dir_crush.
        rewrite H0 in *; firstorder idtac.
      Qed.

      Lemma getDir_LastSharer_neq:
        forall oidx sidx dir,
          getDir sidx dir = mesiS ->
          LastSharer dir sidx -> oidx <> sidx ->
          getDir oidx dir = mesiI.
      Proof.
        unfold LastSharer; dir_crush.
        rewrite H0 in *; dest_in; exfalso; auto.
      Qed.

      Lemma getDir_S_sharer:
        forall dir,
          dir.(dir_st) = mesiS ->
          forall oidx,
            In oidx dir.(dir_sharers) ->
            getDir oidx dir = mesiS.
      Proof. dir_crush. Qed.

      Lemma getDir_S_non_sharer:
        forall dir,
          dir.(dir_st) = mesiS ->
          forall oidx,
            ~ In oidx dir.(dir_sharers) ->
            getDir oidx dir = mesiI.
      Proof. dir_crush. Qed.

      Lemma getDir_st_I:
        forall dir,
          dir.(dir_st) = mesiI ->
          forall oidx, getDir oidx dir = mesiI.
      Proof. dir_crush. Qed.

      Lemma getDir_st_sound:
        forall dir oidx,
          mesiS <= getDir oidx dir ->
          getDir oidx dir <= dir.(dir_st).
      Proof. dir_crush. Qed.

      Lemma getDir_setDirI:
        forall oidx, getDir oidx setDirI = mesiI.
      Proof. dir_crush. Qed.

      Lemma getDir_setDirS_I_imp:
        forall oidx shs, getDir oidx (setDirS shs) = mesiI -> ~ In oidx shs.
      Proof. dir_crush. Qed.

      Lemma getDir_setDirS_S_imp:
        forall oidx shs, getDir oidx (setDirS shs) = mesiS -> In oidx shs.
      Proof. dir_crush. Qed.

      Lemma getDir_setDirS_sound:
        forall oidx shs, getDir oidx (setDirS shs) <= mesiS.
      Proof. dir_crush. Qed.

      Lemma getDir_setDirE_eq:
        forall oidx, getDir oidx (setDirE oidx) = mesiE.
      Proof. dir_crush. Qed.

      Lemma getDir_setDirE_neq:
        forall oidx eidx, eidx <> oidx -> getDir oidx (setDirE eidx) = mesiI.
      Proof. dir_crush. Qed.

      Lemma getDir_setDirM_eq:
        forall oidx, getDir oidx (setDirM oidx) = mesiM.
      Proof. dir_crush. Qed.

      Lemma getDir_setDirM_neq:
        forall oidx eidx, eidx <> oidx -> getDir oidx (setDirM eidx) = mesiI.
      Proof. dir_crush. Qed.

      Lemma getDir_excl_eq:
        forall dir eidx,
          eidx = dir.(dir_excl) ->
          mesiE <= dir.(dir_st) <= mesiM ->
          getDir eidx dir = dir.(dir_st).
      Proof. dir_crush. Qed.

      Lemma getDir_excl_neq:
        forall dir eidx,
          eidx = dir.(dir_excl) ->
          mesiE <= dir.(dir_st) <= mesiM ->
          forall oidx,
            oidx <> eidx ->
            getDir oidx dir = mesiI.
      Proof. dir_crush. Qed.

    End Facts.

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

  Lemma implOStatesInit_None:
    forall oidx,
      ~ In oidx (c_li_indices cifc ++ c_l1_indices cifc) ->
      implOStatesInit@[oidx] = None.
  Proof.
    unfold implOStatesInit; intros.
    mred.
    - elim H.
      subst topo cifc.
      rewrite c_li_indices_head_rootOf by assumption.
      left; reflexivity.
    - assert (~ In oidx (tl (c_li_indices cifc) ++ c_l1_indices cifc)).
      { subst topo cifc; rewrite c_li_indices_head_rootOf in H by assumption.
        intro Hx; elim H; right; assumption.
      }
      clear -H0.
      generalize dependent (tl (c_li_indices cifc) ++ c_l1_indices cifc).
      induction l; simpl; intros; [reflexivity|].
      mred.
  Qed.

  Definition implORqsInit: ORqs Msg :=
    initORqs (cifc.(c_li_indices) ++ cifc.(c_l1_indices)).

  Lemma implORqsInit_value:
    forall oidx,
      In oidx (c_li_indices cifc ++ c_l1_indices cifc) ->
      implORqsInit@[oidx] = Some [].
  Proof.
    intros; unfold implORqsInit; fold cifc.
    induction (c_li_indices cifc ++ c_l1_indices cifc); [dest_in|].
    simpl; icase oidx; mred.
  Qed.

  Section Rules.
    Variables (oidx cidx: IdxT).

    Section L1.
      (** NOTE: [cidx] will be instantiated to [l1ExtOf oidx]. *)

      Definition l1GetSImm: Rule :=
        rule 0~>0 from template immd {
          receive Spec.getRq from cidx;
          assert (fun ost orq mins => mesiS <= ost#[status]);
          !|ost, _| --> (ost, <| Spec.getRs; ost#[val] |>)
        }.

      Definition l1GetSRqUpUp: Rule :=
        rule 0~>1 from template rquu {
          receive Spec.getRq from cidx to oidx;
          assert (fun ost mins => ost#[status] <= mesiI);
          (!|ost, msg| --> <| mesiRqS; O |>)
        }.

      Definition l1GetSRsDownDownS: Rule :=
        rule 0~>2~>0 from template rsdd {
          receive mesiRsS;
          hold Spec.getRq;
          assert (fun _ _ _ => True);
          (!|ost, min, rq, rsbTo|
            --> (ost +#[val <- msg_value min]
                     +#[status <- mesiS],
                  <| Spec.getRs; msg_value min |>))
        }.

      Definition l1GetSRsDownDownE: Rule :=
        rule 0~>2~>1 from template rsdd {
          receive mesiRsE;
          hold Spec.getRq;
          assert (fun _ _ _ => True);
          (!|ost, min, rq, rsbTo|
            --> (ost +#[val <- msg_value min]
                     +#[status <- mesiE],
                  <| Spec.getRs; msg_value min |>))
        }.

      Definition l1DownSImm: Rule :=
        rule 0~>3 from template immu {
          receive mesiDownRqS to oidx;
          assert (fun ost orq mins => mesiS <= ost#[status]);
          (!|ost, min| --> (ost +#[owned <- false]
                                +#[status <- mesiS],
                             <| mesiDownRsS; ost#[val] |>))
        }.

      Definition l1GetMImmE: Rule :=
        rule 1~>0~>0 from template immd {
          receive Spec.setRq from cidx;
          assert (fun ost orq mins => ost#[status] = mesiE);
          (!|ost, msg|
            --> (ost +#[owned <- true]
                     +#[status <- mesiM]
                     +#[val <- msg_value msg],
                  <| Spec.setRs; O |>))
        }.

      Definition l1GetMImmM: Rule :=
        rule 1~>0~>1 from template immd {
          receive Spec.setRq from cidx;
          assert
            (fun ost orq mins =>
               ost#[owned] = true /\ ost#[status] = mesiM);
          (!|ost, msg| --> (ost +#[val <- msg_value msg],
                             <| Spec.setRs; O |>))
        }.

      Definition l1GetMRqUpUp: Rule :=
        rule 1~>1 from template rquu {
          receive Spec.setRq from cidx to oidx;
          assert (fun ost mins => ost#[status] <= mesiS);
          (!|ost, msg| --> <| mesiRqM; O |>)
        }.

      Definition l1GetMRsDownDown: Rule :=
        rule 1~>2 from template rsdd {
          receive mesiRsM;
          hold Spec.setRq;
          assert (fun _ _ _ => True);
          (!|ost, min, rq, rsbTo|
            --> (ost +#[status <- mesiM]
                     +#[owned <- true]
                     +#[val <- msg_value rq],
                  <| Spec.setRs; O |>))
        }.

      Definition l1DownIImmS: Rule :=
        rule 1~>3~>0 from template immu {
          receive mesiDownRqIS to oidx;
          assert (fun _ _ _ => True);
          (!|ost, min| --> (ost +#[owned <- false]
                                +#[status <- invalidate ost#[status]],
                             <| mesiDownRsIS; O |>))
        }.

      Definition l1DownIImmME: Rule :=
        rule 1~>3~>1 from template immu {
          receive mesiDownRqIM to oidx;
          assert (fun ost orq mins => mesiE <= ost#[status]);
          (!|ost, min| --> (ost +#[owned <- false]
                                +#[status <- invalidate ost#[status]],
                             <| mesiDownRsIM; O |>))
        }.

      Definition l1InvRqUpUp: Rule :=
        rule 2~>0 from template rqsu {
          to oidx;
          assert (fun ost => ost#[owned] = false /\ mesiNP < ost#[status] < mesiM);
          (ost --> <| mesiInvRq; O |>)
        }.

      (** NOTE: L1 writes back only when it is an owner, but here the
       * precondition allows to write back regardless of its ownership.
       * It is to ensure serializability of the system, and a cache controller
       * in a real implementation should fire this rule only when the status
       * is M. Thus this design has more behavior, but still correct. The parent
       * should distinguish whether the data is valid or not by looking at its
       * directory status.
       *)
      Definition l1InvRqUpUpWB: Rule :=
        rule 2~>1 from template rqsu {
          to oidx;
          assert (fun ost => mesiNP < ost#[status]);
          (ost --> <| mesiInvWRq; ost#[val] |>)
        }.

      Definition l1InvRsDownDown: Rule :=
        rule 2~>2 from template rsds {
          receive mesiInvRs;
          assert (fun _ _ _ => True);
          (!|ost, _| --> (ost +#[owned <- false]
                              +#[status <- mesiNP]))
        }.

    End L1.

    Section Li.

      Definition liGetSImmS: Rule :=
        rule 0~>0~>0~~cidx from template immd {
          receive mesiRqS from cidx;
          assert (fun ost orq mins =>
                    ost#[dir].(dir_st) <= mesiS /\ ost#[status] = mesiS);
          (!|ost, _| --> (ost +#[dir <- addSharer cidx ost#[dir]],
                           <| mesiRsS; ost#[val] |>))
        }.

      (** NOTE: it is important to note that the "owned" bit is not changed. *)
      Definition liGetSImmME: Rule :=
        rule 0~>0~>1~~cidx from template immd {
          receive mesiRqS from cidx;
          assert (fun ost orq mins =>
                    mesiE <= ost#[status] /\ ost#[dir].(dir_st) = mesiI);
          (!|ost, _| --> (ost +#[status <- mesiI]
                              +#[dir <- setDirE cidx],
                           <| mesiRsE; ost#[val] |>))
        }.

      Definition liGetSRqUpUp: Rule :=
        rule 0~>1~~cidx from template rquu {
          receive mesiRqS from cidx to oidx;
          assert (fun ost mins =>
                    ost#[owned] = false /\
                      ost#[status] <= mesiI /\ ost#[dir].(dir_st) <= mesiS);
          (!|ost, msg| --> <| mesiRqS; O |>)
        }.

      Definition liGetSRsDownDownS: Rule :=
        rule 0~>2~>0 from template rsdd {
          receive mesiRsS;
          hold mesiRqS;
          assert (fun _ _ _ => True);
          (!|ost, min, rq, rsbTo|
            --> (ost +#[val <- msg_value min]
                     +#[owned <- false]
                     +#[status <- mesiS]
                     +#[dir <- addSharer (objIdxOf rsbTo) ost#[dir]],
                 <| mesiRsS; msg_value min |>))
        }.

      Definition liGetSRsDownDownE: Rule :=
        rule 0~>2~>1 from template rsdd {
          receive mesiRsE;
          hold mesiRqS;
          assert (fun _ _ _ => True);
          (!|ost, min, rq, rsbTo|
            --> (ost +#[val <- msg_value min]
                     +#[owned <- false]
                     +#[status <- mesiI]
                     +#[dir <- setDirE (objIdxOf rsbTo)],
                  <| mesiRsE; msg_value min |>))
        }.

      Definition liGetSRqUpDownME: Rule :=
        rule 0~>3~~cidx from template rqud {
          receive mesiRqS from cidx to oidx;
          assert
            (fun ost mins =>
               cidx <> ost#[dir].(dir_excl) /\
                 In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
                 ost#[status] <= mesiI /\ mesiE <= ost#[dir].(dir_st) <= mesiM);
          (!|ost, msg| --> ([ost#[dir].(dir_excl)], <| mesiDownRqS; O |>))
        }.

      Definition liDownSRsUpDownME: Rule :=
        rule 0~>4 from template rsudo {
          receive mesiDownRsS;
          hold mesiRqS;
          assert (fun _ => True);
          (!|ost, idm, rq, rsbTo|
            --> (ost +#[owned <- true]
                     +#[val <- msg_value (valOf idm)]
                     +#[status <- mesiS]
                     +#[dir <- setDirS [objIdxOf rsbTo; objIdxOf (idOf idm)]],
                  <| mesiRsS; msg_value (valOf idm) |>))
        }.

      (** NOTE:
       * 1) data should be sent along with [mesiDownRsS], even when the status
       * is S or E, since the parent might not have the up-to-date data (e.g.,
       * when the line is evicted).
       * 2) when the status is S, it should be the owner since it previously had
       * the status E or M.
       *)
      Definition liDownSImm: Rule :=
        rule 0~>5 from template immu {
          receive mesiDownRqS to oidx;
          assert
            (fun ost orq mins =>
               mesiS <= ost#[status] /\ ost#[dir].(dir_st) <= mesiS);
          (!|ost, min| --> (ost +#[owned <- false]
                                +#[status <- mesiS],
                             <| mesiDownRsS; ost#[val] |>))
        }.

      Definition liDownSRqDownDownME: Rule :=
        rule 0~>6 from template rqdd {
          receive mesiDownRqS to oidx;
          assert
            (fun ost mins =>
               In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
               ost#[status] <= mesiI /\ mesiE <= ost#[dir].(dir_st) <= mesiM);
          (!|ost, msg| --> ([ost#[dir].(dir_excl)], <| mesiDownRqS; O |>))
        }.

      Definition liDownSRsUpUp: Rule :=
        rule 0~>7 from template rsuuo {
          receive mesiDownRsS;
          hold mesiDownRqS;
          assert (fun _ => True);
          (!|ost, idm, rq, rsbTo|
            --> (ost +#[val <- msg_value (valOf idm)]
                     +#[owned <- false]
                     +#[status <- mesiS]
                     +#[dir <- setDirS [objIdxOf (idOf idm)]],
                 <| mesiDownRsS; msg_value (valOf idm) |>))
        }.

      Definition liGetMImm: Rule :=
        rule 1~>0~~cidx from template immd {
          receive mesiRqM from cidx;
          assert
            (fun ost orq mins =>
               mesiE <= ost#[status] \/
               (ost#[status] = mesiS /\ ost#[owned] = true /\
               ost#[dir].(dir_st) = mesiS /\ LastSharer ost#[dir] cidx));
          (!|ost, msg| --> (ost +#[owned <- false]
                                +#[status <- mesiI]
                                +#[dir <- setDirM cidx],
                             <| mesiRsM; O |>))
        }.

      Definition liGetMRqUpUp: Rule :=
        rule 1~>1~~cidx from template rquu {
          receive mesiRqM from cidx to oidx;
          assert
            (fun ost mins =>
               ost#[owned] = false /\
               ost#[status] <= mesiS /\ ost#[dir].(dir_st) <= mesiS);
          (!|ost, msg| --> <| mesiRqM; O |>)
        }.

      (** This is the case where it's possible to directly respond a [mesiRsM]
       * message back since there are no internal sharers to invalidate.
       *)
      Definition liGetMRsDownDownDirI: Rule :=
        rule 1~>2 from template rsdd {
          receive mesiRsM;
          hold mesiRqM;
          assert (fun ost orq mins =>
                    ost#[dir].(dir_st) = mesiI \/
                    (ost#[dir].(dir_st) = mesiS /\
                    LastSharer ost#[dir] (objIdxOf (getUpLockIdxBackI orq))));
          (!|ost, min, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirM (objIdxOf rsbTo)],
                 <| mesiRsM; O |>))
        }.

      (** This is the case where internal invalidation is required
       * due to sharers.
       *)
      Definition liGetMRsDownRqDownDirS: Rule :=
        rule 1~>3 from template rsrq {
          receive mesiRsM to oidx;
          hold mesiRqM;
          assert
            (fun ost orq mins =>
               RsDownRqDownSoundPrec
                 topo oidx orq
                 (remove idx_dec (objIdxOf (getUpLockIdxBackI orq))
                         ost#[dir].(dir_sharers)) /\
               ost#[dir].(dir_sharers) <> nil /\
               SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
               OtherSharerExists ost#[dir] (objIdxOf (getUpLockIdxBackI orq)) /\
               ost#[dir].(dir_st) = mesiS);
          (!|ost, rq, rsbTo| --> (ost +#[owned <- true],
                                   (remove idx_dec (objIdxOf rsbTo) ost#[dir].(dir_sharers),
                                     <| mesiDownRqIS; O |>)))
        }.

      Definition liGetMRqUpDownME: Rule :=
        rule 1~>4~~cidx from template rqud {
          receive mesiRqM from cidx to oidx;
          assert
            (fun ost mins =>
               cidx <> ost#[dir].(dir_excl) /\
               In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
               ost#[status] <= mesiI /\ mesiE <= ost#[dir].(dir_st) <= mesiM);
          (!|ost, msg| --> ([ost#[dir].(dir_excl)], <| mesiDownRqIM; O |>))
        }.

      Definition liGetMRqUpDownS: Rule :=
        rule 1~>5~~cidx from template rqud {
          receive mesiRqM from cidx to oidx;
          assert
            (fun ost mins =>
               ost#[dir].(dir_sharers) <> nil /\
               SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
               OtherSharerExists ost#[dir] cidx /\
               ost#[owned] = true /\ ost#[status] <= mesiS /\ ost#[dir].(dir_st) = mesiS);
          (!|ost, msg| --> (remove idx_dec cidx ost#[dir].(dir_sharers), <| mesiDownRqIS; O |>))
        }.

      Definition liDownIRsUpDownS: Rule :=
        rule 1~>6~>0 from template rsud {
          receive mesiDownRsIS;
          hold mesiRqM;
          assert (fun ost => ost#[dir].(dir_st) = mesiS);
          (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirM (objIdxOf rsbTo)],
                  <| mesiRsM; O |>))
        }.

      Definition liDownIRsUpDownME: Rule :=
        rule 1~>6~>1 from template rsud {
          receive mesiDownRsIM;
          hold mesiRqM;
          assert (fun ost => mesiE <= ost#[dir].(dir_st));
          (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirM (objIdxOf rsbTo)],
                  <| mesiRsM; O |>))
        }.

      Definition liDownIImmS: Rule :=
        rule 1~>7~>0 from template immu {
          receive mesiDownRqIS to oidx;
          assert (fun ost orq mins => ost#[dir].(dir_st) = mesiI);
          (!|ost, min| --> (ost +#[owned <- false]
                                +#[status <- invalidate ost#[status]],
                             <| mesiDownRsIS; O |>))
        }.

      Definition liDownIImmME: Rule :=
        rule 1~>7~>1 from template immu {
          receive mesiDownRqIM to oidx;
          assert (fun ost orq mins =>
                     mesiE <= ost#[status] /\ ost#[dir].(dir_st) = mesiI);
          (!|ost, min| --> (ost +#[owned <- false]
                                +#[status <- mesiI],
                             <| mesiDownRsIM; O |>))
        }.

      Definition liDownIRqDownDownDirS: Rule :=
        rule 1~>9~>0 from template rqdd {
          receive mesiDownRqIS to oidx;
          assert
            (fun ost mins =>
               ost#[dir].(dir_sharers) <> nil /\
               SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
               ost#[dir].(dir_st) = mesiS);
          (!|ost, msg| --> (ost#[dir].(dir_sharers), <| mesiDownRqIS; O |>))
        }.

      Definition liDownIRqDownDownDirME: Rule :=
        rule 1~>9~>1 from template rqdd {
          receive mesiDownRqIM to oidx;
          assert
            (fun ost mins =>
               In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
               mesiE <= ost#[dir].(dir_st) <= mesiM);
          (!|ost, msg| --> ([ost#[dir].(dir_excl)], <| mesiDownRqIM; O |>))
        }.

      Definition liDownIRqDownDownDirMES: Rule :=
        rule 1~>9~>2 from template rqdd {
          receive mesiDownRqIM to oidx;
          assert
            (fun ost mins =>
               ost#[dir].(dir_sharers) <> nil /\
               SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
               ost#[dir].(dir_st) = mesiS);
          (!|ost, msg| --> (ost#[dir].(dir_sharers), <| mesiDownRqIS; O |>))
        }.

      Definition liDownIRsUpUpS: Rule :=
        rule 1~>10~>0 from template rsuu {
          receive mesiDownRsIS;
          hold mesiDownRqIS;
          assert (fun _ => True);
          (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirI],
                  <| mesiDownRsIS; O |>))
        }.

      Definition liDownIRsUpUpME: Rule :=
        rule 1~>10~>1 from template rsuu {
          receive mesiDownRsIM;
          hold mesiDownRqIM;
          assert (fun ost => mesiE <= ost#[dir].(dir_st));
          (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirI],
                  <| mesiDownRsIM; O |>))
        }.

      Definition liDownIRsUpUpMES: Rule :=
        rule 1~>10~>2 from template rsuu {
          receive mesiDownRsIS;
          hold mesiDownRqIM;
          assert (fun ost => ost#[dir].(dir_st) = mesiS);
          (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirI],
                  <| mesiDownRsIM; O |>))
        }.

      (** NOTE: Here having [ost#[owned] = false] as a precondition is very
       * important since there's a chance that the object has a _dirty_ line
       * even if the status is S.
       *)
      Definition liInvRqUpUp: Rule :=
        rule 2~>0 from template rqsu {
          to oidx;
          assert
            (fun ost => ost#[owned] = false /\
                        mesiNP < ost#[status] < mesiM /\
                        ost#[dir].(dir_st) = mesiI);
          (ost --> <| mesiInvRq; O |>)
        }.

      (** NOTE: ditto [l1InvRqUpUpWB]; a cache controller should not use this
       * rule when [owned = false]; it's meaningless.
       *)
      Definition liInvRqUpUpWB: Rule :=
        rule 2~>1 from template rqsu {
          to oidx;
          assert
            (fun ost =>
               ost#[dir].(dir_st) = mesiI /\
               ((ost#[owned] = true /\ mesiI < ost#[status]) \/
                (ost#[owned] = false /\ mesiNP < ost#[status] < mesiE)));
          (ost --> <| mesiInvWRq; ost#[val] |>)
        }.

      Definition liInvRsDownDown: Rule :=
        rule 2~>2 from template rsds {
          receive mesiInvRs;
          assert (fun _ _ _ => True);
          (!|ost, _| --> (ost +#[owned <- false]
                              +#[status <- mesiNP]))
        }.

      Definition liDropImm: Rule :=
        rule 2~>3 from template imm {
          assert (fun ost orq mins =>
                    (ost#[status] = mesiI /\ ost#[dir].(dir_st) <> mesiE) \/
                    (ost#[status] = mesiS /\ ost#[owned] = false));
          (ost --> ost +#[status <- mesiNP])
        }.

      Definition liInvImmI: Rule :=
        rule 2~>5~~cidx from template immd {
          receive mesiInvRq from cidx;
          assert (fun ost orq mins => getDir cidx ost#[dir] = mesiI);
          (!|ost, _| --> (ost, <| mesiInvRs; O |>))
        }.

      Definition liInvImmS00: Rule :=
        rule 2~>6~>0~>0~~cidx from template immd {
          receive mesiInvRq from cidx;
          assert
            (fun ost orq mins =>
               ost#[owned] = false /\
               getDir cidx ost#[dir] = mesiS /\ LastSharer ost#[dir] cidx);
          (!|ost, _| --> (ost +#[dir <- setDirI], <| mesiInvRs; O |>))
        }.

      Definition liInvImmS01: Rule :=
        rule 2~>6~>0~>1~~cidx from template immd {
          receive mesiInvRq from cidx;
          assert
            (fun ost orq mins =>
               ost#[owned] = true /\ ost#[status] = mesiS /\
               getDir cidx ost#[dir] = mesiS /\ LastSharer ost#[dir] cidx);
          (!|ost, _| --> (ost +#[status <- mesiM]
                              +#[dir <- setDirI], <| mesiInvRs; O |>))
        }.

      Definition liInvImmS1: Rule :=
        rule 2~>6~>1~~cidx from template immd {
          receive mesiInvRq from cidx;
          assert
            (fun ost orq mins =>
               getDir cidx ost#[dir] = mesiS /\ NotLastSharer ost#[dir]);
          (!|ost, _| --> (ost +#[dir <- removeSharer cidx ost#[dir]],
                           <| mesiInvRs; O |>))
        }.

      (** NOTE: using [mesiInvRq] to evict an E line implies the line is not
       * dirty, thus the parent can just use its data to upgrade to E.
       *)
      Definition liInvImmE: Rule :=
        rule 2~>7~~cidx from template immd {
          receive mesiInvRq from cidx;
          assert (fun ost orq mins => getDir cidx ost#[dir] = mesiE);
          (!|ost, msg| --> (ost +#[status <- mesiE]
                                +#[dir <- setDirI],
                             <| mesiInvRs; O |>))
        }.

      Definition liInvImmWBI: Rule :=
        rule 2~>8~~cidx from template immd {
          receive mesiInvWRq from cidx;
          assert (fun ost orq mins => getDir cidx ost#[dir] = mesiI);
          (!|ost, _| --> (ost, <| mesiInvRs; O |>))
        }.

      Definition liInvImmWBS0: Rule :=
        rule 2~>9~>0~~cidx from template immd {
          receive mesiInvWRq from cidx;
          assert
            (fun ost orq mins =>
               ost#[owned] = false /\
               getDir cidx ost#[dir] = mesiS /\ LastSharer ost#[dir] cidx);
          (!|ost, _| --> (ost +#[dir <- setDirI], <| mesiInvRs; O |>))
        }.

      Definition liInvImmWBS1: Rule :=
        rule 2~>9~>1~~cidx from template immd {
          receive mesiInvWRq from cidx;
          assert
            (fun ost orq mins =>
               getDir cidx ost#[dir] = mesiS /\ NotLastSharer ost#[dir]);
          (!|ost, _| --> (ost +#[dir <- removeSharer cidx ost#[dir]],
                           <| mesiInvRs; O |>))
        }.

      Definition liInvImmWBS: Rule :=
        rule 2~>10~~cidx from template immd {
          receive mesiInvWRq from cidx;
          assert
            (fun ost orq mins =>
               ost#[owned] = true /\ ost#[status] = mesiS /\
               getDir cidx ost#[dir] = mesiS /\ LastSharer ost#[dir] cidx);
          (!|ost, msg| --> (ost +#[status <- mesiM]
                                +#[dir <- setDirI], <| mesiInvRs; O |>))
        }.

      (** NOTE: using [mesiInvWRq] to evict a line implies the line is dirty,
       * thus the parent should take the value and upgrade its status to M. *)
      Definition liInvImmWBME: Rule :=
        rule 2~>11~~cidx from template immd {
          receive mesiInvWRq from cidx;
          assert (fun ost orq mins => mesiE <= getDir cidx ost#[dir]);
          (!|ost, msg| --> (ost +#[dir <- setDirI]
                                +#[owned <- true]
                                +#[status <- mesiM]
                                +#[val <- msg_value msg],
                             <| mesiInvRs; O |>))
        }.

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
             l1GetMRsDownDown; l1DownIImmS oidx; l1DownIImmME oidx;
             (** rules involved with [Put] *)
             l1InvRqUpUp oidx; l1InvRqUpUpWB oidx; l1InvRsDownDown];
           obj_rules_valid := _ |}.
      Next Obligation.
        inds_valid_tac.
      Qed.

    End L1.

    Definition liRulesFromChild (cidx: IdxT): list Rule :=
      [liGetSImmS cidx; liGetSImmME cidx; liGetSRqUpUp oidx cidx;
      liGetSRqUpDownME oidx cidx; liGetMImm cidx; liGetMRqUpUp oidx cidx;
      liGetMRqUpDownME oidx cidx; liGetMRqUpDownS oidx cidx;
      liInvImmI cidx; liInvImmS00 cidx; liInvImmS01 cidx; liInvImmS1 cidx;
      liInvImmE cidx; liInvImmWBI cidx; liInvImmWBS0 cidx; liInvImmWBS1 cidx;
      liInvImmWBS cidx; liInvImmWBME cidx].

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
                liDownSImm oidx; liDownSRqDownDownME oidx; liDownSRsUpUp]
             (** rules involved with [GetM] *)
             ++ [liGetMRsDownDownDirI; liGetMRsDownRqDownDirS oidx;
                liDownIRsUpDownS; liDownIRsUpDownME; liDownIImmS oidx; liDownIImmME oidx;
                liDownIRqDownDownDirS oidx; liDownIRqDownDownDirME oidx; liDownIRqDownDownDirMES oidx;
                liDownIRsUpUpS; liDownIRsUpUpME; liDownIRsUpUpMES]
             (** rules involved with [Put] *)
             ++ [liInvRqUpUp oidx; liInvRqUpUpWB oidx; liInvRsDownDown; liDropImm];
         obj_rules_valid := _ |}.
    Next Obligation.
      solve_inds_NoDup disc_child_inds_disj.
    Qed.

    Definition memRulesFromChild (cidx: IdxT): list Rule :=
      [liGetSImmME cidx; liGetMImm cidx; liInvImmE cidx; liInvImmWBME cidx].

    Definition memRulesFromChildren (coinds: list IdxT): list Rule :=
      List.concat (map memRulesFromChild coinds).

    Hint Unfold memRulesFromChild memRulesFromChildren: RuleConds.

    Program Definition mem: Object :=
      {| obj_idx := oidx;
         obj_rules := (memRulesFromChildren (subtreeChildrenIndsOf topo oidx));
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

#[global] Hint Unfold l1GetSImm l1GetSRqUpUp l1GetSRsDownDownS l1GetSRsDownDownE
 l1DownSImm l1GetMImmE l1GetMImmM l1GetMRqUpUp l1GetMRsDownDown
 l1DownIImmS l1DownIImmME l1InvRqUpUp l1InvRqUpUpWB l1InvRsDownDown: MesiRules.

#[global] Hint Unfold liGetSImmS liGetSImmME
 liGetSRqUpUp liGetSRsDownDownS liGetSRsDownDownE
 liGetSRqUpDownME liDownSRsUpDownME
 liDownSImm liDownSRqDownDownME liDownSRsUpUp
 liGetMImm liGetMRqUpUp liGetMRsDownDownDirI liGetMRsDownRqDownDirS
 liGetMRqUpDownME liGetMRqUpDownS liDownIRsUpDownS liDownIRsUpDownME
 liDownIImmS liDownIImmME liDownIRqDownDownDirS liDownIRqDownDownDirME liDownIRqDownDownDirMES
 liDownIRsUpUpS liDownIRsUpUpME liDownIRsUpUpMES liInvRqUpUp liInvRqUpUpWB liInvRsDownDown
 liInvImmI liInvImmS00 liInvImmS01 liInvImmS1 liInvImmE
 liInvImmWBI liInvImmWBS0 liInvImmWBS1 liInvImmWBS liInvImmWBME liDropImm: MesiRules.
