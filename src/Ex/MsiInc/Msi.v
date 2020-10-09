Require Import Bool Vector List String Peano_dec Lia.
Require Import Common FMap HVector IndexSupport Syntax Semantics.
Require Import Topology RqRsTopo.
Require Import RqRsLang. Import RqRsNotations.

Require Import Ex.Spec Ex.SpecInds Ex.Template Ex.Msi.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

(** Design choices:
 * - Hierarchical (for an arbitrary tree topology)
 * - MSI
 * - Directory (not snooping)
 * - Invalidate (not update)
 * - Write-back (not write-through)
 * - Inclusive
 *)

Section System.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo := fst (tree2Topo tr 0).
  Let cifc := snd (tree2Topo tr 0).

  (** Cache states *)

  Instance ImplOStateIfc: OStateIfc :=
    {| ost_ty := [nat:Type; bool:Type; MSI:Type; DirT:Type]%vector |}.

  Definition implOStateInit: OState :=
    (0, (false, (msiNP, (dirInit, tt)))).

  Definition implOStateInitRoot: OState :=
    (0, (true, (msiM, (dirInit, tt)))).

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

  (** Rules per cache *)
  Section Rules.
    Variables (oidx cidx: IdxT).

    Section L1.
      (** NOTE: for L1 caches [cidx] will be instantiated to [l1ExtOf oidx]. *)

      Definition l1GetSImm: Rule :=
        rule.immd[0~>0]
        :accepts Spec.getRq
        :from cidx
        :requires (fun ost orq mins => msiS <= ost#[status])
        :transition
           (!|ost, _| --> (ost, <| Spec.getRs; ost#[val] |>)).

      Definition l1GetSRqUpUp: Rule :=
        rule.rquu[0~>1]
        :accepts Spec.getRq
        :from cidx
        :me oidx
        :requires (fun ost mins => ost#[status] <= msiI)
        :transition
           (!|ost, msg| --> <| msiRqS; O |>).

      Definition l1GetSRsDownDown: Rule :=
        rule.rsdd[0~>2]
        :accepts msiRsS
        :holding Spec.getRq
        :requires (fun _ _ _ => True)
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[val <- msg_value min]
                     +#[status <- msiS],
                 <| Spec.getRs; msg_value min |>)).

      Definition l1DownSImm: Rule :=
        rule.immu[0~>3]
        :accepts msiDownRqS
        :me oidx
        :requires (fun ost orq mins => msiS <= ost#[status])
        :transition
           (!|ost, min| --> (ost +#[owned <- false]
                                 +#[status <- msiS],
                             <| msiDownRsS; ost#[val] |>)).

      Definition l1GetMImm: Rule :=
        rule.immd[1~>0]
        :accepts Spec.setRq
        :from cidx
        :requires
           (fun ost orq mins =>
              ost#[owned] = true /\ ost#[status] = msiM)
        :transition
           (!|ost, msg|
            --> (ost +#[val <- msg_value msg],
                 <| Spec.setRs; O |>)).

      Definition l1GetMRqUpUp: Rule :=
        rule.rquu[1~>1]
        :accepts Spec.setRq
        :from cidx
        :me oidx
        :requires (fun ost mins => ost#[status] <= msiS)
        :transition
           (!|ost, msg| --> <| msiRqM; O |>).

      Definition l1GetMRsDownDown: Rule :=
        rule.rsdd[1~>2]
        :accepts msiRsM
        :holding Spec.setRq
        :requires (fun _ _ _ => True)
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[status <- msiM]
                     +#[owned <- true]
                     +#[val <- msg_value rq],
                 <| Spec.setRs; O |>)).

      Definition l1DownIImmS: Rule :=
        rule.immu[1~>3~>0]
        :accepts msiDownRqIS
        :me oidx
        :requires (fun _ _ _ => True)
        :transition
           (!|ost, min| --> (ost +#[owned <- false]
                                 +#[status <- invalidate ost#[status]],
                             <| msiDownRsIS; O |>)).

      Definition l1DownIImmM: Rule :=
        rule.immu[1~>3~>1]
        :accepts msiDownRqIM
        :me oidx
        :requires (fun ost orq mins => ost#[status] = msiM)
        :transition
           (!|ost, min| --> (ost +#[owned <- false]
                                 +#[status <- invalidate ost#[status]],
                             <| msiDownRsIM; ost#[val] |>)).

      Definition l1InvRqUpUp: Rule :=
        rule.rqsu[2~>0]
        :me oidx
        :requires (fun ost => ost#[owned] = false /\ msiNP < ost#[status] < msiM)
        :transition
           (ost --> <| msiInvRq; O |>).

      (** NOTE: L1 writes back only when it is an owner, but here the
       * precondition allows to write back regardless of its ownership.
       * It is to ensure serializability of the system, and a cache controller
       * in a real implementation should fire this rule only when the status
       * is M. Thus this design has more behavior, but still correct. The parent
       * should distinguish whether the data is valid or not by looking at its
       * directory status.
       *)
      Definition l1InvRqUpUpWB: Rule :=
        rule.rqsu[2~>1]
        :me oidx
        :requires (fun ost => msiNP < ost#[status])
        :transition
           (ost --> <| msiInvWRq; ost#[val] |>).

      Definition l1InvRsDownDown: Rule :=
        rule.rsds[2~>2]
        :accepts msiInvRs
        :requires (fun _ _ _ => True)
        :transition (!|ost, _| --> (ost +#[owned <- false]
                                        +#[status <- msiNP])).

    End L1.

    Section Li.

      Definition liGetSImmS: Rule :=
        rule.immd[0~>0~>0~~cidx]
        :accepts msiRqS
        :from cidx
        :requires
           (fun ost orq mins =>
              ost#[dir].(dir_st) <= msiS /\ ost#[status] = msiS)
        :transition
           (!|ost, _| --> (ost +#[dir <- addSharer cidx ost#[dir]],
                           <| msiRsS; ost#[val] |>)).

      (** NOTE: it is important to note that the "owned" bit is not changed at all. *)
      Definition liGetSImmM: Rule :=
        rule.immd[0~>0~>1~~cidx]
        :accepts msiRqS
        :from cidx
        :requires
           (fun ost orq mins =>
              ost#[status] = msiM /\ ost#[dir].(dir_st) = msiI)
        :transition
           (!|ost, _| --> (ost +#[status <- msiS]
                               +#[dir <- setDirS [cidx]],
                           <| msiRsS; ost#[val] |>)).

      Definition liGetSRqUpUp: Rule :=
        rule.rquu[0~>1~~cidx]
        :accepts msiRqS
        :from cidx
        :me oidx
        :requires
           (fun ost mins =>
              ost#[owned] = false /\
              ost#[status] <= msiI /\ ost#[dir].(dir_st) <= msiS)
        :transition (!|ost, msg| --> <| msiRqS; O |>).

      Definition liGetSRsDownDown: Rule :=
        rule.rsdd[0~>2~>0]
        :accepts msiRsS
        :holding msiRqS
        :requires (fun _ _ _ => True)
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[val <- msg_value min]
                     +#[owned <- false]
                     +#[status <- msiS]
                     +#[dir <- addSharer (objIdxOf rsbTo) ost#[dir]],
                 <| msiRsS; msg_value min |>)).

      Definition liGetSRqUpDownM: Rule :=
        rule.rqud[0~>3~~cidx]
        :accepts msiRqS
        :from cidx
        :me oidx
        :requires
           (fun ost mins =>
              cidx <> ost#[dir].(dir_excl) /\
              In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
              ost#[status] <= msiI /\ ost#[dir].(dir_st) = msiM)
        :transition
           (!|ost, msg| --> ([ost#[dir].(dir_excl)], <| msiDownRqS; O |>)).

      Definition liDownSRsUpDownM: Rule :=
        rule.rsudo[0~>4]
        :accepts msiDownRsS
        :holding msiRqS
        :requires (fun _ _ _ => True)
        :transition
           (!|ost, idm, rq, rsbTo|
            --> (ost +#[owned <- true]
                     +#[val <- msg_value (valOf idm)]
                     +#[status <- msiS]
                     +#[dir <- setDirS [objIdxOf rsbTo; objIdxOf (idOf idm)]],
                 <| msiRsS; msg_value (valOf idm) |>)).

      (** NOTE:
       * 1) data should be sent along with [msiDownRsS], even when the status
       * is S, since the parent might not have the up-to-date data (e.g., when
       * the line is evicted).
       * 2) when the status is S, it should be the owner since it previously had
       * the status M.
       *)
      Definition liDownSImm: Rule :=
        rule.immu[0~>5]
        :accepts msiDownRqS
        :me oidx
        :requires
           (fun ost orq mins =>
              msiS <= ost#[status] /\ ost#[dir].(dir_st) <= msiS)
        :transition
           (!|ost, min| --> (ost +#[owned <- false]
                                 +#[status <- msiS],
                             <| msiDownRsS; ost#[val] |>)).

      Definition liDownSRqDownDownM: Rule :=
        rule.rqdd[0~>6]
        :accepts msiDownRqS
        :me oidx
        :requires
           (fun ost mins =>
              In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
              ost#[status] <= msiI /\ ost#[dir].(dir_st) = msiM)
        :transition
           (!|ost, msg| --> ([ost#[dir].(dir_excl)],
                             <| msiDownRqS; O |>)).

      Definition liDownSRsUpUp: Rule :=
        rule.rsuuo[0~>7]
        :accepts msiDownRsS
        :holding msiDownRqS
        :requires (fun _ _ _ => True)
        :transition
           (!|ost, idm, rq, rsbTo|
            --> (ost +#[val <- msg_value (valOf idm)]
                     +#[owned <- false]
                     +#[status <- msiS]
                     +#[dir <- setDirS [objIdxOf (idOf idm)]],
                 <| msiDownRsS; msg_value (valOf idm) |>)).

      Definition liGetMImm: Rule :=
        rule.immd[1~>0~~cidx]
        :accepts msiRqM
        :from cidx
        :requires
           (fun ost orq mins =>
              ost#[status] = msiM \/
              (ost#[status] = msiS /\ ost#[owned] = true /\
               ost#[dir].(dir_st) = msiS /\ LastSharer ost#[dir] cidx))
        :transition
           (!|ost, msg| --> (ost +#[owned <- false]
                                 +#[status <- msiI]
                                 +#[dir <- setDirM cidx],
                             <| msiRsM; O |>)).

      Definition liGetMRqUpUp: Rule :=
        rule.rquu[1~>1~~cidx]
        :accepts msiRqM
        :from cidx
        :me oidx
        :requires
           (fun ost mins =>
              ost#[owned] = false /\
              ost#[status] <= msiS /\ ost#[dir].(dir_st) <= msiS)
        :transition
           (!|ost, msg| --> <| msiRqM; O |>).

      (** A case where it's possible to directly respond a [msiRsM] message back
       * since there are no internal sharers to invalidate. *)
      Definition liGetMRsDownDownDirI: Rule :=
        rule.rsdd[1~>2]
        :accepts msiRsM
        :holding msiRqM
        :requires
           (fun ost orq mins =>
              ost#[dir].(dir_st) = msiI \/
              (ost#[dir].(dir_st) = msiS /\
               LastSharer ost#[dir] (objIdxOf (getUpLockIdxBackI orq))))
        :transition
           (!|ost, min, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirM (objIdxOf rsbTo)],
                 <| msiRsM; O |>)).

      (** A case where internal invalidation is required due to sharers. *)
      Definition liGetMRsDownRqDownDirS: Rule :=
        rule.rsrq[1~>3]
        :accepts msiRsM
        :holding msiRqM
        :me oidx
        :requires
           (fun ost orq mins =>
              RsDownRqDownSoundPrec
                topo oidx orq
                (remove idx_dec (objIdxOf (getUpLockIdxBackI orq))
                        ost#[dir].(dir_sharers)) /\
              ost#[dir].(dir_sharers) <> nil /\
              SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
              OtherSharerExists ost#[dir] (objIdxOf (getUpLockIdxBackI orq)) /\
              ost#[dir].(dir_st) = msiS)
        :transition
           (!|ost, rq, rsbTo| --> (ost +#[owned <- true],
                                   (remove idx_dec (objIdxOf rsbTo) ost#[dir].(dir_sharers),
                                    <| msiDownRqIS; O |>))).

      Definition liGetMRqUpDownM: Rule :=
        rule.rqud[1~>4~~cidx]
        :accepts msiRqM
        :from cidx
        :me oidx
        :requires
           (fun ost mins =>
              cidx <> ost#[dir].(dir_excl) /\
              In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
              ost#[status] <= msiI /\ ost#[dir].(dir_st) = msiM)
        :transition
           (!|ost, msg| --> ([ost#[dir].(dir_excl)], <| msiDownRqIM; O |>)).

      Definition liGetMRqUpDownS: Rule :=
        rule.rqud[1~>5~~cidx]
        :accepts msiRqM
        :from cidx
        :me oidx
        :requires
           (fun ost mins =>
              ost#[dir].(dir_sharers) <> nil /\
              SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
              OtherSharerExists ost#[dir] cidx /\
              ost#[owned] = true /\ ost#[status] <= msiS /\ ost#[dir].(dir_st) = msiS)
        :transition
           (!|ost, msg| --> (remove idx_dec cidx ost#[dir].(dir_sharers),
                             <| msiDownRqIS; O |>)).

      Definition liDownIRsUpDownS: Rule :=
        rule.rsud[1~>6~>0]
        :accepts msiDownRsIS
        :holding msiRqM
        :requires (fun ost orq mins => ost#[dir].(dir_st) = msiS)
        :transition
           (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirM (objIdxOf rsbTo)],
                 <| msiRsM; O |>)).

      Definition liDownIRsUpDownM: Rule :=
        rule.rsud[1~>6~>1]
        :accepts msiDownRsIM
        :holding msiRqM
        :requires (fun ost orq mins => ost#[dir].(dir_st) = msiM)
        :transition
           (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirM (objIdxOf rsbTo)],
                 <| msiRsM; O |>)).

      Definition liDownIImmS: Rule :=
        rule.immu[1~>7~>0]
        :accepts msiDownRqIS
        :me oidx
        :requires (fun ost orq mins => ost#[dir].(dir_st) = msiI)
        :transition
           (!|ost, min| --> (ost +#[owned <- false]
                                 +#[status <- invalidate ost#[status]],
                             <| msiDownRsIS; O |>)).

      Definition liDownIImmM: Rule :=
        rule.immu[1~>7~>1]
        :accepts msiDownRqIM
        :me oidx
        :requires (fun ost orq mins =>
                     ost#[status] = msiM /\ ost#[dir].(dir_st) = msiI)
        :transition
           (!|ost, min| --> (ost +#[owned <- false]
                                 +#[status <- msiI],
                             <| msiDownRsIM; ost#[val] |>)).

      Definition liDownIRqDownDownDirS: Rule :=
        rule.rqdd[1~>9~>0]
        :accepts msiDownRqIS
        :me oidx
        :requires
           (fun ost mins =>
              ost#[dir].(dir_sharers) <> nil /\
              SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
              ost#[dir].(dir_st) = msiS)
        :transition
           (!|ost, msg| --> (ost#[dir].(dir_sharers), <| msiDownRqIS; O |>)).

      Definition liDownIRqDownDownDirM: Rule :=
        rule.rqdd[1~>9~>1]
        :accepts msiDownRqIM
        :me oidx
        :requires
           (fun ost mins =>
              In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
              ost#[dir].(dir_st) = msiM)
        :transition
           (!|ost, msg| --> ([ost#[dir].(dir_excl)], <| msiDownRqIM; O |>)).

      Definition liDownIRqDownDownDirMS: Rule :=
        rule.rqdd[1~>9~>2]
        :accepts msiDownRqIM
        :me oidx
        :requires
           (fun ost mins =>
              ost#[dir].(dir_sharers) <> nil /\
              SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
              ost#[dir].(dir_st) = msiS)
        :transition
           (!|ost, msg| --> (ost#[dir].(dir_sharers), <| msiDownRqIS; O |>)).

      Definition liDownIRsUpUpS: Rule :=
        rule.rsuu[1~>10~>0]
        :accepts msiDownRsIS
        :holding msiDownRqIS
        :requires (fun _ _ _ => True)
        :transition
           (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirI],
                 <| msiDownRsIS; O |>)).

      Definition liDownIRsUpUpMS: Rule :=
        rule.rsuu[1~>10~>2]
        :accepts msiDownRsIS
        :holding msiDownRqIM
        :requires (fun ost orq mins => ost#[dir].(dir_st) = msiS)
        :transition
           (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirI],
                 <| msiDownRsIM; ost#[val] |>)).

      Definition liDownIRsUpUpM: Rule :=
        rule.rsuuo[1~>10~>1]
        :accepts msiDownRsIM
        :holding msiDownRqIM
        :requires (fun ost orq mins => ost#[dir].(dir_st) = msiM)
        :transition
           (!|ost, idm, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirI],
                 <| msiDownRsIM; msg_value (valOf idm) |>)).

      Definition liInvRqUpUp: Rule :=
        rule.rqsu[2~>0]
        :me oidx
        :requires
           (fun ost => ost#[owned] = false /\
                       msiNP < ost#[status] < msiM /\
                       ost#[dir].(dir_st) = msiI)
        :transition (ost --> <| msiInvRq; O |>).

      (** NOTE: ditto [l1InvRqUpUpWB]; a cache controller should not use this
       * rule when [ost#[owned] = false /\ msiNP < ost#[status] <= msiS];
       * it's meaningless. *)
      Definition liInvRqUpUpWB: Rule :=
        rule.rqsu[2~>1]
        :me oidx
        :requires
           (fun ost =>
              ost#[dir].(dir_st) = msiI /\
              ((ost#[owned] = true /\ msiI < ost#[status]) \/
               (ost#[owned] = false /\ msiNP < ost#[status] <= msiS)))
        :transition (ost --> <| msiInvWRq; ost#[val] |>).

      Definition liInvRsDownDown: Rule :=
        rule.rsds[2~>2]
        :accepts msiInvRs
        :requires (fun _ _ _ => True)
        :transition (!|ost, _| --> (ost +#[owned <- false]
                                        +#[status <- msiNP])).

      Definition liInvImmI: Rule :=
        rule.immd[2~>5~~cidx]
        :accepts msiInvRq
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[dir] = msiI)
        :transition
           (!|ost, _| --> (ost, <| msiInvRs; O |>)).

      Definition liInvImmS00: Rule :=
        rule.immd[2~>6~>0~>0~~cidx]
        :accepts msiInvRq
        :from cidx
        :requires
           (fun ost orq mins =>
              ost#[owned] = false /\
              getDir cidx ost#[dir] = msiS /\ LastSharer ost#[dir] cidx)
        :transition
           (!|ost, _| --> (ost +#[dir <- setDirI], <| msiInvRs; O |>)).

      Definition liInvImmS01: Rule :=
        rule.immd[2~>6~>0~>1~~cidx]
        :accepts msiInvRq
        :from cidx
        :requires
           (fun ost orq mins =>
              ost#[owned] = true /\ ost#[status] = msiS /\
              getDir cidx ost#[dir] = msiS /\ LastSharer ost#[dir] cidx)
        :transition
           (!|ost, _| --> (ost +#[status <- msiM]
                               +#[dir <- setDirI], <| msiInvRs; O |>)).

      Definition liInvImmS1: Rule :=
        rule.immd[2~>6~>1~~cidx]
        :accepts msiInvRq
        :from cidx
        :requires
           (fun ost orq mins =>
              getDir cidx ost#[dir] = msiS /\ NotLastSharer ost#[dir])
        :transition
           (!|ost, _| --> (ost +#[dir <- removeSharer cidx ost#[dir]],
                           <| msiInvRs; O |>)).

      Definition liInvImmWBI: Rule :=
        rule.immd[2~>7~~cidx]
        :accepts msiInvWRq
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[dir] = msiI)
        :transition
           (!|ost, _| --> (ost, <| msiInvRs; O |>)).

      Definition liInvImmWBS1: Rule :=
        rule.immd[2~>8~>1~~cidx]
        :accepts msiInvWRq
        :from cidx
        :requires
           (fun ost orq mins =>
              getDir cidx ost#[dir] = msiS /\ NotLastSharer ost#[dir])
        :transition
           (!|ost, _| --> (ost +#[dir <- removeSharer cidx ost#[dir]],
                           <| msiInvRs; O |>)).

      Definition liInvImmWBM: Rule :=
        rule.immd[2~>10~~cidx]
        :accepts msiInvWRq
        :from cidx
        :requires (fun ost orq mins => getDir cidx ost#[dir] = msiM)
        :transition
           (!|ost, msg| --> (ost +#[dir <- setDirI]
                                 +#[owned <- true]
                                 +#[status <- msiM]
                                 +#[val <- msg_value msg],
                             <| msiInvRs; O |>)).

      Definition liBInvRqS: Rule :=
        rule.rqsd[3~>0~>0]
        :requires
           (fun ost =>
              ost#[dir].(dir_sharers) <> nil /\
              SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
              ost#[dir].(dir_st) = msiS)
        :transition (ost --> (ost#[dir].(dir_sharers), <| msiDownRqIS; O |>)).

      Definition liBInvRqM: Rule :=
        rule.rqsd[3~>0~>1]
        :requires
           (fun ost =>
              In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
              ost#[dir].(dir_st) = msiM)
        :transition (ost --> ([ost#[dir].(dir_excl)], <| msiDownRqIM; O |>)).

      Definition liBInvRsS0: Rule :=
        rule.rsus[3~>1~>0]
        :accepts msiDownRsIS
        :requires
           (fun ost orq mins => ost#[owned] = false /\ ost#[dir].(dir_st) = msiS)
        :transition (!|ost, _| --> (ost +#[dir <- setDirI])).

      Definition liBInvRsS1: Rule :=
        rule.rsus[3~>1~>1]
        :accepts msiDownRsIS
        :requires
           (fun ost orq mins => ost#[owned] = true /\ ost#[dir].(dir_st) = msiS)
        :transition (!|ost, _| --> (ost +#[dir <- setDirI]
                                        +#[status <- msiM])).

      Definition liBInvRsM: Rule :=
        rule.rsuso[3~>1~>2]
        :accepts msiDownRsIM
        :requires
           (fun ost orq mins => ost#[dir].(dir_st) = msiM)
        :transition (!|ost, idm| --> (ost +#[dir <- setDirI]
                                          +#[owned <- true]
                                          +#[status <- msiM]
                                          +#[val <- msg_value (valOf idm)])).

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
             l1GetSRsDownDown; l1DownSImm oidx;
             (** rules involved with [GetM] *)
             l1GetMImm eidx;
             l1GetMRqUpUp oidx eidx;
             l1GetMRsDownDown; l1DownIImmS oidx; l1DownIImmM oidx;
             (** rules involved with [Put] *)
             l1InvRqUpUp oidx; l1InvRqUpUpWB oidx; l1InvRsDownDown];
           obj_rules_valid := _ |}.
      Next Obligation.
        inds_valid_tac.
      Qed.

    End L1.

    Definition liRulesFromChild (cidx: IdxT): list Rule :=
      [liGetSImmS cidx; liGetSImmM cidx; liGetSRqUpUp oidx cidx;
      liGetSRqUpDownM oidx cidx; liGetMImm cidx; liGetMRqUpUp oidx cidx;
      liGetMRqUpDownM oidx cidx; liGetMRqUpDownS oidx cidx;
      liInvImmI cidx; liInvImmS00 cidx; liInvImmS01 cidx; liInvImmS1 cidx;
      liInvImmWBI cidx; liInvImmWBS1 cidx; liInvImmWBM cidx].

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
             ++ [liGetSRsDownDown; liDownSRsUpDownM;
                liDownSImm oidx; liDownSRqDownDownM oidx; liDownSRsUpUp]
             (** rules involved with [GetM] *)
             ++ [liGetMRsDownDownDirI; liGetMRsDownRqDownDirS oidx;
                liDownIRsUpDownS; liDownIRsUpDownM;
                liDownIImmS oidx; liDownIImmM oidx;
                liDownIRqDownDownDirS oidx; liDownIRqDownDownDirM oidx;
                liDownIRqDownDownDirMS oidx;
                liDownIRsUpUpS; liDownIRsUpUpM; liDownIRsUpUpMS]
             (** rules involved with [Put] *)
             ++ [liInvRqUpUp oidx; liInvRqUpUpWB oidx; liInvRsDownDown]
             (** rules involved with [BInv] *)
             ++ [liBInvRqS oidx; liBInvRqM oidx; liBInvRsS0; liBInvRsS1; liBInvRsM];
         obj_rules_valid := _ |}.
    Next Obligation.
      solve_inds_NoDup disc_child_inds_disj.
    Qed.

    Definition memRulesFromChild (cidx: IdxT): list Rule :=
      [liGetSImmM cidx; liGetMImm cidx; liInvImmWBM cidx].

    Definition memRulesFromChildren (coinds: list IdxT): list Rule :=
      List.concat (map memRulesFromChild coinds).

    Hint Unfold memRulesFromChild memRulesFromChildren: RuleConds.

    Program Definition mem: Object :=
      {| obj_idx := oidx;
         obj_rules := memRulesFromChildren (subtreeChildrenIndsOf topo oidx);
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

Hint Unfold l1GetSImm l1GetSRqUpUp l1GetSRsDownDown
     l1DownSImm l1GetMImm l1GetMRqUpUp l1GetMRsDownDown
     l1DownIImmS l1DownIImmM l1InvRqUpUp l1InvRqUpUpWB l1InvRsDownDown: MsiRules.

Hint Unfold liGetSImmS liGetSImmM
     liGetSRqUpUp liGetSRsDownDown
     liGetSRqUpDownM liDownSRsUpDownM
     liDownSImm liDownSRqDownDownM liDownSRsUpUp
     liGetMImm liGetMRqUpUp liGetMRsDownDownDirI liGetMRsDownRqDownDirS
     liGetMRqUpDownM liGetMRqUpDownS liDownIRsUpDownS liDownIRsUpDownM
     liDownIImmS liDownIImmM liDownIRqDownDownDirS liDownIRqDownDownDirM liDownIRqDownDownDirMS
     liDownIRsUpUpS liDownIRsUpUpM liDownIRsUpUpMS
     liInvRqUpUp liInvRqUpUpWB liInvRsDownDown
     liInvImmI liInvImmS00 liInvImmS01 liInvImmS1
     liInvImmWBI liInvImmWBS1 liInvImmWBM
     liBInvRqS liBInvRqM liBInvRsS0 liBInvRsS1 liBInvRsM: MsiRules.
