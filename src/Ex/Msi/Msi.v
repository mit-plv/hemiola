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
 * - Non-inclusive
 *)

Section System.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo := fst (tree2Topo tr 0).
  Let cifc := snd (tree2Topo tr 0).

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

  Section Rules.
    Variables (oidx cidx: IdxT).

    Section L1.
      (** NOTE: [cidx] will be instantiated to [l1ExtOf oidx]. *)

      Definition l1GetSImm: Rule :=
        rule 0~>0 from template immd {
        receive Spec.getRq from cidx;
        assert (fun ost orq mins => msiS <= ost#[status]);
        (!|ost, _| --> (ost, <| Spec.getRs; ost#[val] |>))
      }.

      Definition l1GetSRqUpUp: Rule :=
        rule 0~>1 from template rquu {
          receive Spec.getRq from cidx to oidx;
          assert (fun ost mins => ost#[status] <= msiI);
          (!|ost, msg| --> <| msiRqS; O |>)
      }.

      Definition l1GetSRsDownDown: Rule :=
        rule 0~>2 from template rsdd {
          receive msiRsS;
          hold Spec.getRq;
          assert (fun _ _ _ => True);
          (!|ost, min, rq, rsbTo|
            --> (ost +#[val <- msg_value min]
                     +#[status <- msiS],
                  <| Spec.getRs; msg_value min |>))
      }.

      Definition l1DownSImm: Rule :=
        rule 0~>3 from template immu {
          receive msiDownRqS to oidx;
          assert (fun ost orq mins => msiS <= ost#[status]);
          (!|ost, min| --> (ost +#[owned <- false]
                                +#[status <- msiS],
                             <| msiDownRsS; ost#[val] |>))
      }.

      Definition l1GetMImm: Rule :=
        rule 1~>0 from template immd {
          receive Spec.setRq from cidx;
          assert
            (fun ost orq mins =>
               ost#[owned] = true /\ ost#[status] = msiM);
          (!|ost, msg| --> (ost +#[val <- msg_value msg], <| Spec.setRs; O |>))
      }.

      Definition l1GetMRqUpUp: Rule :=
        rule 1~>1 from template rquu {
          receive Spec.setRq from cidx to oidx;
          assert (fun ost mins => ost#[status] <= msiS);
          (!|ost, msg| --> <| msiRqM; O |>)
      }.

      Definition l1GetMRsDownDown: Rule :=
        rule 1~>2 from template rsdd {
          receive msiRsM;
          hold Spec.setRq;
          assert (fun _ _ _ => True);
          (!|ost, min, rq, rsbTo|
            --> (ost +#[status <- msiM]
                     +#[owned <- true]
                     +#[val <- msg_value rq],
                  <| Spec.setRs; O |>))
      }.

      Definition l1DownIImmS: Rule :=
        rule 1~>3~>0 from template immu {
          receive msiDownRqIS to oidx;
          assert (fun _ _ _ => True);
          (!|ost, min| --> (ost +#[owned <- false]
                                +#[status <- invalidate ost#[status]],
                             <| msiDownRsIS; O |>))
      }.

      Definition l1DownIImmM: Rule :=
        rule 1~>3~>1 from template immu {
          receive msiDownRqIM to oidx;
          assert (fun ost orq mins => ost#[status] = msiM);
          (!|ost, min| --> (ost +#[owned <- false]
                                +#[status <- invalidate ost#[status]],
                             <| msiDownRsIM; O |>))
      }.

      Definition l1InvRqUpUp: Rule :=
        rule 2~>0 from template rqsu {
          to oidx;
          assert (fun ost => ost#[owned] = false /\ msiNP < ost#[status] < msiM);
          (ost --> <| msiInvRq; O |>)
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
          assert (fun ost => msiNP < ost#[status]);
          (ost --> <| msiInvWRq; ost#[val] |>)
      }.

      Definition l1InvRsDownDown: Rule :=
        rule 2~>2 from template rsds {
          receive msiInvRs;
          assert (fun _ _ _ => True);
          (!|ost, _| --> (ost +#[owned <- false]
                              +#[status <- msiNP]))
      }.

    End L1.

    Section Li.

      Definition liGetSImmS: Rule :=
        rule 0~>0~>0~~cidx from template immd {
          receive msiRqS from cidx;
          assert
            (fun ost orq mins =>
               ost#[dir].(dir_st) <= msiS /\ ost#[status] = msiS);
          (!|ost, _| --> (ost +#[dir <- addSharer cidx ost#[dir]],
                           <| msiRsS; ost#[val] |>))
      }.

      (** NOTE: it is important to note that the "owned" bit is not changed. *)
      Definition liGetSImmM: Rule :=
        rule 0~>0~>1~~cidx from template immd {
          receive msiRqS from cidx;
          assert
            (fun ost orq mins =>
               ost#[status] = msiM /\ ost#[dir].(dir_st) = msiI);
          (!|ost, _| --> (ost +#[status <- msiS]
                              +#[dir <- setDirS [cidx]],
                           <| msiRsS; ost#[val] |>))
      }.

      Definition liGetSRqUpUp: Rule :=
        rule 0~>1~~cidx from template rquu {
          receive msiRqS from cidx to oidx;
          assert
            (fun ost mins =>
               ost#[owned] = false /\
               ost#[status] <= msiI /\ ost#[dir].(dir_st) <= msiS);
          (!|ost, msg| --> <| msiRqS; O |>)
      }.

      Definition liGetSRsDownDown: Rule :=
        rule 0~>2~>0 from template rsdd {
          receive msiRsS;
          hold msiRqS;
          assert (fun _ _ _ => True);
          (!|ost, min, rq, rsbTo|
            --> (ost +#[val <- msg_value min]
                     +#[owned <- false]
                     +#[status <- msiS]
                     +#[dir <- addSharer (objIdxOf rsbTo) ost#[dir]],
                  <| msiRsS; msg_value min |>))
      }.

      Definition liGetSRqUpDownM: Rule :=
        rule 0~>3~~cidx from template rqud {
          receive msiRqS from cidx to oidx;
          assert
            (fun ost mins =>
               cidx <> ost#[dir].(dir_excl) /\
               In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
               ost#[status] <= msiI /\ ost#[dir].(dir_st) = msiM);
          (!|ost, msg| --> ([ost#[dir].(dir_excl)], <| msiDownRqS; O |>))
      }.

      Definition liDownSRsUpDownM: Rule :=
        rule 0~>4 from template rsudo {
          receive msiDownRsS;
          hold msiRqS;
          assert (fun _ _ _ => True);
          (!|ost, idm, rq, rsbTo|
            --> (ost +#[owned <- true]
                     +#[val <- msg_value (valOf idm)]
                     +#[status <- msiS]
                     +#[dir <- setDirS [objIdxOf rsbTo; objIdxOf (idOf idm)]],
                  <| msiRsS; msg_value (valOf idm) |>))
      }.

      (** NOTE:
       * 1) data should be sent along with [msiDownRsS], even when the status
       * is S, since the parent might not have the up-to-date data (e.g., when
       * the line is evicted).
       * 2) when the status is S, it should be the owner since it previously had
       * the status M.
       *)
      Definition liDownSImm: Rule :=
        rule 0~>5 from template immu {
          receive msiDownRqS to oidx;
          assert
            (fun ost orq mins =>
               msiS <= ost#[status] /\ ost#[dir].(dir_st) <= msiS);
          (!|ost, min| --> (ost +#[owned <- false]
                                +#[status <- msiS],
                             <| msiDownRsS; ost#[val] |>))
      }.

      Definition liDownSRqDownDownM: Rule :=
        rule 0~>6 from template rqdd {
          receive msiDownRqS to oidx;
          assert
            (fun ost mins =>
               In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
               ost#[status] <= msiI /\ ost#[dir].(dir_st) = msiM);
          (!|ost, msg| --> ([ost#[dir].(dir_excl)], <| msiDownRqS; O |>))
      }.

      Definition liDownSRsUpUp: Rule :=
        rule 0~>7 from template rsuuo {
          receive msiDownRsS;
          hold msiDownRqS;
          assert (fun _ _ _ => True);
          (!|ost, idm, rq, rsbTo|
            --> (ost +#[val <- msg_value (valOf idm)]
                     +#[owned <- false]
                     +#[status <- msiS]
                     +#[dir <- setDirS [objIdxOf (idOf idm)]],
                  <| msiDownRsS; msg_value (valOf idm) |>))
      }.

      Definition liGetMImm: Rule :=
        rule 1~>0~~cidx from template immd {
          receive msiRqM from cidx;
          assert
            (fun ost orq mins =>
               ost#[status] = msiM \/
               (ost#[status] = msiS /\ ost#[owned] = true /\
                ost#[dir].(dir_st) = msiS /\ LastSharer ost#[dir] cidx));
          (!|ost, msg| --> (ost +#[owned <- false]
                                +#[status <- msiI]
                                +#[dir <- setDirM cidx],
                             <| msiRsM; O |>))
      }.

      Definition liGetMRqUpUp: Rule :=
        rule 1~>1~~cidx from template rquu {
          receive msiRqM from cidx to oidx;
          assert
            (fun ost mins =>
               ost#[owned] = false /\
               ost#[status] <= msiS /\ ost#[dir].(dir_st) <= msiS);
          (!|ost, msg| --> <| msiRqM; O |>)
      }.

      (** This is the case where it's possible to directly respond a [msiRsM]
       * message back since there are no internal sharers to invalidate.
       *)
      Definition liGetMRsDownDownDirI: Rule :=
        rule 1~>2 from template rsdd {
          receive msiRsM;
          hold msiRqM;
          assert
            (fun ost orq mins =>
               ost#[dir].(dir_st) = msiI \/
               (ost#[dir].(dir_st) = msiS /\
               LastSharer ost#[dir] (objIdxOf (getUpLockIdxBackI orq))));
          (!|ost, min, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirM (objIdxOf rsbTo)],
                  <| msiRsM; O |>))
      }.

      (** This is the case where internal invalidation is required
       * due to sharers.
       *)
      Definition liGetMRsDownRqDownDirS: Rule :=
        rule 1~>3 from template rsrq {
          receive msiRsM to oidx;
          hold msiRqM;
          assert
            (fun ost orq mins =>
               RsDownRqDownSoundPrec
                 topo oidx orq
                 (remove idx_dec (objIdxOf (getUpLockIdxBackI orq))
                         ost#[dir].(dir_sharers)) /\
               ost#[dir].(dir_sharers) <> nil /\
               SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
               OtherSharerExists ost#[dir] (objIdxOf (getUpLockIdxBackI orq)) /\
               ost#[dir].(dir_st) = msiS);
          (!|ost, rq, rsbTo| --> (ost +#[owned <- true],
                                   (remove idx_dec (objIdxOf rsbTo) ost#[dir].(dir_sharers),
                                     <| msiDownRqIS; O |>)))
      }.

      Definition liGetMRqUpDownM: Rule :=
        rule 1~>4~~cidx from template rqud {
          receive msiRqM from cidx to oidx;
          assert
            (fun ost mins =>
               cidx <> ost#[dir].(dir_excl) /\
               In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
               ost#[status] <= msiI /\ ost#[dir].(dir_st) = msiM);
          (!|ost, msg| --> ([ost#[dir].(dir_excl)], <| msiDownRqIM; O |>))
      }.

      Definition liGetMRqUpDownS: Rule :=
        rule 1~>5~~cidx from template rqud {
          receive msiRqM from cidx to oidx;
          assert
            (fun ost mins =>
               ost#[dir].(dir_sharers) <> nil /\
               SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
               OtherSharerExists ost#[dir] cidx /\
               ost#[owned] = true /\ ost#[status] <= msiS /\ ost#[dir].(dir_st) = msiS);
          (!|ost, msg| --> (remove idx_dec cidx ost#[dir].(dir_sharers),
                             <| msiDownRqIS; O |>))
      }.

      Definition liDownIRsUpDownS: Rule :=
        rule 1~>6~>0 from template rsud {
          receive msiDownRsIS;
          hold msiRqM;
          assert (fun ost orq mins => ost#[dir].(dir_st) = msiS);
          (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirM (objIdxOf rsbTo)],
                  <| msiRsM; O |>))
      }.

      Definition liDownIRsUpDownM: Rule :=
        rule 1~>6~>1 from template rsud {
          receive msiDownRsIM;
          hold msiRqM;
          assert (fun ost orq mins => ost#[dir].(dir_st) = msiM);
          (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirM (objIdxOf rsbTo)],
                  <| msiRsM; O |>))
      }.

      Definition liDownIImmS: Rule :=
        rule 1~>7~>0 from template immu {
          receive msiDownRqIS to oidx;
          assert (fun ost orq mins => ost#[dir].(dir_st) = msiI);
          (!|ost, min| --> (ost +#[owned <- false]
                                +#[status <- invalidate ost#[status]],
                             <| msiDownRsIS; O |>))
        }.

      Definition liDownIImmM: Rule :=
        rule 1~>7~>1 from template immu {
          receive msiDownRqIM to oidx;
          assert (fun ost orq mins =>
                     ost#[status] = msiM /\ ost#[dir].(dir_st) = msiI);
          (!|ost, min| --> (ost +#[owned <- false]
                                +#[status <- msiI],
                             <| msiDownRsIM; O |>))
      }.

      Definition liDownIRqDownDownDirS: Rule :=
        rule 1~>9~>0 from template rqdd {
          receive msiDownRqIS to oidx;
          assert
            (fun ost mins =>
               ost#[dir].(dir_sharers) <> nil /\
               SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
               ost#[dir].(dir_st) = msiS);
          (!|ost, msg| --> (ost#[dir].(dir_sharers), <| msiDownRqIS; O |>))
      }.

      Definition liDownIRqDownDownDirM: Rule :=
        rule 1~>9~>1 from template rqdd {
          receive msiDownRqIM to oidx;
          assert
            (fun ost mins =>
               In ost#[dir].(dir_excl) (subtreeChildrenIndsOf topo oidx) /\
               ost#[dir].(dir_st) = msiM);
          (!|ost, msg| --> ([ost#[dir].(dir_excl)], <| msiDownRqIM; O |>))
      }.

      Definition liDownIRqDownDownDirMS: Rule :=
        rule 1~>9~>2 from template rqdd {
          receive msiDownRqIM to oidx;
          assert
            (fun ost mins =>
               ost#[dir].(dir_sharers) <> nil /\
               SubList ost#[dir].(dir_sharers) (subtreeChildrenIndsOf topo oidx) /\
               ost#[dir].(dir_st) = msiS);
          (!|ost, msg| --> (ost#[dir].(dir_sharers), <| msiDownRqIS; O |>))
      }.

      Definition liDownIRsUpUpS: Rule :=
        rule 1~>10~>0 from template rsuu {
          receive msiDownRsIS;
          hold msiDownRqIS;
          assert (fun _ _ _ => True);
          (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirI],
                  <| msiDownRsIS; O |>))
      }.

      Definition liDownIRsUpUpMS: Rule :=
        rule 1~>10~>2 from template rsuu {
          receive msiDownRsIS;
          hold msiDownRqIM;
          assert (fun ost orq mins => ost#[dir].(dir_st) = msiS);
          (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirI],
                  <| msiDownRsIM; O |>))
      }.

      Definition liDownIRsUpUpM: Rule :=
        rule 1~>10~>1 from template rsuu {
          receive msiDownRsIM;
          hold msiDownRqIM;
          assert (fun ost orq mins => ost#[dir].(dir_st) = msiM);
          (!|ost, mins, rq, rsbTo|
            --> (ost +#[owned <- false]
                     +#[status <- invalidate ost#[status]]
                     +#[dir <- setDirI],
                  <| msiDownRsIM; O |>))
      }.

      Definition liInvRqUpUp: Rule :=
        rule 2~>0 from template rqsu {
          to oidx;
          assert (fun ost => ost#[owned] = false /\
                               msiNP < ost#[status] < msiM /\
                               ost#[dir].(dir_st) = msiI);
          (ost --> <| msiInvRq; O |>)
      }.

      (** NOTE: ditto [l1InvRqUpUpWB]; a cache controller should not use this
       * rule when [owned = false]; it's meaningless.
       *)
      Definition liInvRqUpUpWB: Rule :=
        rule 2~>1 from template rqsu {
          to oidx;
          assert (fun ost =>
                    ost#[dir].(dir_st) = msiI /\
                    ((ost#[owned] = true /\ msiI < ost#[status]) \/
                    (ost#[owned] = false /\ msiNP < ost#[status] <= msiS)));
          (ost --> <| msiInvWRq; ost#[val] |>)
      }.

      Definition liInvRsDownDown: Rule :=
        rule 2~>2 from template rsds {
          receive msiInvRs;
          assert (fun _ _ _ => True);
          (!|ost, _| --> (ost +#[owned <- false]
                              +#[status <- msiNP]))
      }.

      Definition liDropImm: Rule :=
        rule 2~>3 from template imm {
          assert (fun ost orq mins => ost#[status] <= msiS /\ ost#[owned] = false);
          (ost --> ost +#[status <- msiNP])
      }.

      Definition liInvImmI: Rule :=
        rule 2~>5~~cidx from template immd {
          receive msiInvRq from cidx;
          assert (fun ost orq mins => getDir cidx ost#[dir] = msiI);
          (!|ost, _| --> (ost, <| msiInvRs; O |>))
      }.

      Definition liInvImmS00: Rule :=
        rule 2~>6~>0~>0~~cidx from template immd {
          receive msiInvRq from cidx;
          assert
            (fun ost orq mins =>
               ost#[owned] = false /\
               getDir cidx ost#[dir] = msiS /\ LastSharer ost#[dir] cidx);
          (!|ost, _| --> (ost +#[dir <- setDirI], <| msiInvRs; O |>))
      }.

      Definition liInvImmS01: Rule :=
        rule 2~>6~>0~>1~~cidx from template immd {
          receive msiInvRq from cidx;
          assert
            (fun ost orq mins =>
               ost#[owned] = true /\ ost#[status] = msiS /\
               getDir cidx ost#[dir] = msiS /\ LastSharer ost#[dir] cidx);
          (!|ost, _| --> (ost +#[status <- msiM]
                              +#[dir <- setDirI], <| msiInvRs; O |>))
      }.

      Definition liInvImmS1: Rule :=
        rule 2~>6~>1~~cidx from template immd {
          receive msiInvRq from cidx;
          assert
            (fun ost orq mins =>
               getDir cidx ost#[dir] = msiS /\ NotLastSharer ost#[dir]);
          (!|ost, _| --> (ost +#[dir <- removeSharer cidx ost#[dir]],
                           <| msiInvRs; O |>))
      }.

      Definition liInvImmWBI: Rule :=
        rule 2~>7~~cidx from template immd {
          receive msiInvWRq from cidx;
          assert (fun ost orq mins => getDir cidx ost#[dir] = msiI);
          (!|ost, _| --> (ost, <| msiInvRs; O |>))
      }.

      Definition liInvImmWBS0: Rule :=
        rule 2~>8~>0~~cidx from template immd {
          receive msiInvWRq from cidx;
          assert
            (fun ost orq mins =>
               ost#[owned] = false /\
               getDir cidx ost#[dir] = msiS /\ LastSharer ost#[dir] cidx);
          (!|ost, _| --> (ost +#[dir <- setDirI], <| msiInvRs; O |>))
      }.

      Definition liInvImmWBS1: Rule :=
        rule 2~>8~>1~~cidx from template immd {
          receive msiInvWRq from cidx;
          assert
            (fun ost orq mins =>
               getDir cidx ost#[dir] = msiS /\ NotLastSharer ost#[dir]);
          (!|ost, _| --> (ost +#[dir <- removeSharer cidx ost#[dir]],
                           <| msiInvRs; O |>))
      }.

      Definition liInvImmWBS: Rule :=
        rule 2~>9~~cidx from template immd {
          receive msiInvWRq from cidx;
          assert
            (fun ost orq mins =>
               ost#[owned] = true /\ ost#[status] = msiS /\
               getDir cidx ost#[dir] = msiS /\ LastSharer ost#[dir] cidx);
          (!|ost, msg| --> (ost +#[status <- msiM]
                                +#[dir <- setDirI], <| msiInvRs; O |>))
      }.

      Definition liInvImmWBM: Rule :=
        rule 2~>10~~cidx from template immd {
          receive msiInvWRq from cidx;
          assert (fun ost orq mins => getDir cidx ost#[dir] = msiM);
          (!|ost, msg| --> (ost +#[dir <- setDirI]
                                +#[owned <- true]
                                +#[status <- msiM]
                                +#[val <- msg_value msg],
                             <| msiInvRs; O |>))
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
      liInvImmWBI cidx; liInvImmWBS0 cidx; liInvImmWBS1 cidx;
      liInvImmWBS cidx; liInvImmWBM cidx].

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
             ++ [liInvRqUpUp oidx; liInvRqUpUpWB oidx; liInvRsDownDown; liDropImm];
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

#[global] Hint Unfold l1GetSImm l1GetSRqUpUp l1GetSRsDownDown
 l1DownSImm l1GetMImm l1GetMRqUpUp l1GetMRsDownDown
 l1DownIImmS l1DownIImmM l1InvRqUpUp l1InvRqUpUpWB l1InvRsDownDown: MsiRules.

#[global] Hint Unfold liGetSImmS liGetSImmM
 liGetSRqUpUp liGetSRsDownDown
 liGetSRqUpDownM liDownSRsUpDownM
 liDownSImm liDownSRqDownDownM liDownSRsUpUp
 liGetMImm liGetMRqUpUp liGetMRsDownDownDirI liGetMRsDownRqDownDirS
 liGetMRqUpDownM liGetMRqUpDownS liDownIRsUpDownS liDownIRsUpDownM
 liDownIImmS liDownIImmM liDownIRqDownDownDirS liDownIRqDownDownDirM liDownIRqDownDownDirMS
 liDownIRsUpUpS liDownIRsUpUpM liDownIRsUpUpMS
 liInvRqUpUp liInvRqUpUpWB liInvRsDownDown
 liInvImmI liInvImmS00 liInvImmS01 liInvImmS1
 liInvImmWBI liInvImmWBS0 liInvImmWBS1 liInvImmWBS liInvImmWBM liDropImm: MsiRules.
