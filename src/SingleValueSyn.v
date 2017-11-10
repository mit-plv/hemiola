Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics.
Require Import StepDet StepSeq Serial Predicate Synthesis.

Require Import SingleValue SingleValueSim.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section Impl.
  Variables extIdx1 extIdx2: nat.
  Hypotheses (Hiext1: isExternal (impl0 extIdx1 extIdx2) extIdx1 = true)
             (Hiext2: isExternal (impl0 extIdx1 extIdx2) extIdx2 = true)
             (Hsext1: isExternal (spec extIdx1 extIdx2) extIdx1 = true)
             (Hsext2: isExternal (spec extIdx1 extIdx2) extIdx2 = true).

  Local Definition spec := spec extIdx1 extIdx2.
  Local Definition specObj := specObj extIdx1 extIdx2.
  Local Definition impl0 := impl0 extIdx1 extIdx2.
  Local Definition svmP := svmP extIdx1 extIdx2.

  (** First, prove that the initial system is provided properly. *)
  Theorem impl0_ok: SynthOk spec SvmSim svmP impl0.
  Proof.
    repeat split.
    - admit.
    - repeat econstructor.
    - admit.
  Admitted.
  
  Section SynStep.

    Local Definition targetObjIdx := child1Idx.
    Local Definition targetTrsIdx := 0.

    Ltac get_target_trs impl oidx tidx :=
      let oobj := (eval cbn in (nth_error (sys_objs impl) oidx)) in
      match oobj with
      | Some ?obj =>
        let otrs := (eval cbn in (nth_error (obj_trs obj) tidx)) in
        match otrs with
        | Some ?trs => exact trs
        end
      end.

    Ltac cbner t := let ct := (eval cbn in t) in exact ct.

    Ltac get_precond trs :=
      cbner (pmsg_precond trs).
    
    Local Definition targetTrs: PMsg :=
      ltac:(get_target_trs impl0 targetObjIdx targetTrsIdx).

    Local Definition targetMid: MsgId := pmsg_mid targetTrs.
    Local Definition targetSpecMid := svmMsgIdF extIdx1 extIdx2 targetMid.
    Local Definition targetPrec: PreCond := ltac:(get_precond targetTrs).

    Ltac mv_rewriter :=
      repeat
        match goal with
        | [H: Some _ = M.find _ _ |- _] => apply eq_sym in H
        | [H: None = M.find _ _ |- _] => apply eq_sym in H
        | [H1: M.find ?m ?k1 = Some _, H2: M.find ?m ?k2 = Some _ |- _] =>
          rewrite H1 in H2; inv H2
        | [H1: M.find ?m ?k1 = Some _, H2: M.find ?m ?k2 = None |- _] =>
          rewrite H1 in H2; discriminate
        end.

    (* If it succeeds, then provably [inv1] and [inv2] are not compatible 
     * for all state.
     * If it fails, then there's no information.
     *)
    Ltac inv_not_compatible inv1 inv2 :=
      let Hnc := fresh "Hnc" in
      assert (forall st, inv1 st -> inv2 st -> False)
        as Hnc by (cbn; intros; dest; intuition mv_rewriter);
      clear Hnc.

    Ltac find_new_prec cprec invs :=
      match invs with
      | nil => fail
      | ?inv :: ?invs' =>
        tryif (inv_not_compatible cprec inv)
        then (exact inv)
        else find_new_prec cprec invs'
      end.

    Local Definition newPrec: PreCond :=
      ltac:(let tgt := (eval hnf in targetPrec) in
            let invs := (eval hnf in svmImplChild1Inv) in
            find_new_prec tgt invs).

    (* Ltac find_state_sim oidx oinv sims := *)
    (*   match sims with *)
    (*   | nil => fail *)
    (*   | ?sim :: ?sims' => *)
    (*     tryif (inv_not_compatible oinv *)
    (*                               (fun iost => exists ist sst, *)
    (*                                    ist@[oidx] = Some iost /\ sim ist sst)) *)
    (*     then find_state_sim oidx oinv sims' *)
    (*     else exact sim *)
    (*   end. *)

    (* Local Definition newStateInv: ObjectStates -> ObjectStates -> Prop := *)
    (*   ltac:(let tgt := (eval hnf in newPrec) in *)
    (*         let sims := (eval hnf in svmR) in *)
    (*         find_state_sim child1Idx tgt sims). *)

    (* Local Definition targetStateInv: ObjectStates -> ObjectStates -> Prop := *)
    (*   ltac:(let tgt := (eval hnf in targetPrec) in *)
    (*         let sims := (eval hnf in svmR) in *)
    (*         find_state_sim child1Idx tgt sims). *)

    Local Definition synTrs:
      { impl1: System &
               SynthOk spec SvmSim svmP impl1 }.
    Proof.
    Abort.
    
    (* Ltac no_vloc_st oss oidx kidx := *)
    (*   lazymatch goal with *)
    (*   | [vloc := (oss, VFromState oidx kidx, _) |- _] => fail *)
    (*   | _ => idtac *)
    (*   end. *)

    (* (* NOTE: there's only one [VFromMsg] information per a transaction. *) *)
    (* Ltac no_vloc_msg := *)
    (*   lazymatch goal with *)
    (*   | [vloc := (VFromMsg, _) |- _] => fail *)
    (*   | _ => idtac *)
    (*   end. *)

    (* Ltac collect_vloc := *)
    (*   repeat *)
    (*     match goal with *)
    (*     | [H1: M.find ?oidx ?oss = Some ?ost, H2: M.find ?kidx (ost_st ?ost) = Some ?v |- _] => *)
    (*       no_vloc_st oss oidx kidx; *)
    (*       let vloc := fresh "vloc" in *)
    (*       set (oss, VFromState oidx kidx, v) as vloc *)
    (*     | [H: pmsg_postcond _ _ ?v _ |- _] => *)
    (*       no_vloc_msg; *)
    (*       let vloc := fresh "vloc" in *)
    (*       set (VFromMsg, v) as vloc *)
    (*     end. *)

    (* Ltac simpl_postcond := *)
    (*   repeat *)
    (*     match goal with *)
    (*     | [H: pmsg_postcond _ _ _ _ |- _] => simpl in H; mv_rewriter *)
    (*     end. *)

    (* Ltac no_diff sdf := *)
    (*   lazymatch goal with *)
    (*   | [df := sdf |- _] => fail *)
    (*   | _ => idtac *)
    (*   end. *)

    (* Ltac collect_diff oss1 oss2 := *)
    (*   repeat *)
    (*     match goal with *)
    (*     | [vloc := (oss2, ?wh, ?v) |- _] => *)
    (*       is_pure_const v; *)
    (*       no_diff (ConstDiff wh v); *)
    (*       let df := fresh "df" in *)
    (*       pose (ConstDiff wh v) as df *)
    (*     | [vloc1 := (oss1, ?wh1, ?v), vloc2 := (oss2, ?wh2, ?v) |- _] => *)
    (*       not_pure_const v; *)
    (*       first [is_equal wh1 wh2 | *)
    (*              no_diff (VMoved wh1 wh2); *)
    (*              let df := fresh "df" in *)
    (*              pose (VMoved wh1 wh2) as df] *)
    (*     end. *)

    
  End SynStep.

End Impl.

