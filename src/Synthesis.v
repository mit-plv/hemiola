Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics SemFacts.
Require Import StepDet Serial SerialFacts TrsSim Predicate.

Set Implicit Arguments.

Section SimP.

  (** User inputs *)
  Variables
    (impl0 spec: System)
    (R: TState -> TState -> Prop)
    (p: Label -> Label).

  Definition SynthOk (s: System) :=
    R (getStateInit s) (getStateInit spec) /\
    TrsSimulates R p s spec /\
    SerializableSys s.

  Hypothesis (Hinit_ok: SynthOk impl0).

  Section SynthesisStep.

    Definition SynT := System -> System -> Prop.
    Variable syn: SynT.

    (** The synthesizer [syn] should "preserve" three conditions:
     * 1) initial state
     * 2) serializability
     * 3) simulation on sequential semantics
     *)
    Hypotheses (Hsyn_init: forall s s', syn s s' -> getStateInit s' = getStateInit s)
               (Hsyn_serial:
                  forall s, SerializableSys s ->
                            forall s', syn s s' -> SerializableSys s')
               (Hsyn_sim:
                  forall s, TrsSimulates R p s spec ->
                            forall s', syn s s' ->
                                       TrsSimulates R p s' spec).

    Lemma synthOk_refinement:
      forall s, SynthOk s -> steps_det # steps_det |-- s ⊑[p] spec.
    Proof.
      unfold SynthOk; intros; dest.
      eapply refines_trans.
      - apply serializable_seqSteps_refines in H1.
        eassumption.
      - eapply sequential_simulation_implies_refinement; eauto.
    Qed.

    Lemma synthOk_preserved:
      forall s s', SynthOk s -> syn s s' -> SynthOk s'.
    Proof.
      unfold SynthOk; intros; dest.
      repeat split; eauto.
      erewrite Hsyn_init; eauto.
    Qed.

  End SynthesisStep.

End SimP.

Section TrsLocker.

  Definition alwaysLock (trsh: TrsHelper) := trsh = [].

End TrsLocker.

Section SynTrs.
  Variables (trsIdx: IdxT)
            (this: IdxT)
            (trsLocker: TrsHelper -> Prop).

  Definition liftTrsLocker (os: OState): Prop := trsLocker (ost_tst os).

  Definition rqChn: IdxT := 0.
  Definition rsChn: IdxT := 1.

  Definition msgValOut (val: Value) (tochn: IdxT * IdxT) :=
    {| msg_id := {| mid_type := trsIdx;
                    mid_from := this;
                    mid_to := fst tochn;
                    mid_chn := snd tochn |};
       msg_value := val
    |}.

  Section Immediate.

    Definition synImm (prec: PreCond) (rqFrom: IdxT) (postcond: PostCond)
               (valOut: StateT -> Value) :=
      {| pmsg_mid := {| mid_type := trsIdx;
                        mid_from := rqFrom;
                        mid_to := this;
                        mid_chn := rqChn |};
         pmsg_precond := fun ost => prec ost /\ liftTrsLocker ost;
         pmsg_outs := fun st val =>
                        msgValOut (valOut (ost_st st)) (rqFrom, rsChn) :: nil;
         pmsg_postcond := postcond
      |}.

  End Immediate.

  Section RequestFwd.
    Variables (rqFrom: IdxT) (fwds: list IdxT).

    Definition synRqOuts (tochns: list (IdxT * IdxT)) (val: Value) :=
      map (msgValOut val) tochns.

    Definition synRqPostcond (pre: OState) (val: Value) (post: OState) :=
      post = {| ost_st := ost_st pre;
                ost_tst := (ost_tst pre)
                           +[ trsIdx <-
                              {| tst_rqfrom := rqFrom;
                                 tst_rqval := val; (* store the request value *)
                                 tst_rss := map (fun idx => (idx, None)) fwds |}]
             |}.

    Definition synRq (prec: PreCond) :=
      {| pmsg_mid := {| mid_type := trsIdx;
                        mid_from := rqFrom;
                        mid_to := this;
                        mid_chn := rqChn |};
         pmsg_precond := fun pre => prec pre /\ liftTrsLocker pre;
         (* forward the request value *)
         pmsg_outs := fun _ val => synRqOuts (map (fun to => (to, rqChn)) fwds) val;
         pmsg_postcond := synRqPostcond
      |}.

  End RequestFwd.

  Section ResponseBack.
    Variable rsFrom: IdxT.

    Fixpoint markResponded (rss: list (IdxT * option Value)) (rsVal: Value) :=
      match rss with
      | nil => nil
      | (idx, ov) :: rss' =>
        if idx ==n rsFrom
        then (idx, Some rsVal) :: rss'
        else (idx, ov) :: (markResponded rss' rsVal)
      end.

    Definition markRespondedTrs (trsh: TrsHelperUnit) (rsVal: Value) :=
      {| tst_rqfrom := tst_rqfrom trsh;
         tst_rqval := tst_rqval trsh;
         tst_rss := markResponded (tst_rss trsh) rsVal |}.

    Definition Responded (pre: OState) (rsVal: Value) (post: OState) :=
      (ost_tst pre)@[trsIdx] >>=[False]
      (fun preth =>
         (ost_tst post)@[trsIdx] >>=[False]
         (fun postth => postth = markRespondedTrs preth rsVal)).

    Definition allResponded (fwds: list (IdxT * option Value)) :=
      forallb (fun ib => match snd ib with
                         | Some _ => true
                         | _ => false
                         end) fwds.

    (* NOTE: prestate already contains the request value and all the responded
     * values in [TrsHelperUnit], thus we don't need [Value] to define
     * [postcond].
     *)
    Definition WhenAllResponded (postcond: OState -> OState -> Prop)
               (pre: OState) (post: OState) :=
      (ost_tst pre)@[trsIdx] >>=[False]
      (fun trsh =>
         if allResponded (tst_rss trsh)
         then postcond pre post /\
              ost_tst post = M.remove trsIdx (ost_tst pre)
         else True).

    Fixpoint getFwdValue (vals: list (IdxT * option Value)) :=
      match vals with
      | nil => VUnit
      | (_, Some v) :: vals' =>
        match v with
        | VUnit => getFwdValue vals'
        | _ => v
        end
      | (_, None) :: vals' => getFwdValue vals'
      end.

    Definition rsFwdValue (post: OState) :=
      (ost_tst post)@[trsIdx] >>=[VUnit]
      (fun trsh => getFwdValue (tst_rss trsh)).
         
    Definition synRsPostcond (postcond: OState -> OState -> Prop)
               (pre: OState) (val: Value) (post: OState) :=
      exists allResp,
        Responded pre val allResp /\
        WhenAllResponded postcond allResp post.

    Definition synRsOuts (rsOut: StateT -> TrsHelperUnit -> Value) :=
      fun st val =>
        (ost_tst st)@[trsIdx] >>=[nil]
        (fun trsh =>
           let rss := markResponded (tst_rss trsh) val in
           if allResponded rss
           then {| msg_id := {| mid_type := trsIdx;
                                mid_from := this;
                                mid_to := tst_rqfrom trsh;
                                mid_chn := rsChn |};
                   msg_value := rsOut (ost_st st) (markRespondedTrs trsh val)
                |} :: nil
           else nil).

    (* NOTE: [postcond] is a desired postcondition when assuming 
     * the transaction is atomic.
     *)
    Definition synRs (postcond: OState -> OState -> Prop)
               (rsOut: StateT -> TrsHelperUnit -> Value) :=
      {| pmsg_mid := {| mid_type := trsIdx;
                        mid_from := rsFrom;
                        mid_to := this;
                        mid_chn := rsChn |};
         pmsg_precond := T;
         pmsg_outs := synRsOuts rsOut;
         pmsg_postcond := synRsPostcond postcond |}.

  End ResponseBack.

  Section AddPMsgs.

    Definition buildRawObjs (oobs: list Object): list Object :=
      map (fun obj => {| obj_idx := obj_idx obj;
                         obj_state_init := obj_state_init obj;
                         obj_trs := nil |}) oobs.

    Definition buildRawSys (osys: System) :=
      {| sys_objs := buildRawObjs (sys_objs osys);
         sys_chns := sys_chns osys |}.

    Definition addPMsgsO (pmsgs: list PMsg) (obj: Object) :=
      {| obj_idx := obj_idx obj;
         obj_state_init := obj_state_init obj;
         obj_trs :=
           (filter (fun pmsg =>
                      if mid_to (pmsg_mid pmsg) ==n obj_idx obj
                      then true else false) pmsgs)
             ++ obj_trs obj |}.

    Fixpoint addPMsgs (pmsgs: list PMsg) (objs: list Object) :=
      match objs with
      | nil => nil
      | obj :: obs' =>
        (addPMsgsO pmsgs obj) :: (addPMsgs pmsgs obs')
      end.

    Definition addPMsgsSys (pmsgs: list PMsg) (sys: System) :=
      {| sys_objs := addPMsgs pmsgs (sys_objs sys);
         sys_chns := sys_chns sys |}.
    
  End AddPMsgs.

  Definition idxInter (li1 li2: list IdxT): list IdxT :=
    filter (fun idx => if idx ?<n li2 then true else false) li1.
  Definition idxSubtract (li1 li2: list IdxT): list IdxT :=
    filter (fun idx => if idx ?<n li2 then false else true) li1.
  
End SynTrs.

Section VChange.
  
  Inductive VLoc :=
  | VLocState: forall (oidx kidx: IdxT), VLoc
  | VLocMsg: VLoc.

  Inductive VChgConst :=
  | VccIntro: forall (target: VLoc) (const: Value), VChgConst.

  Inductive VChgMove :=
  | VcmIntro: forall (source: VLoc) (targets: list VLoc), VChgMove.

  (* Currently [VChanges] is defined restrictively in that only one 
   * value move is allowed per a transaction.
   *)
  Record VChanges :=
    { vchg_consts: list VChgConst;
      vchg_move: option VChgMove
    }.

  Definition getVLocValue (vloc: VLoc) (oss: ObjectStates) (mval: Value) :=
    match vloc with
    | VLocState oidx kidx =>
      oss@[oidx] >>= (fun ost => (ost_st ost)@[kidx])
    | VLocMsg => Some mval
    end.

  Definition SemVChgConst (vcc: VChgConst)
             (pre post: ObjectStates) (rqV rsV: Value) :=
    match vcc with
    | VccIntro tgt c => getVLocValue tgt post rsV = Some c
    end.

  Definition SemVChgMove (vcm: VChgMove)
             (pre post: ObjectStates) (rqV rsV: Value) :=
    match vcm with
    | VcmIntro src tgts =>
      Forall (fun tgt =>
                match getVLocValue src pre rqV,
                      getVLocValue tgt post rsV with
                | Some sv, Some tv => sv = tv
                | _, _ => False
                end) tgts
    end.

  Definition SemVChanges (vchs: VChanges)
             (pre post: ObjectStates) (rqV rsV: Value) :=
    match vchs with
    | {| vchg_consts := vccs; vchg_move := ovcm |} =>
      Forall (fun vcc => SemVChgConst vcc pre post rqV rsV) vccs /\
      ovcm >>=[True] (fun vcm => SemVChgMove vcm pre post rqV rsV)
    end.

End VChange.

Section SynByVChanges.
  Variables trsIdx: IdxT.

  Section PerTarget.
    Variable targetIdx: IdxT.

    (* Applies only the proper updates in terms of the given [targetIdx] *)
    Fixpoint constUpdatesOf (consts: list VChgConst)
             (pre: StateT) :=
      match consts with
      | nil => pre
      | (VccIntro vloc val) :: chgs' =>
        match vloc with
        | VLocState oidx kidx =>
          if oidx ==n targetIdx
          then constUpdatesOf chgs' (pre +[kidx <- val])
          else constUpdatesOf chgs' pre
        | _ => constUpdatesOf chgs' pre
        end
      end.

    Fixpoint getVLocTarget (tgts: list VLoc) :=
      match tgts with
      | nil => None
      | tgt :: tgts' =>
        match tgt with
        | VLocState oidx kidx =>
          if oidx ==n targetIdx
          then Some kidx
          else getVLocTarget tgts'
        | _ => getVLocTarget tgts'
        end
      end.

    (* Applies only the proper updates in terms of the given [targetIdx] *)
    Definition movedUpdateOf (omv: option VChgMove)
               (rqVal fwdVal: Value) (pre: StateT) :=
      match omv with
      | Some (VcmIntro src tgts) =>
        match getVLocTarget tgts with
        | Some kidx =>
          match src with
          | VLocState _ _ => pre +[kidx <- fwdVal]
          | VLocMsg => pre +[kidx <- rqVal]
          end
        | None => pre
        end
      | None => pre
      end.

    Section Immediate.

      (* If an object handles the request immediately, the only case that
       * it has to send a certain value is when it is the source.
       *)
      Definition valOutVChanges (chgs: VChanges) (pre: StateT): Value :=
        match vchg_move chgs with
        | Some (VcmIntro (VLocState oidx kidx) _) =>
          if oidx ==n targetIdx
          then (pre@[kidx]) >>=[VUnit] (fun val => val)
          else VUnit
        | _ => VUnit
        end.

      Definition vChangesImmUpdatesOf
                 (consts: list VChgConst) (mv: option VChgMove)
                 (rqVal: Value) :=
        fun pre post =>
          (ost_tst pre)@[trsIdx] >>=[False]
          (fun trsh =>
             ost_st post = movedUpdateOf
                             mv rqVal rqVal
                             (constUpdatesOf consts (ost_st pre))).

      Definition postcondImmVChanges (chgs: VChanges) (rqVal: Value) :=
        vChangesImmUpdatesOf (vchg_consts chgs)
                             (vchg_move chgs)
                             rqVal.

      Definition synImmVChanges (rqFrom: IdxT) (prec: PreCond) (chgs: VChanges) :=
        synImm trsIdx targetIdx alwaysLock prec
               rqFrom
               (fun pre val post => postcondImmVChanges chgs val pre post)
               (valOutVChanges chgs).
      
    End Immediate.

    Section RequestFwd.

      Definition synRqVChanges (rqFrom: IdxT) (fwds: list IdxT) (prec: PreCond) :=
        synRq trsIdx targetIdx alwaysLock rqFrom fwds prec.

    End RequestFwd.

    Section ResponseBack.

      Definition vChangesRsUpdatesOf (consts: list VChgConst)
                 (mv: option VChgMove) :=
        fun pre post =>
          (ost_tst pre)@[trsIdx] >>=[False]
          (fun trsh =>
             ost_st post = movedUpdateOf
                             mv (tst_rqval trsh) (getFwdValue (tst_rss trsh))
                             (constUpdatesOf consts (ost_st pre))).

      Definition postcondRsVChanges (chgs: VChanges) :=
        vChangesRsUpdatesOf (vchg_consts chgs)
                            (vchg_move chgs).

      Definition rsOutsVChanges (vmoved: option VChgMove)
                 (pre: StateT) (trsh: TrsHelperUnit) :=
        match vmoved with
        | Some (VcmIntro (VLocState oidx kidx) _) =>
          if oidx ==n targetIdx
          then (pre@[kidx]) >>=[VUnit] (fun val => val)
          else VUnit
        | _ =>
          (* Forward the value even after it reaches the destination. *)
          getFwdValue (tst_rss trsh)
        end.

      Definition synRsVChanges (rsFrom: IdxT) (chgs: VChanges) :=
        synRs trsIdx targetIdx rsFrom 
              (postcondRsVChanges chgs)
              (rsOutsVChanges (vchg_move chgs)).

    End ResponseBack.

  End PerTarget.

  Section GivenVChanges.
    Variables (topo: list Channel)
              (chgs: VChanges)
              (erqFrom: IdxT).

    Inductive SynVChanges:
      list (IdxT * IdxT) (* currently synthesizing object index pairs (from, to) *) ->
      list IdxT (* synthesized object indices *) ->
      list PMsg (* synthesized [PMsg]s *) ->
      Prop :=
    | SynVChangeInit: forall erqFrom hdl, SynVChanges ((erqFrom, hdl) :: nil) nil nil
    | SynVChangeImm:
        forall rqFrom oidx oinds sinds smsgs,
          SynVChanges ((rqFrom, oidx) :: oinds) sinds smsgs ->
          idxSubtract (getForwards topo oidx) sinds = nil ->
          SynVChanges oinds (oidx :: sinds)
                      (synImmVChanges oidx rqFrom T (** precondition? *) chgs :: smsgs)
    | SynVChangeFwd:
        forall rqFrom oidx oinds sinds smsgs,
          SynVChanges ((rqFrom, oidx) :: oinds) sinds smsgs ->
          forall fwds,
            fwds = idxSubtract (nodup eq_nat_dec (getForwards topo oidx)) sinds ->
            fwds <> nil ->
            forall rqFwd rss,
              rqFwd = synRqVChanges oidx rqFrom fwds T (** precondition? *) ->
              rss = map (fun rsFrom => synRsVChanges oidx rsFrom chgs) fwds ->
              SynVChanges (oinds ++ (map (fun to => (oidx, to)) fwds))
                          (oidx :: sinds)
                          (rqFwd :: rss ++ smsgs).
    
  End GivenVChanges.

  Section Correctness.
    Variables (topo: list Channel)
              (chgs: VChanges)
              (erqFrom: IdxT).
    
    Variables (pre post: ObjectStates)
              (rqV rsV: Value).
    Hypothesis (Hchgs: SemVChanges chgs pre post rqV rsV).

    (* Lemma *)

  End Correctness.

End SynByVChanges.



(** Some tactics about [VLoc] and [VChange] *)

Ltac no_vloc_st oss oidx kidx :=
  lazymatch goal with
  | [vloc := (oss, VLocState oidx kidx, _) |- _] => fail
  | _ => idtac
  end.

(* NOTE: there's only one [VLocMsg] information per a transaction. *)
Ltac no_vloc_msg :=
  lazymatch goal with
  | [vloc := (VLocMsg, _) |- _] => fail
  | _ => idtac
  end.

Ltac collect_vloc :=
  repeat
    match goal with
    | [H1: M.find ?oidx ?oss = Some ?ost, H2: M.find ?kidx (ost_st ?ost) = Some ?v |- _] =>
      no_vloc_st oss oidx kidx;
      let vloc := fresh "vloc" in
      set (oss, VLocState oidx kidx, v) as vloc
    | [H: pmsg_postcond _ _ ?v _ |- _] =>
      no_vloc_msg;
      let vloc := fresh "vloc" in
      set (VLocMsg, v) as vloc
    end.

Ltac clear_vloc :=
  repeat
    match goal with
    | [vloc := _ : _ * VLoc * _ |- _] => clear vloc
    end.

Ltac no_diff sdf :=
  lazymatch goal with
  | [df := sdf |- _] => fail
  | _ => idtac
  end.

Ltac collect_diff oss1 oss2 :=
  repeat
    match goal with
    | [vloc := (oss2, VLocState ?oidx ?kidx, ?v) |- _] =>
      is_pure_const v;
      no_diff (VccIntro oidx kidx v);
      let df := fresh "df" in
      pose (VccIntro oidx kidx v) as df
    | [vloc1 := (oss1, ?wh1, ?v),
       vloc2 := (oss2, VLocState ?oidx2 ?kidx2, ?v) |- _] =>
      not_pure_const v;
      first [is_equal wh1 (VLocState oidx2 kidx2) |
             no_diff (VcmIntro wh1 oidx2 kidx2);
             let df := fresh "df" in
             pose (VcmIntro wh1 oidx2 kidx2) as df]
    end.

