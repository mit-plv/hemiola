Require Import Bool List String Peano_dec.
Require Import FnMap FunctionalExtensionality.

Set Implicit Arguments.

Open Scope list.

Ltac inv H := inversion H; subst; clear H.

Section Language.

  Definition IdxT := nat.

  (* A message is always either a request or a response. *)
  Inductive RqRs := Rq | Rs.

  (** Utilities *)
  Definition idx_add {A} (k: IdxT) (v: A) m := add eq_nat_dec k v m.
  Definition idx_msgType_dec: forall (k1 k2: IdxT * RqRs), {k1 = k2} + {k1 <> k2}.
  Proof.
    decide equality.
    - decide equality.
    - apply eq_nat_dec.
  Defined.
  Definition idx_msgType_add {A} (k: IdxT * RqRs) (v: A) m :=
    add idx_msgType_dec k v m.
  Definition idx_idx_dec: forall (k1 k2: IdxT * IdxT), {k1 = k2} + {k1 <> k2}.
  Proof.
    decide equality; apply eq_nat_dec.
  Defined.
  Definition idx_idx_add {A} (k: IdxT * IdxT) (v: A) m :=
    add idx_idx_dec k v m.

  Variable MsgT: Type.
  Variable StateT: Type.

  Record MsgId := { msg_rq : IdxT; (* an object that requests this message *)
                    msg_rs : IdxT; (* an object that responses this message *)
                    msg_rqrs : RqRs;
                    msg_type : MsgT
                  }.

  Definition msgFrom (msg: MsgId) :=
    match msg_rqrs msg with
    | Rq => msg_rq msg
    | Rs => msg_rs msg
    end.

  Definition msgTo (msg: MsgId) :=
    match msg_rqrs msg with
    | Rq => msg_rs msg
    | Rs => msg_rq msg
    end.

  Definition buildMsgId rq rs rr ty :=
    {| msg_rq := rq; msg_rs := rs; msg_rqrs := rr; msg_type := ty |}.

  Inductive PMsg :=
  | Pmsg: forall (msg: MsgId)
                 (precond: StateT -> Prop)
                 (outs: StateT -> list MsgId)
                 (postcond: StateT (* prestate *) ->
                            StateT (* poststate *) -> Prop), PMsg.

  Definition midOf (pmsg: PMsg) :=
    match pmsg with
    | Pmsg msg _ _ _ => msg
    end.

  Definition precondOf (pmsg: PMsg) :=
    match pmsg with
    | Pmsg _ precond _ _ => precond
    end.

  Definition outsOf (pmsg: PMsg) :=
    match pmsg with
    | Pmsg _ _ outs _ => outs
    end.

  Definition postcondOf (pmsg: PMsg) :=
    match pmsg with
    | Pmsg _ _ _ postcond => postcond
    end.

  Record Object :=
    { obj_idx: nat;
      obj_state_init: StateT;
      obj_pmsgs: PMsg -> Prop;
    }.

  Definition System := list Object.

  Section Semantics.

    Definition isTrsPair (rq rs: MsgId) :=
      (if eq_nat_dec (msg_rq rq) (msg_rq rs) then true else false)
        && (if eq_nat_dec (msg_rs rq) (msg_rs rs) then true else false)
        && (match msg_rqrs rq, msg_rqrs rs with
            | Rq, Rs => true
            | _, _ => false
            end).

    Definition ObjectStates := Map IdxT StateT.

    Definition MsgsFrom :=
      Map (IdxT * RqRs) (* (from, msgType) *) (list MsgId).
    Definition Messages := Map IdxT (* to *) MsgsFrom.

    Definition ValidOuts (idx: IdxT) (msgs: list MsgId) :=
      Forall (fun m => msgFrom m = idx) msgs.

    (*! A new version *)
    Inductive step_obj (obj: Object):
      StateT -> MsgsFrom ->
      option MsgId (* internal in? *) -> list MsgId (* outs *) ->
      StateT -> MsgsFrom -> Prop :=
    | SoInt: forall os msgs_from fidx fmsgT fmsg fmsgs fpmsg pos,
        (* 1) pick an internal message to process *)
        find (fidx, fmsgT) msgs_from = Some (fmsg :: fmsgs) ->

        (* 2) nondeterministically tries to find a predicated message for [fmsg],
         * which satisfies the precondition and postcondition.
         *)
        msgTo fmsg = obj_idx obj ->
        obj_pmsgs obj fpmsg -> midOf fpmsg = fmsg ->
        precondOf fpmsg os ->
        postcondOf fpmsg os pos ->

        (* -) later syntax should care [ValidOuts] *)
        ValidOuts (obj_idx obj) (outsOf fpmsg os) ->

        step_obj obj os msgs_from
                 (Some fmsg) (outsOf fpmsg os)
                 pos (idx_msgType_add (fidx, fmsgT) fmsgs msgs_from)
    | SoExt: forall os msgs_from emsg emsgs,
        find (msgFrom emsg, msg_rqrs emsg) msgs_from = Some emsgs ->
        msgTo emsg = obj_idx obj ->
        step_obj obj os msgs_from None (emsg :: nil) os msgs_from.

    Definition distributeMsg (from: IdxT) (msg: MsgId)
               (msgs: Messages): Messages :=
      let to := msgTo msg in
      match find to msgs with
      | Some toMsgs =>
        let added := match toMsgs (from, msg_rqrs msg) with
                     (* should be added last, since the head is the oldest *)
                     | Some fromMsgs => fromMsgs ++ (msg :: nil)
                     | None => msg :: nil
                     end in
        idx_add to (idx_msgType_add (from, msg_rqrs msg) added toMsgs) msgs
      | None =>
        idx_add to (idx_msgType_add (from, msg_rqrs msg) (msg :: nil) (@empty _ _)) msgs
      end.

    Fixpoint distributeMsgs (from: IdxT) (nmsgs: list MsgId)
             (msgs: Messages): Messages :=
      match nmsgs with
      | nil => msgs
      | msg :: nmsgs' => distributeMsgs from nmsgs' (distributeMsg from msg msgs)
      end.

    Definition getIndices (sys: System) := map (fun o => obj_idx o) sys.

    Definition isInternal (indices: list nat) (idx: IdxT) :=
      if in_dec eq_nat_dec idx indices then true else false.
    Definition isExternal (indices: list nat) (idx: IdxT) :=
      if in_dec eq_nat_dec idx indices then false else true.

    Definition fromExt (indices: list nat) (omsg: option MsgId) :=
      match omsg with
      | Some msg => if isExternal indices (msgFrom msg) then Some msg else None
      | None => None
      end.
    Definition toExts (indices: list nat) (msgs: list MsgId) :=
      filter (fun pm => isExternal indices (msgTo pm)) msgs.

    Record Label := { lbl_in: option MsgId;
                      lbl_outs: list MsgId }.

    Record State := { st_oss: ObjectStates;
                      st_msgs: Messages }.

    Inductive step (sys: System) : State -> Label -> State -> Prop :=
    | Step: forall oss idx (obj: Object) (os: StateT)
                   oims msgs_from msg_in msgs_out pos pmsgs_from,
        In obj sys ->
        obj_idx obj = idx ->
        find idx oss = Some os ->
        find idx oims = Some msgs_from -> 
        step_obj obj os msgs_from msg_in msgs_out pos pmsgs_from ->
        match msg_in with
        | Some msg => isInternal (getIndices sys) (msgFrom msg) = true
        | None => match msgs_out with
                  | msg :: _ => isExternal (getIndices sys) (msgFrom msg) = true
                  | _ => False
                  end
        end ->
        step sys {| st_oss := oss; st_msgs := oims |}
             {| lbl_in := msg_in; lbl_outs := msgs_out |}
             {| st_oss := idx_add idx pos oss;
                st_msgs := distributeMsgs idx msgs_out (idx_add idx pmsgs_from oims) |}.

    Definition ocons {A} (oa: option A) (l: list A) :=
      match oa with
      | Some a => a :: l
      | None => l
      end.
    Infix "::>" := ocons (at level 0).

    (* NOTE: head is the youngest *)
    Inductive steps (sys: System) : State -> list Label -> State -> Prop :=
    | StepsNil: forall st, steps sys st nil st
    | StepsCons:
        forall st1 msgs st2,
          steps sys st1 msgs st2 ->
          forall lbl st3,
            step sys st2 lbl st3 ->
            steps sys st1 (lbl :: msgs) st3.

    Fixpoint getObjectStatesInit (sys: System) : ObjectStates :=
      match sys with
      | nil => @empty _ _
      | obj :: sys' =>
        idx_add (obj_idx obj)
                (obj_state_init obj)
                (getObjectStatesInit sys')
      end.

    Record BLabel :=
      { blbl_in: option MsgId;
        blbl_outs: list MsgId }.

    Definition getBLabel (sys: System) (lbl: Label) :=
      match lbl with
      | {| lbl_in := min; lbl_outs := mouts |} =>
        let ein := fromExt (getIndices sys) min in
        let eouts := toExts (getIndices sys) mouts in
        match ein, eouts with
        | None, nil => None
        | _, _ => Some {| blbl_in := ein; blbl_outs := eouts |}
        end
      end.

    Fixpoint behaviorOf (sys: System) (l: list Label) :=
      match l with
      | nil => nil
      | lbl :: l' => (getBLabel sys lbl) ::> (behaviorOf sys l')
      end.

    Inductive Behavior: System -> list BLabel -> Prop :=
    | Behv: forall sys hst st,
        steps sys {| st_oss := getObjectStatesInit sys;
                     st_msgs := @empty _ _ |} hst st ->
        forall bhst,
          bhst = behaviorOf sys hst ->
          Behavior sys bhst.

    (** Now about linearizability *)

    Fixpoint historyOf (sys: System) (l: list Label) :=
      match l with
      | nil => nil
      | {| lbl_in := min; lbl_outs := mouts |} :: l' =>
        (toExts (getIndices sys) mouts)
          ++ ((fromExt (getIndices sys) min) ::> (historyOf sys l'))
      end.

    Inductive History : System -> list MsgId -> Prop :=
    | Hist: forall sys hst st,
        steps sys {| st_oss := getObjectStatesInit sys;
                     st_msgs := @empty _ _ |} hst st ->
        History sys (historyOf sys hst).

    (* A history consisting only of requests and matching responses. *)
    Inductive Complete: list MsgId -> Prop :=
    | CplNil: Complete nil
    | CplAdd:
        forall hst1 hst2 hst3,
          Complete (hst1 ++ hst2 ++ hst3) ->
          forall rq rs,
            isTrsPair rq rs = true ->
            forall chst,
              chst = hst1 ++ rq :: hst2 ++ rs :: hst3 ->
              Complete chst.

    Inductive SubHistory {A}: list A -> list A -> Prop :=
    | SlNil: SubHistory nil nil
    | SlAdd: forall l1 l2, SubHistory l1 l2 -> forall a, SubHistory (a :: l1) (a :: l2)
    | SlSkip: forall l1 l2, SubHistory l1 l2 -> forall a, SubHistory l1 (a :: l2).
    
    Definition ExtHistory {A} (l el: list A): Prop :=
      exists e, el = l ++ e.

    Fixpoint matchTrsPair (rq: MsgId) (rss: list MsgId) :=
      match rss with
      | nil => None
      | rs :: rss' =>
        if isTrsPair rq rs then Some rss'
        else match matchTrsPair rq rss' with
             | Some nrss => Some (rs :: nrss)
             | None => None
             end
      end.

    (* Assuming the history is well-formed. *)
    Fixpoint complete' (hst rss: list MsgId): list MsgId * list MsgId :=
      match hst with
      | nil => (nil, rss)
      | msg :: hst' =>
        match msg_rqrs msg with
        | Rq => let (phst, prss) := complete' hst' rss in
                match matchTrsPair msg prss with
                | Some nrss => (msg :: phst, nrss)
                | None => (phst, prss)
                end
        | Rs => let (phst, prss) := complete' hst' rss in
                (msg :: phst, msg :: prss)
        end
      end.

    (* Axiom exMsgT: MsgT. *)
    (* Example exMsg1 := {| msg_rq := 1; msg_rs := 2; msg_rqrs := Rq; msg_type := exMsgT |}. *)
    (* Example exMsg2 := {| msg_rq := 1; msg_rs := 2; msg_rqrs := Rs; msg_type := exMsgT |}. *)
    (* Example exMsg3 := {| msg_rq := 3; msg_rs := 4; msg_rqrs := Rq; msg_type := exMsgT |}. *)
    (* Example exMsg4 := {| msg_rq := 3; msg_rs := 4; msg_rqrs := Rs; msg_type := exMsgT |}. *)
    (* Eval compute in (complete' (exMsg1 :: exMsg2 :: nil) nil). *)
    (* Eval compute in (complete' (exMsg2 :: exMsg1 :: nil) nil). *)
    (* Eval compute in (complete' (exMsg1 :: exMsg3 :: exMsg4 :: exMsg2 :: nil) nil). *)

    Definition complete (hst: list MsgId) := fst (complete' hst nil).
    Definition WellFormed (hst: list MsgId) := snd (complete' hst nil) = nil.

    Lemma complete_subList: forall hst, SubHistory (complete hst) hst.
    Proof.
    Admitted.
    
    Lemma complete_complete: forall hst, Complete (complete hst).
    Proof.
    Admitted.

    Lemma complete_maximal:
      forall hst chst,
        chst <> complete hst ->
        SubHistory chst hst -> Complete chst ->
        ~ SubHistory (complete hst) chst.
    Proof.
    Admitted.

    (* An informal definition of "sequential":
     * 1) The first message should be a request
     * 2) A matching response for each request should be right after the request.
     * 3) There might not be a matching response for the last request.
     *)
    Fixpoint Sequential' (hst: list MsgId) (orq: option MsgId) :=
      match hst with
      | nil => true
      | msg :: hst' =>
        match orq with
        | Some rq => isTrsPair rq msg && Sequential' hst' None
        | None => match msg_rqrs msg with
                  | Rq => Sequential' hst' (Some msg)
                  | Rs => false
                  end
        end
      end.
    Definition Sequential (hst: list MsgId) := Sequential' hst None = true.
    Definition Concurrent (hst: list MsgId) := ~ Sequential hst.

    Definition sequential_concurrent_dec:
      forall hst, {Sequential hst} + {Concurrent hst}.
    Proof.
      unfold Concurrent, Sequential; intros.
      destruct (Sequential' hst None).
      - left; reflexivity.
      - right; discriminate.
    Defined.

    (* A system is sequential when all possible histories are sequential. *)
    Definition SequentialSys (sys: System) :=
      forall hst, History sys hst -> Sequential (rev hst).
    
    (* In message passing system, "object subhistory" and "process subhistory"
     * have exactly the same meaning; here an index "i" indicates a single object.
     * An ambiguity comes when we need to decide whether a req/resp from "i" to "j"
     * belongs to i's or j's subhistory.
     * For requests, j's subhistory contains them.
     * For responses, i's subhistory contains them.
     *)
    Definition isSystemMsg (sys: list IdxT) (e: MsgId) :=
      (if in_dec idx_msgType_dec (msg_rq e, msg_rqrs e)
                 (map (fun i => (i, Rq)) sys) then true else false)
      || (if in_dec idx_msgType_dec (msg_rs e, msg_rqrs e)
                    (map (fun i => (i, Rs)) sys) then true else false).
    Definition objSubHistory (i: IdxT) (hst: list MsgId) :=
      filter (isSystemMsg (i :: nil)) hst.

    (* Two histories are equivalent iff any object subhistories are equal. *)
    Definition Equivalent (hst1 hst2: list MsgId) :=
      forall i, objSubHistory i hst1 = objSubHistory i hst2.

    (* TODO: this is actually not a fully correct definition:
     * Linearizability requires one more condition: any _strict_ transaction
     * orders are preserved by [lhst].
     *)
    Definition Linearizable (hst lhst: list MsgId) :=
      exists ehst,
        ExtHistory hst ehst /\
        Sequential lhst /\
        Equivalent (complete ehst) lhst.

    (* A system is linear when all possible histories are linearizable. *)
    Definition Linear (sys: System) :=
      forall hst,
        History sys hst ->
        exists lhst, History sys lhst /\
                     Linearizable (rev hst) (rev lhst).

  End Semantics.

  Section Facts.

    Lemma find_idx_add_eq:
      forall {A} (m: Map nat A) (k: nat) (v: A),
        find k (idx_add k v m) = Some v.
    Proof.
      unfold find, idx_add, add; intros.
      destruct (eq_nat_dec k k); auto.
      elim n; reflexivity.
    Qed.

    Lemma find_idx_add_neq:
      forall {A} (m: Map nat A) (k1 k2: nat) (v: A),
        k1 <> k2 ->
        find k1 (idx_add k2 v m) = find k1 m.
    Proof.
      unfold find, idx_add, add; intros.
      destruct (eq_nat_dec k2 k1); auto; subst.
      elim H; reflexivity.
    Qed.

    Lemma idx_add_comm:
      forall {A} (m: Map nat A) (k1 k2: nat) (v1 v2: A),
        k1 <> k2 ->
        idx_add k1 v1 (idx_add k2 v2 m) = idx_add k2 v2 (idx_add k1 v1 m).
    Proof.
      unfold idx_add, add; intros.
      extensionality x.
      destruct (eq_nat_dec k1 x), (eq_nat_dec k2 x); subst; auto.
      elim H; reflexivity.
    Qed.

    Lemma subHistory_refl: forall {A} (l: list A), SubHistory l l.
    Proof.
      induction l; simpl; intros; constructor; auto.
    Qed.
    Hint Immediate subHistory_refl.

    Lemma extHistory_trans:
      forall {A} (l1 l2 l3: list A),
        ExtHistory l1 l2 -> ExtHistory l2 l3 -> ExtHistory l1 l3.
    Proof.
      unfold ExtHistory; intros.
      destruct H, H0; subst.
      eexists; rewrite <-app_assoc; reflexivity.
    Qed.

    Lemma equivalent_refl: forall hst, Equivalent hst hst.
    Proof.
      intros; unfold Equivalent; reflexivity.
    Qed.
    Hint Immediate equivalent_refl.

  End Facts.

End Language.

Definition Refines {MsgT IStateT SStateT}
           (impl: System MsgT IStateT) (spec: System MsgT SStateT) :=
  forall hst, Behavior impl hst -> Behavior spec hst.

Hint Immediate subHistory_refl extHistory_trans equivalent_refl.

