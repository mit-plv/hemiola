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
  Hypothesis (msgT_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2}).
  Variable MvalT: MsgT -> RqRs -> Type.
  Variable StateT: Type.

  Record MsgId := { msg_rq : IdxT; (* an object that requests this message *)
                    msg_rs : IdxT; (* an object that responses this message *)
                    msg_type : MsgT;
                    msg_rqrs : RqRs
                  }.

  Record Msg :=
    { msg_id: MsgId;
      msg_value: MvalT (msg_type msg_id) (msg_rqrs msg_id)
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

  Definition buildMsgId rq rs ty rr :=
    {| msg_rq := rq; msg_rs := rs; msg_type := ty; msg_rqrs := rr |}.

  Record PMsg :=
    { pmsg_mid: MsgId;
      pmsg_precond: StateT -> Prop;
      pmsg_outs: StateT ->
                 MvalT (msg_type pmsg_mid) (msg_rqrs pmsg_mid) ->
                 list Msg;
      pmsg_postcond: StateT (* prestate *) ->
                     MvalT (msg_type pmsg_mid) (msg_rqrs pmsg_mid) ->
                     StateT (* poststate *) -> Prop
    }.

  Record Object :=
    { obj_idx: nat;
      obj_state_init: StateT;
      obj_pmsgs: list PMsg
    }.

  Definition System := list Object.

  Section Semantics.

    Definition isTrsPair (rq rs: MsgId) :=
      (if eq_nat_dec (msg_rq rq) (msg_rq rs) then true else false)
        && (if eq_nat_dec (msg_rs rq) (msg_rs rs) then true else false)
        && (if msgT_dec (msg_type rq) (msg_type rs) then true else false)
        && (match msg_rqrs rq, msg_rqrs rs with
            | Rq, Rs => true
            | _, _ => false
            end).

    Definition ObjectStates := Map IdxT StateT.

    Definition MsgsFrom :=
      Map (IdxT * RqRs) (* (from, msgType) *) (list Msg).
    Definition Messages := Map IdxT (* to *) MsgsFrom.

    (* A set of output messages are valid if
     * 1) they are from the same source [idx] and
     * 2) all targets are different to each others.
     * TODO? syntax may have to ensure [ValidOuts], or by well-formedness.
     *)
    Definition ValidOuts (idx: IdxT) (msgs: list Msg) :=
      Forall (fun m => msgFrom (msg_id m) = idx) msgs /\
      NoDup (map (fun m => msgTo (msg_id m)) msgs).

    (* [step_obj] is for a step by an object that handles an internal message:
     * 1) First, an internal message is nondeterministically picked, and
     * 2) A predicated message for [fmsg], which satisfies its precondition and
     *    postcondition, is nondeterministically picked to take a step.
     *)
    Inductive step_obj (obj: Object):
      StateT -> MsgsFrom ->
      Msg (* in *) -> list Msg (* outs *) ->
      StateT -> MsgsFrom -> Prop :=
    | SoInt:
        forall os msgs_from fidx fmsgT fmsg fmsgs fpmsg pos
               (Hm: msg_id fmsg = pmsg_mid fpmsg)
               (fvalue: MvalT (msg_type (pmsg_mid fpmsg)) (msg_rqrs (pmsg_mid fpmsg))),
          find (fidx, fmsgT) msgs_from = Some (fmsg :: fmsgs) ->
          fvalue = match Hm with eq_refl => msg_value fmsg end ->
          msgTo (msg_id fmsg) = obj_idx obj ->
          In fpmsg (obj_pmsgs obj) ->
          pmsg_precond fpmsg os ->
          pmsg_postcond fpmsg os fvalue pos ->
          ValidOuts (obj_idx obj) (pmsg_outs fpmsg os fvalue) ->
          step_obj obj os msgs_from
                   fmsg (pmsg_outs fpmsg os fvalue)
                   pos (idx_msgType_add (fidx, fmsgT) fmsgs msgs_from).

    Definition distributeMsg (msg: Msg) (msgs: Messages): Messages :=
      let from := msgFrom (msg_id msg) in
      let to := msgTo (msg_id msg) in
      match find to msgs with
      | Some toMsgs =>
        let added := match toMsgs (from, msg_rqrs (msg_id msg)) with
                     (* should be added last, since the head is the oldest *)
                     | Some fromMsgs => fromMsgs ++ (msg :: nil)
                     | None => msg :: nil
                     end in
        idx_add to (idx_msgType_add (from, msg_rqrs (msg_id msg)) added toMsgs) msgs
      | None =>
        idx_add to (idx_msgType_add (from, msg_rqrs (msg_id msg)) (msg :: nil) (@empty _ _)) msgs
      end.

    Fixpoint distributeMsgs (nmsgs: list Msg) (msgs: Messages): Messages :=
      match nmsgs with
      | nil => msgs
      | msg :: nmsgs' =>
        distributeMsgs nmsgs' (distributeMsg msg msgs)
      end.

    Definition getIndices (sys: System) := map (fun o => obj_idx o) sys.

    Definition isInternal (indices: list nat) (idx: IdxT) :=
      if in_dec eq_nat_dec idx indices then true else false.
    Definition isExternal (indices: list nat) (idx: IdxT) :=
      if in_dec eq_nat_dec idx indices then false else true.

    Definition fromExt (sys: System) (omsg: option Msg) :=
      match omsg with
      | Some msg => if isExternal (getIndices sys) (msgFrom (msg_id msg))
                    then Some msg else None
      | None => None
      end.
    Definition toInts (sys: System) (msgs: list Msg) :=
      filter (fun pm => isInternal (getIndices sys) (msgTo (msg_id pm))) msgs.
    Definition toExts (sys: System) (msgs: list Msg) :=
      filter (fun pm => isExternal (getIndices sys) (msgTo (msg_id pm))) msgs.

    (* [lbl_in] is [None] if a step is taken externally. *)
    Record Label := { lbl_in: option Msg;
                      lbl_outs: list Msg }.

    Record State := { st_oss: ObjectStates;
                      st_msgs: Messages }.

    (* [step_sys] covers an internal and external step in terms of a given 
     * system.
     *)
    Inductive step_sys (sys: System) : State -> Label -> State -> Prop :=
    | SsInt: forall oss idx (obj: Object) (os: StateT)
                    oims msgs_from msg_in msgs_out pos pmsgs_from,
        In obj sys ->
        obj_idx obj = idx ->
        find idx oss = Some os ->
        find idx oims = Some msgs_from -> 
        step_obj obj os msgs_from msg_in msgs_out pos pmsgs_from ->
        isInternal (getIndices sys) (msgFrom (msg_id msg_in)) = true ->
        step_sys sys {| st_oss := oss; st_msgs := oims |}
                 {| lbl_in := Some msg_in;
                    lbl_outs := toExts sys msgs_out |}
                 {| st_oss := idx_add idx pos oss;
                    st_msgs := distributeMsgs (toInts sys msgs_out)
                                              (idx_add idx pmsgs_from oims) |}
    | SsExt: forall oss oims emsg_in emsgs_out,
        isExternal (getIndices sys) (msgTo (msg_id emsg_in)) = true ->
        Forall (fun emsg => isExternal
                              (getIndices sys)
                              (msgFrom (msg_id emsg)) = true) emsgs_out ->
        step_sys sys {| st_oss := oss; st_msgs := oims |}
                 {| lbl_in := None;
                    lbl_outs := emsgs_out |}
                 {| st_oss := oss;
                    st_msgs := distributeMsgs emsgs_out oims |}.

    Definition DisjointSystem (sys1 sys2: System) :=
      NoDup (map (fun obj => obj_idx obj) sys1 ++ map (fun obj => obj_idx obj) sys2).
    Definition combineSystem (sys1 sys2: System) := sys1 ++ sys2.

    Definition combineState (st1 st2: State) :=
      {| st_oss := union (st_oss st1) (st_oss st2);
         st_msgs := union (st_msgs st1) (st_msgs st2) |}.

    Definition DisjointLabel (lbl1 lbl2: Label) :=
      match lbl_in lbl1, lbl_in lbl2 with
      | Some _, None => forall msg, In msg (lbl_outs lbl2) -> In msg (lbl_outs lbl1)
      | None, Some _ => forall msg, In msg (lbl_outs lbl1) -> In msg (lbl_outs lbl2)
      | None, None => True
      | _, _ => False
      end.

    Definition combineLabel (lbl1 lbl2: Label) :=
      match lbl_in lbl1, lbl_in lbl2 with
      | Some _, None => {| lbl_in := lbl_in lbl1;
                           lbl_outs := lbl_outs lbl1 (* -- (lbl_outs lbl2), TODO *) |}
      | None, Some _ => {| lbl_in := lbl_in lbl2;
                           lbl_outs := lbl_outs lbl2 (* -- (lbl_outs lbl1), TODO *) |}
      | None, None => {| lbl_in := None;
                         lbl_outs := (lbl_outs lbl1) ++ (lbl_outs lbl2) |}
      | _, _ => {| lbl_in := None; lbl_outs := nil |}
      end.

    Inductive step : System -> State -> Label -> State -> Prop :=
    | StepLift:
        forall sys st1 lbl st2,
          step_sys sys st1 lbl st2 ->
          step sys st1 lbl st2
    | StepComb:
        forall sys1 st11 lbl1 st12,
          step sys1 st11 lbl1 st12 ->
          forall sys2 st21 lbl2 st22,
            step sys2 st21 lbl2 st22 ->
            step (combineSystem sys1 sys2)
                 (combineState st11 st21)
                 (combineLabel lbl1 lbl2)
                 (combineState st12 st22).

    Definition ocons {A} (oa: option A) (l: list A) :=
      match oa with
      | Some a => a :: l
      | None => l
      end.
    Infix "::>" := ocons (at level 0).

    (* Note that the head is the youngest *)
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

    Definition getLabel (sys: System) (lbl: Label) :=
      match lbl with
      | {| lbl_in := min; lbl_outs := mouts |} =>
        let ein := fromExt sys min in
        match ein, mouts with
        | None, nil => None
        | _, _ => Some {| lbl_in := ein; lbl_outs := mouts |}
        end
      end.

    Fixpoint behaviorOf (sys: System) (l: list Label) :=
      match l with
      | nil => nil
      | lbl :: l' => (getLabel sys lbl) ::> (behaviorOf sys l')
      end.

    Inductive Behavior: System -> list Label -> Prop :=
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
        mouts ++ min ::> (historyOf sys l')
      end.

    Inductive History : System -> list Msg -> Prop :=
    | Hist: forall sys hst,
        Behavior sys hst ->
        History sys (historyOf sys hst).

    (* A history consisting only of requests and matching responses. *)
    Inductive Complete: list Msg -> Prop :=
    | CplNil: Complete nil
    | CplAdd:
        forall hst1 hst2 hst3,
          Complete (hst1 ++ hst2 ++ hst3) ->
          forall rq rs,
            isTrsPair (msg_id rq) (msg_id rs) = true ->
            forall chst,
              chst = hst1 ++ rq :: hst2 ++ rs :: hst3 ->
              Complete chst.

    Inductive SubHistory {A}: list A -> list A -> Prop :=
    | SlNil: SubHistory nil nil
    | SlAdd: forall l1 l2, SubHistory l1 l2 -> forall a, SubHistory (a :: l1) (a :: l2)
    | SlSkip: forall l1 l2, SubHistory l1 l2 -> forall a, SubHistory l1 (a :: l2).
    
    Definition ExtHistory {A} (l el: list A): Prop :=
      exists e, el = l ++ e.

    Fixpoint matchTrsPair (rq: Msg) (rss: list Msg) :=
      match rss with
      | nil => None
      | rs :: rss' =>
        if isTrsPair (msg_id rq) (msg_id rs) then Some rss'
        else match matchTrsPair rq rss' with
             | Some nrss => Some (rs :: nrss)
             | None => None
             end
      end.

    (* Assuming the history is well-formed. *)
    Fixpoint complete' (hst rss: list Msg): list Msg * list Msg :=
      match hst with
      | nil => (nil, rss)
      | msg :: hst' =>
        match msg_rqrs (msg_id msg) with
        | Rq => let (phst, prss) := complete' hst' rss in
                match matchTrsPair msg prss with
                | Some nrss => (msg :: phst, nrss)
                | None => (phst, prss)
                end
        | Rs => let (phst, prss) := complete' hst' rss in
                (msg :: phst, msg :: prss)
        end
      end.

    Definition complete (hst: list Msg) := fst (complete' hst nil).
    Definition WellFormed (hst: list Msg) := snd (complete' hst nil) = nil.

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
    Fixpoint Sequential' (hst: list Msg) (orq: option Msg) :=
      match hst with
      | nil => true
      | msg :: hst' =>
        match orq with
        | Some rq => isTrsPair (msg_id rq) (msg_id msg) && Sequential' hst' None
        | None => match msg_rqrs (msg_id msg) with
                  | Rq => Sequential' hst' (Some msg)
                  | Rs => false
                  end
        end
      end.
    Definition Sequential (hst: list Msg) := Sequential' hst None = true.
    Definition Concurrent (hst: list Msg) := ~ Sequential hst.

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
    
    (* In message passing system, a "process" refers to a "requester" and an 
     * "object" refers to a "requestee".
     * Thus, for a given message {| msg_rq := i; msg_rs := j; msg_rqrs := _ |},
     * its requester (process) is "i" and the (target) object is "j".
     *)
    Definition isProcessOf (obj: Object) (msg: Msg) :=
      if eq_nat_dec (obj_idx obj) (msg_rq (msg_id msg)) then true else false.

    Definition isObjectOf (obj: Object) (msg: Msg) :=
      if eq_nat_dec (obj_idx obj) (msg_rs (msg_id msg)) then true else false.

    Definition objSubHistory (obj: Object) (hst: list Msg) :=
      filter (isObjectOf obj) hst.

    Definition procSubHistory (obj: Object) (hst: list Msg) :=
      filter (isProcessOf obj) hst.

    (* Two histories are equivalent iff any process subhistories are equal. *)
    Definition Equivalent (hst1 hst2: list Msg) :=
      forall i, procSubHistory i hst1 = procSubHistory i hst2.

    (* TODO: this is actually not a fully correct definition:
     * Linearizability requires one more condition: any _strict_ transaction
     * orders are preserved by [lhst].
     *)
    Definition Linearizable (hst lhst: list Msg) :=
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

Definition Refines {MsgT} {MvalT: MsgT -> RqRs -> Type} {IStateT SStateT}
           (impl: System MvalT IStateT) (spec: System MvalT SStateT) :=
  forall hst, Behavior impl hst -> Behavior spec hst.

Hint Immediate subHistory_refl extHistory_trans equivalent_refl.

