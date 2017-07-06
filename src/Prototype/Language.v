Require Import List String Peano_dec.
Require Import FnMap.

Set Implicit Arguments.

Open Scope list.

Section Language.

  (* A message is always either a request or a response.
   * A request indicates a start of a transaction.
   * A corresponding response indicates the end of the transaction.
   *)
  Variable Msg: Type.
  Variables (msg_is_req: Msg -> bool).
  
  Section Syntax.

    Definition IdxT := nat.
    Definition IMsg := (IdxT * Msg)%type.

    Section Object.
      Variable StateT: Type.

      Definition CmdT :=
        StateT -> option (list IMsg (* internal messages out *) *
                          option IMsg (* optional external out *) *
                          StateT (* next state *)).
      Definition RuleT := IMsg -> CmdT.

      Record Object :=
        { obj_idx: nat;
          obj_state_init: StateT;
          obj_rules: list RuleT;
        }.

    End Object.

    Definition Objects := list { st : Type & Object st }.

  End Syntax.

  Section Semantics.

    Record ObjectState StateT :=
      { os_obj: Object StateT;
        os_state: StateT
      }.

    Definition ObjectStates :=
      Map IdxT { StateT : Type & ObjectState StateT }.

    Definition InMsgs := Map IdxT (* from *) (list Msg).

    Definition ObjectInMsgs := Map (IdxT * bool) (* (to, is_req) *) InMsgs.

    Definition idx_add {A} (k: IdxT) (v: A) m :=
      add eq_nat_dec k v m.

    Definition idx_bool_dec: forall (k1 k2: IdxT * bool), {k1 = k2} + {k1 <> k2}.
    Proof.
      decide equality.
      - apply Bool.bool_dec.
      - apply eq_nat_dec.
    Defined.
    Definition idx_bool_add {A} (k: IdxT * bool) (v: A) m :=
      add idx_bool_dec k v m.

    Fixpoint step_rule {StateT} (rules: list (RuleT StateT))
             (imsg: IMsg) (st: StateT) :=
      match rules with
      | nil => None
      | r :: rules' =>
        match r imsg st with 
        | Some mst => Some mst
        | None => step_rule rules' imsg st
        end
      end.

    Inductive step_obj {StateT}:
      ObjectState StateT -> InMsgs ->
      list IMsg -> option IMsg (* external_in *) -> option IMsg (* external_out *) ->
      ObjectState StateT -> InMsgs -> Prop :=
    | StepObjInt: forall os imsgs fidx fmsg fmsgs imsgs_to emsgs_to pos,
        step_rule (obj_rules (os_obj os)) (fidx, fmsg) (os_state os) =
        Some (imsgs_to, emsgs_to, pos) ->
        find fidx imsgs = Some (fmsg :: fmsgs) ->
        step_obj os imsgs
                 imsgs_to None emsgs_to
                 {| os_obj := os_obj os;
                    os_state := pos |}
                 (idx_add fidx fmsgs imsgs)
    | StepObjExt: forall os imsgs emsg_in imsgs_to emsgs_to pos,
        step_rule (obj_rules (os_obj os)) emsg_in (os_state os) =
        Some (imsgs_to, emsgs_to, pos) ->
        step_obj os imsgs
                 imsgs_to (Some emsg_in) emsgs_to
                 {| os_obj := os_obj os;
                    os_state := pos |}
                 imsgs.

    Fixpoint distr_msgs (from: IdxT) (to: list IMsg)
             (msgs: ObjectInMsgs): ObjectInMsgs :=
      match to with
      | nil => msgs
      | (toIdx, msg) :: to' =>
        match find (toIdx, msg_is_req msg) msgs with
        | Some toMsgs =>
          let added := match toMsgs from with
                       | Some fromMsgs => fromMsgs ++ (msg :: nil)
                       | None => msg :: nil
                       end in
          idx_bool_add (toIdx, msg_is_req msg) (idx_add from added toMsgs) msgs
        | None =>
          idx_bool_add (toIdx, msg_is_req msg) (idx_add from (msg :: nil) (@empty _ _)) msgs
        end
      end.

    Inductive step : ObjectStates -> ObjectInMsgs ->
                     option IMsg (* external in *) -> option IMsg (* external out *) ->
                     ObjectStates -> ObjectInMsgs -> Prop :=
    | Step: forall oss idx is_req {StateT} (os: ObjectState StateT)
                   oims imsgs imsgs_to emsg_in emsg_out pos pimsgs,
        find idx oss = Some (existT _ _ os) ->
        find (idx, is_req) oims = Some imsgs -> 
        step_obj os imsgs imsgs_to emsg_in emsg_out pos pimsgs ->
        step oss oims emsg_in emsg_out
             (idx_add idx (existT _ _ pos) oss)
             (distr_msgs idx imsgs_to (idx_bool_add (idx, is_req) pimsgs oims)).

    (* NOTE: the oldest is the head *)
    Definition addHistory (om: option IMsg) (hst: list IMsg) :=
      match om with
      | Some m => hst ++ (m :: nil)
      | None => hst
      end.
    Infix "<::" := addHistory (at level 30, right associativity).

    Inductive steps : ObjectStates -> ObjectInMsgs ->
                      list IMsg (* history *) ->
                      ObjectStates -> ObjectInMsgs -> Prop :=
    | StepsNil: forall oss oims, steps oss oims nil oss oims
    | StepsCons:
        forall oss1 oims1 emsgs oss2 oims2,
          steps oss1 oims1 emsgs oss2 oims2 ->
          forall oss3 emsg_in emsg_out oims3,
            step oss2 oims2 emsg_in emsg_out oss3 oims3 ->
            steps oss1 oims1 (emsg_out <:: emsg_in <:: emsgs) oss3 oims3.

    Definition getObjectStateInit {StateT} (obj: Object StateT) :=
      {| os_obj := obj;
         os_state := obj_state_init obj |}.
    Fixpoint getObjectStatesInit (obs: Objects) : ObjectStates :=
      match obs with
      | nil => @empty _ _
      | obj :: obs' =>
        idx_add (obj_idx (projT2 obj))
                (existT _ _ (getObjectStateInit (projT2 obj)))
                (getObjectStatesInit obs')
      end.

    Definition HistoryOf (obs: Objects) (hst: list IMsg) :=
      exists oss oims, steps (getObjectStatesInit obs) (@empty _ _) hst oss oims.

    (** Now some notions borrowed from linearlizability and serializability.
     * Definitions need to be much more robust for the real language design.
     * It's for now a bit informal.
     *)

    (* A maximum subsequence of H consisting only of requests and matching responses. *)
    Definition complete (hst: list IMsg): list IMsg. Admitted.

    Definition Complete (hst: list IMsg) := hst = complete hst.

    Fixpoint Serial' (hst: list IMsg) (oi: option IdxT) :=
      match hst with
      | nil => True
      | (idx, msg) :: hst' =>
        match oi with
        | Some i => idx = i /\ msg_is_req msg = false /\
                    Serial' hst' None
        | None => msg_is_req msg = true /\ Serial' hst' (Some idx)
        end
      end.

    Definition Serial (hst: list IMsg) := Serial' hst None.

    Definition subHistory (i: IdxT) (hst: list IMsg) :=
      filter (fun e => if eq_nat_dec i (fst e) then true else false) hst.

    Definition Equivalent (hst1 hst2: list IMsg) :=
      forall i, subHistory i hst1 = subHistory i hst2.

    Definition Serializable (hst: list IMsg) :=
      exists shst, Serial shst /\ Equivalent (complete hst) shst.

    Definition SerialObjects (obs: Objects) :=
      forall hst, HistoryOf obs hst -> Serializable hst.

  End Semantics.

  Section Facts.

    Lemma equivalent_refl: forall hst, Equivalent hst hst.
    Proof.
      unfold Equivalent; intros; reflexivity.
    Qed.
    Hint Immediate equivalent_refl.

    Lemma equivalent_app:
      forall hst1 hst1' hst2 hst2',
        Equivalent hst1 hst1' -> Equivalent hst2 hst2' ->
        Equivalent (hst1 ++ hst2) (hst1' ++ hst2').
    Proof.
    Admitted.

    Lemma complete_serial: forall hst, Serial hst -> Serial (complete hst).
    Proof.
    Admitted.
    Hint Immediate complete_serial.

    Lemma complete_serial_app:
      forall hst1,
        Complete hst1 ->
        forall hst2, Serial hst2 -> Serial (hst1 ++ hst2).
    Proof.
    Admitted.
    Hint Immediate complete_serial_app.

    Lemma complete_complete_app:
      forall hst1,
        Complete hst1 ->
        forall hst2, complete (hst1 ++ hst2) = complete hst1 ++ complete hst2.
    Proof.
    Admitted.

    Lemma complete_equivalent:
      forall hst, Complete hst -> Equivalent (complete hst) hst.
    Proof.
    Admitted.
    Hint Immediate complete_equivalent.
      
    Lemma serial_serializable: forall hst, Serial hst -> Serializable hst.
    Proof.
      intros; exists (complete hst); split; eauto.
    Qed.
    Hint Immediate serial_serializable.

    Lemma complete_serializable_app:
      forall hst1,
        Complete hst1 ->
        forall hst2, Serializable hst2 -> Serializable (hst1 ++ hst2).
    Proof.
      unfold Serializable; intros.
      destruct H0 as [shst2 [? ?]].
      exists (hst1 ++ shst2); split; auto.

      rewrite complete_complete_app by assumption.
      apply equivalent_app; auto.
    Qed.

  End Facts.

End Language.

