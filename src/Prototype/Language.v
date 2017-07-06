Require Import List String Peano_dec.
Require Import FnMap.

Set Implicit Arguments.

Open Scope list.

Section Language.

  Definition IdxT := nat.

  (* A message is always either a request or a response.
   * A request indicates a start of a transaction.
   * A corresponding response indicates the end of the transaction.
   *)
  Variable MsgT: Type.
  Inductive MsgType := Req | Resp.
  Record Msg := { msg_type : MsgType;
                  msg_from : IdxT;
                  msg_to : IdxT;
                  msg_content : MsgT }.
  Definition buildMsg ty fr to co := {| msg_type := ty;
                                        msg_from := fr;
                                        msg_to := to;
                                        msg_content := co |}.
  
  Section Syntax.

    Section Object.
      Variable StateT: Type.

      Definition CmdT :=
        StateT -> option (list Msg (* internal messages out *) *
                          list Msg (* optional external out; the youngest should be the head *) *
                          StateT (* next state *)).
      Definition RuleT := Msg -> CmdT.

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

    Definition MsgsFrom := Map (IdxT * MsgType) (* (from, msgType) *) (list Msg).
    Definition Messages := Map IdxT (* to *) MsgsFrom.

    Definition idx_add {A} (k: IdxT) (v: A) m := add eq_nat_dec k v m.
    Definition idx_msgType_dec: forall (k1 k2: IdxT * MsgType), {k1 = k2} + {k1 <> k2}.
    Proof.
      decide equality.
      - decide equality.
      - apply eq_nat_dec.
    Defined.
    Definition idx_msgType_add {A} (k: IdxT * MsgType) (v: A) m :=
      add idx_msgType_dec k v m.
    Definition idx_idx_dec: forall (k1 k2: IdxT * IdxT), {k1 = k2} + {k1 <> k2}.
    Proof.
      decide equality; apply eq_nat_dec.
    Defined.
    Definition idx_idx_add {A} (k: IdxT * IdxT) (v: A) m :=
      add idx_idx_dec k v m.

    (* Return the result handled meaningfully first by a rule. *)
    Fixpoint step_rule {StateT} (rules: list (RuleT StateT))
             (imsg: Msg) (st: StateT) :=
      match rules with
      | nil => None
      | r :: rules' =>
        match r imsg st with 
        | Some mst => Some mst
        | None => step_rule rules' imsg st
        end
      end.

    Inductive step_obj {StateT}:
      ObjectState StateT -> MsgsFrom ->
      list Msg -> option Msg (* (possibly) external_in *) -> list Msg (* external_out *) ->
      ObjectState StateT -> MsgsFrom -> Prop :=
    | StepObjInt: forall os msgs_from fidx fmsgT fmsg fmsgs imsgs_to emsgs_to pos,
        step_rule (obj_rules (os_obj os)) fmsg (os_state os) =
        Some (imsgs_to, emsgs_to, pos) ->
        find (fidx, fmsgT) msgs_from = Some (fmsg :: fmsgs) ->
        step_obj os msgs_from
                 imsgs_to None emsgs_to
                 {| os_obj := os_obj os;
                    os_state := pos |}
                 (idx_msgType_add (fidx, fmsgT) fmsgs msgs_from)
    | StepObjExt: forall os msgs_from emsg_in imsgs_to emsgs_to pos,
        step_rule (obj_rules (os_obj os)) emsg_in (os_state os) =
        Some (imsgs_to, emsgs_to, pos) ->
        step_obj os msgs_from
                 imsgs_to (Some emsg_in) emsgs_to
                 {| os_obj := os_obj os;
                    os_state := pos |}
                 msgs_from.

    Fixpoint distr_msgs (from: IdxT) (to: list Msg)
             (msgs: Messages): Messages :=
      match to with
      | nil => msgs
      | msg :: to' =>
        match find (msg_to msg) msgs with
        | Some toMsgs =>
          let added := match toMsgs (from, msg_type msg) with
                       | Some fromMsgs => fromMsgs ++ (msg :: nil)
                       | None => msg :: nil
                       end in
          idx_add (msg_to msg) (idx_msgType_add (from, msg_type msg) added toMsgs) msgs
        | None =>
          idx_add (msg_to msg) (idx_msgType_add (from, msg_type msg) (msg :: nil) (@empty _ _)) msgs
        end
      end.

    Inductive step : ObjectStates -> Messages ->
                     option Msg (* external in *) -> list Msg (* external out *) ->
                     ObjectStates -> Messages -> Prop :=
    | Step: forall oss idx {StateT} (os: ObjectState StateT)
                   oims msgs_from imsgs_to emsg_in emsg_out pos pmsgs_from,
        find idx oss = Some (existT _ _ os) ->
        find idx oims = Some msgs_from -> 
        step_obj os msgs_from imsgs_to emsg_in emsg_out pos pmsgs_from ->
        step oss oims emsg_in emsg_out
             (idx_add idx (existT _ _ pos) oss)
             (distr_msgs idx imsgs_to (idx_add idx pmsgs_from oims)).

    (* NOTE: the oldest is the head *)
    Definition addHistory (om: option Msg) (hst: list Msg) :=
      match om with
      | Some m => hst ++ (m :: nil)
      | None => hst
      end.
    Infix "<::" := addHistory (at level 30, right associativity).

    Inductive steps : ObjectStates -> Messages ->
                      list Msg (* history *) ->
                      ObjectStates -> Messages -> Prop :=
    | StepsNil: forall oss oims, steps oss oims nil oss oims
    | StepsCons:
        forall oss1 oims1 emsgs oss2 oims2,
          steps oss1 oims1 emsgs oss2 oims2 ->
          forall oss3 emsg_in emsg_out oims3,
            step oss2 oims2 emsg_in emsg_out oss3 oims3 ->
            steps oss1 oims1 (emsg_out ++ emsg_in <:: emsgs) oss3 oims3.

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

    Definition HistoryOf (obs: Objects) (hst: list Msg) :=
      exists oss oims, steps (getObjectStatesInit obs) (@empty _ _) hst oss oims.

    (** Now some notions borrowed from linearlizability and serializability.
     * Definitions need to be much more robust for the real language design.
     * It's for now a bit informal.
     *)

    (* A maximum subsequence of H consisting only of requests and matching responses. *)
    (* Should be a fancier implementation *)
    Fixpoint complete' (hst: list Msg) : (list Msg * Map (IdxT (* request_from *) *
                                                          IdxT (* request_to *)) nat) :=
      match hst with
      | nil => (nil, @empty _ _)
      | msg :: hst' =>
        let (chst, rs) := complete' hst' in
        if msg_type msg then (* request *)
          match find (msg_from msg, msg_to msg) rs with
          | Some (S n) => (msg :: chst, idx_idx_add (msg_from msg, msg_to msg) n rs)
          | _ => (chst, rs)
          end
        else (* response *)
          (msg :: chst, idx_idx_add (msg_to msg, msg_from msg)
                                    (match find (msg_to msg, msg_from msg) rs with
                                     | Some n => S n
                                     | None => 1
                                     end) rs)
      end.

    Definition complete (hst: list Msg) := fst (complete' hst).
    Definition Complete (hst: list Msg) := hst = complete hst.

    Fixpoint Serial' (hst: list Msg) (oi: option (IdxT (* request_from *) *
                                                  IdxT (* request_to *))) :=
      match hst with
      | nil => True
      | msg :: hst' =>
        match oi with
        | Some (from, to) => msg_to msg = from /\ msg_from msg = to /\ msg_type msg = Resp /\
                             Serial' hst' None
        | None => msg_type msg = Req /\ Serial' hst' (Some (msg_from msg, msg_to msg))
        end
      end.

    Definition Serial (hst: list Msg) := Serial' hst None.

    Definition subHistory (i: IdxT) (hst: list Msg) :=
      filter (fun e => if eq_nat_dec i (msg_to e) then true
                       else if eq_nat_dec i (msg_from e) then true
                            else false) hst.

    Definition Equivalent (hst1 hst2: list Msg) :=
      forall i, subHistory i hst1 = subHistory i hst2.

    Definition Serializable (hst shst: list Msg) :=
      Serial shst /\ Equivalent (complete hst) shst.

    Definition SerialObjects (obs: Objects) :=
      forall hst,
        HistoryOf obs hst ->
        exists shst, HistoryOf obs shst /\ Serializable hst shst.

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
      
    Lemma serial_serializable: forall hst, Serial hst -> Serializable hst (complete hst).
    Proof.
      intros; split; eauto.
    Qed.
    Hint Immediate serial_serializable.

    Lemma complete_serializable_app:
      forall hst1,
        Complete hst1 ->
        forall hst2 shst2, Serializable hst2 shst2 ->
                           Serializable (hst1 ++ hst2) (hst1 ++ shst2).
    Proof.
      unfold Serializable; intros.
      destruct H0.
      split; auto.

      rewrite complete_complete_app by assumption.
      apply equivalent_app; auto.
    Qed.

  End Facts.

End Language.

