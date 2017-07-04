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

    Definition InMsgs := Map IdxT (list Msg).

    Definition ObjectInMsgs := Map IdxT InMsgs.

    Definition idx_add {A} (k: IdxT) (v: A) m :=
      add eq_nat_dec k v m.

    Fixpoint step_rule {StateT} (rules: list (RuleT StateT))
             (imsg: IMsg) (st: StateT) :=
      match rules with
      | nil => (nil, None, st)
      | r :: rules' =>
        match r imsg st with 
        | Some mst => mst
        | None => step_rule rules' imsg st
        end
      end.

    Inductive step_obj {StateT}:
      ObjectState StateT -> InMsgs ->
      list IMsg -> option IMsg (* external_in *) -> option IMsg (* external_out *) ->
      ObjectState StateT -> InMsgs -> Prop :=
    | StepObjInt: forall os imsgs fidx fmsg fmsgs imsgs_to emsgs_to pos,
        step_rule (obj_rules (os_obj os)) (fidx, fmsg) (os_state os) =
        (imsgs_to, emsgs_to, pos) ->
        find fidx imsgs = Some (fmsg :: fmsgs) ->
        step_obj os imsgs
                 imsgs_to None emsgs_to
                 {| os_obj := os_obj os;
                    os_state := pos |}
                 (idx_add fidx fmsgs imsgs)
    | StepObjExt: forall os imsgs emsg_in imsgs_to emsgs_to pos,
        step_rule (obj_rules (os_obj os)) emsg_in (os_state os) =
        (imsgs_to, emsgs_to, pos) ->
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
        match msgs toIdx with
        | Some toMsgs =>
          let added := match toMsgs from with
                       | Some fromMsgs => fromMsgs ++ (msg :: nil)
                       | None => msg :: nil
                       end in
          idx_add toIdx (idx_add from added toMsgs) msgs
        | None =>
          idx_add toIdx (idx_add from (msg :: nil) (@empty _ _)) msgs
        end
      end.

    Inductive step : ObjectStates -> ObjectInMsgs ->
                     option IMsg (* external in *) -> option IMsg (* external out *) ->
                     ObjectStates -> ObjectInMsgs -> Prop :=
    | Step: forall oss idx {StateT} (os: ObjectState StateT)
                   oims imsgs imsgs_to emsg_in emsg_out pos pimsgs,
        find idx oss = Some (existT _ _ os) ->
        find idx oims = Some imsgs -> 
        step_obj os imsgs imsgs_to emsg_in emsg_out pos pimsgs ->
        step oss oims emsg_in emsg_out
             (idx_add idx (existT _ _ pos) oss)
             (distr_msgs idx imsgs_to (idx_add idx pimsgs oims)).

    Definition addHistory (om: option IMsg) (hst: list IMsg) :=
      match om with
      | Some m => m :: hst
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

    Fixpoint serial' (hst: list IMsg) (oi: option IdxT) :=
      match hst with
      | nil => True
      | (idx, msg) :: hst' =>
        match oi with
        | Some i => idx = i /\ msg_is_req msg = false /\
                    serial' hst' None
        | None => msg_is_req msg = true /\ serial' hst' (Some idx)
        end
      end.

    Definition serial (hst: list IMsg) := serial' hst None.

    Definition subHistory (i: IdxT) (hst: list IMsg) :=
      filter (fun e => if eq_nat_dec i (fst e) then true else false) hst.

    Definition Equivalent (tr1 tr2: list IMsg) :=
      forall i, subHistory i tr1 = subHistory i tr2.

    Definition Serializable (tr: list IMsg) :=
      exists str, serial str /\ Equivalent tr str.

  End Semantics.

End Language.

