Require Import Bool List String Peano_dec.
Require Import Common FMap.
Require Import Syntax Semantics.

Set Implicit Arguments.

Inductive RqRs := Rq | Rs.

Definition OPred :=
  Value (* input *) -> OrdOState -> Value (* output *) -> Prop.

Definition Pred :=
  Value (* input *) -> ObjectStates OrdOState -> Value (* output *) -> Prop.

Record OTrs :=
  { otrs_rqval: Value;
    otrs_rqpred: Pred;
    otrs_opred: OPred;
    otrs_rsbf: list Value -> OrdOState -> Value }.

Inductive PMsg : RqRs -> Type :=
| PMsgIntro: forall (mid: MsgId) (rr: RqRs) (val: Value) (pred: Pred), PMsg rr.

Definition midOfPMsg {rr} (pmsg: PMsg rr): MsgId :=
  match pmsg with
  | PMsgIntro mid _ _ _ => mid
  end.

Definition valOfPMsg {rr} (pmsg: PMsg rr): Value :=
  match pmsg with
  | PMsgIntro _ _ val _ => val
  end.

Definition predOfPMsg {rr} (pmsg: PMsg rr): Pred :=
  match pmsg with
  | PMsgIntro _ _ _ pred => pred
  end.

Global Instance PMsg_HasMsg (rr: RqRs): HasMsg (PMsg rr) :=
  {| getMsg := fun pmsg =>
                 match pmsg with
                 | PMsgIntro mid rr val pred => buildMsg mid val
                 end |}.

Global Instance PMsg_sigT_HasMsg : HasMsg { rr : RqRs & PMsg rr } :=
  {| getMsg := fun pmsg =>
                 match projT2 pmsg with
                 | PMsgIntro mid rr val pred => buildMsg mid val
                 end |}.

Section PLabel.

  Inductive PLabel :=
  | PlblEmpty: PLabel
  | PlblIn (min: PMsg Rq): PLabel
  | PlblImm (min: PMsg Rq) (mout: PMsg Rs): PLabel
  | PlblRqFwd (min: PMsg Rq) (mfwds: list (PMsg Rq)): PLabel
  | PlblRsBack (mins: list (PMsg Rs)) (mback: PMsg Rs): PLabel.

  Definition pToLabel (l: PLabel): Label :=
    match l with
    | PlblEmpty => LblOuts nil
    | PlblIn min => LblIn (getMsg min)
    | PlblImm min mout => LblOuts (getMsg mout :: nil)
    | PlblRqFwd min mfwds => LblOuts (map getMsg mfwds)
    | PlblRsBack mins mback => LblOuts (getMsg mback :: nil)
    end.

  Global Instance PLabel_HasLabel: HasLabel PLabel :=
    { getLabel := pToLabel }.

End PLabel.

Record PObject :=
  { pobj_idx: nat;
    pobj_state_init: OrdOState
  }.

Global Instance PObject_IsObject : IsObject OrdOState PObject :=
  {| getIndex := pobj_idx;
     getOStateInit := pobj_state_init |}.

Definition Topo := list MsgAddr.

Record PSystem :=
  { psys_topo: Topo;
    psys_obs: list PObject }.

Global Instance PSystem_HasObjects : HasObjects PSystem :=
  {| getObjects := psys_obs |}.

Record PState :=
  { pst_oss: ObjectStates OrdOState;
    pst_otrs: M.t OTrs;
    pst_msgs: MessagePool { rr: RqRs & PMsg rr }
  }.

Definition getPStateInit (psys: PSystem): PState :=
  {| pst_oss := getObjectStatesInit (psys_obs psys);
     pst_otrs := [];
     pst_msgs := nil |}.

Global Instance PState_HasInit: HasInit PSystem PState :=
  { getStateInit := getPStateInit }.

(* Definition PHistory := list PLabel. *)

(* Inductive step_pred: PSystem -> PState -> PHistory -> PState -> Prop := *)
(* | SpDone: forall psys st, step_pred psys st nil st *)
(* | SpSlt: forall psys st1 st2 hst, *)
(*     step_pred psys st1 hst st2 -> *)
(*     step_pred psys st1 (PlblEmpty :: hst) st2 *)

(* | SpIn: *)
(*     forall psys mid val pred oss otrs msgs phst pst, *)
(*       isExternal psys (mid_from mid) = true -> *)
(*       isInternal psys (mid_to mid) = true -> *)

(*       step_pred psys *)
(*                 {| pst_oss := oss; *)
(*                    pst_otrs := otrs; *)
(*                    pst_msgs := enqMP (existT _ _ (PMsgIntro mid Rq val pred)) msgs *)
(*                 |} *)
(*                 phst pst -> *)

(*       step_pred psys *)
(*                 {| pst_oss := oss; pst_otrs := otrs; pst_msgs := msgs |} *)
(*                 (PlblIn (PMsgIntro mid Rq val pred) :: phst) *)
(*                 pst. *)

Inductive step_pred (psys: PSystem): PState -> PLabel -> PState -> Prop :=
| SpSlt: forall st, step_pred psys st PlblEmpty st

| SpIn:
    forall mid val pred oss otrs msgs,
      isExternal psys (mid_from mid) = true ->
      isInternal psys (mid_to mid) = true ->
      step_pred psys
                {| pst_oss := oss; pst_otrs := otrs; pst_msgs := msgs |}
                (PlblIn (PMsgIntro mid Rq val pred))
                {| pst_oss := oss;
                   pst_otrs := otrs;
                   pst_msgs := enqMP (existT _ _ (PMsgIntro mid Rq val pred)) msgs
                |}

| SpImm:
    forall mid rq rs rqVal rsVal pred oidx nos oss otrs msgs,
      rq = PMsgIntro mid Rq rqVal pred ->
      rs = PMsgIntro mid Rs rsVal pred ->

      FirstMP msgs (existT _ _ rq) ->
      ValidMsgsIn oidx (rq :: nil) ->
      ValidMsgOuts oidx (rs :: nil) ->
      pred rqVal (oss +[oidx <- nos]) rsVal ->

      step_pred psys
                {| pst_oss := oss; pst_otrs := otrs; pst_msgs := msgs |}
                (PlblImm rq rs)
                {| pst_oss := oss +[ oidx <- nos ];
                   pst_otrs := otrs;
                   pst_msgs := distributeMsgs
                                 (intOuts psys (existT _ _ rs :: nil))
                                 (removeMP (existT _ _ rq) msgs) |}

| SpRqFwd:
    forall oidx rq fwds oss otrs opred rsbf msgs,
      FirstMP msgs (existT _ _ rq) ->
      ValidMsgsIn oidx (rq :: nil) ->
      ValidMsgOuts oidx fwds ->
      Forall (fun pmsg =>
                isInternal psys (mid_to (msg_id (getMsg pmsg))) = true) fwds ->
      
      step_pred psys
                {| pst_oss := oss; pst_otrs := otrs; pst_msgs := msgs |}
                (PlblRqFwd rq fwds)
                {| pst_oss := oss;
                   pst_otrs := otrs +[ oidx <- {| otrs_rqval := valOfPMsg rq;
                                                  otrs_rqpred := predOfPMsg rq;
                                                  otrs_opred := opred;
                                                  otrs_rsbf := rsbf |} ];
                   pst_msgs := distributeMsgs
                                 (map (fun pmsg => existT _ _ pmsg) fwds)
                                 (removeMP (existT _ _ rq) msgs) |}

| SpRsBack:
    forall oidx rss rsb otrs ootrs oss msgs,
      Forall (FirstMP msgs) (map (existT _ _) rss) ->
      ValidMsgsIn oidx rss ->
      ValidMsgOuts oidx (rsb :: nil) ->
      Forall (fun pmsg =>
                isInternal psys (mid_from (msg_id (getMsg pmsg))) = true) rss ->

      otrs@[oidx] = Some ootrs ->
      
      (* predOfPMsg rsb (otrs_rqval rqval) (oss +[oidx <- nos]) (valOfPMsg rsb) *)

      step_pred psys
                {| pst_oss := oss; pst_otrs := otrs; pst_msgs := msgs |}
                (PlblRsBack rss rsb)
                {| pst_oss := oss;
                   pst_otrs := M.remove oidx otrs;
                   pst_msgs := distributeMsgs
                                 (intOuts psys (existT _ _ rsb :: nil))
                                 (removeMsgs (map (existT _ _) rss) msgs) |}.

(** What we want, informally:
 * - [step_det] with particular rules -> [step_pred]
 * - [step_det] with particular rules -> [Transactional] history ->
 *   postconditions in [step_pred] are preserved.
 *
 * - Do we need to specify preconditions in [step_pred]? I think no, because
 *   those are only about "sate interleavings", i.e., serializability.
*)

