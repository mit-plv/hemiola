Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepT.

(** [Atomic] and [Transactional] histories *)

Section PerSystem.
  Variable sys: System.

  (* A history is [Atomic] if it satisfies following conditions:
   * 1) The history can be either an incomplete or a complete transaction.
   * 2) The history always begins by handling an external message.
   * 3) Each label in the history has a form of [RlblOuts (Some hdl) _],
   *    and all [hdl]s have the same [tinfo_tid]. It means that the history is
   *    for a single transaction.
   *)
  Inductive Atomic: TrsId -> Msg -> THistory -> MessagePool TMsg -> Prop :=
  | AtomicStart:
      forall ts rqr rq houts,
        fromExternal sys rq = true ->
        ForallMP (fun tmsg => tmsg_info tmsg =
                              Some (buildTInfo ts (rq :: nil))) houts ->
        Atomic ts rq (RlblOuts (Some rqr) (toTMsgU rq :: nil) houts :: nil) houts
  | AtomicCont:
      forall ts rq hst rule msgs mouts houts,
        Atomic ts rq hst mouts ->
        msgs <> nil ->
        SubList msgs mouts ->
        Atomic ts rq (RlblOuts (Some rule) msgs houts :: hst)
               (distributeMsgs houts (removeMsgs msgs mouts)).

  Inductive Transactional: THistory -> Prop :=
  | TrsSlt:
      Transactional (emptyRLabel :: nil)
  | TrsIn:
      forall msg tin,
        tin = RlblIn msg ->
        Transactional (tin :: nil)
  | TrsAtomic:
      forall ts rq hst mouts,
        Atomic ts rq hst mouts ->
        Transactional hst.

  Definition Sequential (hst: THistory) :=
    exists trss: list THistory,
      Forall Transactional trss /\
      hst = List.concat trss.

End PerSystem.

(** Transaction messages in [MessagePool] *)

Definition trsMessages (trsInfo: TInfo) (mp: MessagePool TMsg) : list TMsg :=
  filter (fun tmsg =>
            match tmsg_info tmsg with
            | Some tinfo => if tinfo_dec tinfo trsInfo then true else false
            | None => false
            end) mp.

(** Serializability *)

Definition trsSteps (sys: System) (st1: TState) (hst: THistory) (st2: TState) :=
  steps step_t sys st1 hst st2 /\
  Transactional sys hst.

Definition seqSteps (sys: System) (st1: TState) (hst: THistory) (st2: TState) :=
  steps step_t sys st1 hst st2 /\
  Sequential sys hst.

Definition BEquivalent (sys: System)
           {LabelT} `{HasLabel LabelT} (ll1 ll2: list LabelT) :=
  behaviorOf sys ll1 = behaviorOf sys ll2.

Definition Serializable (sys: System) (ll: THistory) :=
  exists sll sst,
    (* 1) legal and sequential *) seqSteps sys (initsOf sys) sll sst /\
    (* 3) equivalent *) BEquivalent sys ll sll.

(* A system is serializable when all possible behaviors are [Serializable]. *)
Definition SerializableSys (sys: System) :=
  forall ll st,
    steps step_t sys (initsOf sys) ll st ->
    Serializable sys ll.


(** Let's start (experimentally) with an obvious condition 
 * that ensures [SerializableSys] 
 *)

Definition TotallyBlockingPrec: RPrecond :=
  fun ost orq ins =>
    SubList (map (fun msg => mid_tid (msg_id msg)) ins)
            (map (fun msg => mid_tid (msg_id msg)) orq).

Definition TotallyBlockingRule (rule: Rule) :=
  (rule_precond rule) ->rprec TotallyBlockingPrec.

Definition TotallyBlockingSys (sys: System) :=
  Forall TotallyBlockingRule (sys_rules sys).

Theorem TotallyBlockingSys_SerializableSys:
  forall sys, TotallyBlockingSys sys -> SerializableSys sys.
Proof.
  unfold SerializableSys, Serializable; intros.
  eexists; exists st; split; [split|].
Admitted.
  
