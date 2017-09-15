Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics.

(* In message passing system, a "process" (or "thread") refers to a 
 * "requester" and an "objects" (or "system") refers to a "requestee".
 * Thus, for a given message {| mid_rq := i; mid_rs := j; mid_rqrs := _ |},
 * its requester (process) is "i" and the (target) object is "j".
 *)

(* [sys] acts as a processor for [msg]. *)
Definition asProcessor (sys: System) (msg: Msg) :=
  if mid_rq (msg_id msg) ?<n (indicesOf sys) then true else false.
Definition asSystem (sys: System) (msg: Msg) :=
  if mid_rs (msg_id msg) ?<n (indicesOf sys) then true else false.

Definition sysSubHistory (sys: System) (hst: list Msg) :=
  filter (asSystem sys) hst.
Definition procSubHistory (sys: System) (hst: list Msg) :=
  filter (asProcessor sys) hst.

(* For a given system [sys] and its trace [tr], the history of [tr] is an
 * object subhistory with respect to [sys], where [lbl_hdl] is ignored.
 *)
Fixpoint historyOf (sys: System) (tr: list Label) :=
  match tr with
  | nil => nil
  | {| lbl_ins := ins; lbl_outs := outs |} :: tr' =>
    (sysSubHistory sys (outs ++ ins)) ++ (historyOf sys tr')
  end.

Inductive History : System -> list Msg -> Prop :=
| Hist: forall sys ll st,
    steps sys (getStateInit sys) ll st ->
    History sys (historyOf sys ll).

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
    match mid_rqrs (msg_id msg) with
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
    | None => match mid_rqrs (msg_id msg) with
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

Definition requestsOf (hst: list Msg) :=
  filter (fun m => match mid_rqrs (msg_id m) with
                   | Rq => true
                   | _ => false
                   end) hst.

(* Two histories are equivalent if
 * 1) one history is a permutation of the other, and
 * 2) they have the same request orders per a process.
 *)
Definition Equivalent (hst1 hst2: list Msg) :=
  Permutation hst1 hst2 /\
  forall obj, requestsOf (procSubHistory [obj] hst1) =
              requestsOf (procSubHistory [obj] hst2).

(* NOTE: this is actually not a fully correct definition:
 * Linearizability requires one more condition: any _strict_ transaction
 * orders are preserved by [lhst].
 * I'm currently not sure if we need the second condition for 
 * message-passing systems.
 *)
Definition Linearizable (hst lhst: list Msg) :=
  Sequential lhst /\
  Equivalent (complete hst) lhst.

(* A system is linear when all possible histories are linearizable. *)
Definition Linear (sys: System) :=
  forall hst,
    History sys hst ->
    exists lhst, History sys lhst /\
                 Linearizable (rev hst) (rev lhst).

