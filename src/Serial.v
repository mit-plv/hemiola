Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics.

(* [sys] as a requester for [msg] *)
Definition asRequester (sys: System) (msg: Msg) :=
  if mid_rq (msg_id msg) ?<n (indicesOf sys) then true else false.

(* [sys] as a responder for [msg] *)
Definition asResponder (sys: System) (msg: Msg) :=
  if mid_rs (msg_id msg) ?<n (indicesOf sys) then true else false.

Definition rqSubHistory (sys: System) (hst: list Msg) :=
  filter (asRequester sys) hst.
Definition rsSubHistory (sys: System) (hst: list Msg) :=
  filter (asResponder sys) hst.

(* For a given system [sys] and its trace [tr], the history of [tr] is a request
 * subhistory with respect to [sys], where [lbl_hdl] is ignored.
 *)
Fixpoint historyOf (sys: System) (tr: list BLabel) :=
  match tr with
  | nil => nil
  | {| blbl_ins := ins; blbl_outs := outs |} :: tr' =>
    (rsSubHistory sys (outs ++ ins)) ++ (historyOf sys tr')
  end.

Inductive History : System -> list Msg -> Prop :=
| Hist: forall sys tr,
    Behavior sys tr ->
    History sys (historyOf sys tr).

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

Inductive SubHistory: list Msg -> list Msg -> Prop :=
| ShNil: SubHistory nil nil
| ShAdd: forall l1 l2, SubHistory l1 l2 -> forall a, SubHistory (a :: l1) (a :: l2)
| ShSkip: forall l1 l2, SubHistory l1 l2 -> forall a, SubHistory l1 (a :: l2).

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

(* A history [hst] is [Sequential] if:
 * 1) the first message is a request,
 * 2) a matching response for each request is right after the request, and
 * 3) there might not be a matching response for the last request.
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
  forall obj, requestsOf (rqSubHistory [obj] hst1) =
              requestsOf (rqSubHistory [obj] hst2).

(* NOTE: this may not be a complete definition:
 * Strict serializability (in concurrent system) requires one more condition: 
 * any _strict_ transaction orders are preserved by the serial history [shst].
 * I'm currently not sure if we need the second condition for message-passing 
 * systems.
 *)
Definition Serializable (hst shst: list Msg) :=
  Sequential shst /\
  Equivalent (complete hst) shst.

(* A system is [Serial] when all possible histories are [Serializable]. *)
Definition Serial (sys: System) :=
  forall hst,
    History sys hst ->
    exists lhst, History sys lhst /\
                 Serializable (rev hst) (rev lhst).

