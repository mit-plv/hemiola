Require Import Peano_dec List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics Serial Topology StepM.

(** TODOs:
 * 0. Maybe better to have a notion of [Multipath] including the "type"
 *    of each edge (e.g., upward-request, downward-request, etc.)
 * 1. An [Atomic] step --> exists a corresponding [Multipath]
 * 2. Any history [hst] between continuous histories [h1] and [h2]:
 *    first we need to confirm whether [hst] is right- or left-pushable.
 * 3. Theorem: informally, [forall hst, hst ⊆ rssOf(h1) \/ hst ⊆ rssOf(h2)],
 *    where [rssOf] returns all responses of the history.
 * 3-2. Theorem: [rssOf(h1)] and [rssOf(h2)] are totally disjoint.
 * 4. Theorem: if [hst ⊆ rssOf(hi)] (i = 1(left) or 2(right)), then [hst] is
 *    i-pushable.
 * 4-2. How to prove (4):
 *   + WLOG, let's say [hst ⊆ rssOf(h1)].
 *   + Every response in [h2] is commutable with [hst] because of (3-2).
 *   + Now for each request [rq ∈ h2]:
 *     * If the request is downward, it made a complete lock before [hst],
 *       thus [objectOf(rq) ∉ objectsOf(hst)]. Thus [hst] and [rq] are 
 *       commutable.
 *     * If the request is upward, we would've had a static condition claiming
 *       that every possible state transition of [objectOf(rq)] does not affect
 *       the precondition of [rq]. Since [rq] is not making any state 
 *       transition, [hst] and [rq] are commutable.
 *)

Definition EdgeEquiv (e1 e2: edge) :=
  match edge_from e1, edge_from e2 with
  | Some fr1, Some fr2 => fr1 = fr2
  | _, _ => True
  end /\
  edge_chn e1 = edge_chn e2 /\
  match edge_to e1, edge_to e2 with
  | Some fr1, Some fr2 => fr1 = fr2
  | _, _ => True
  end.

Fixpoint EdgeIn (ie: edge) (es: edges) :=
  match es with
  | nil => False
  | e :: es' => EdgeEquiv e ie \/ EdgeIn e es'
  end.

Inductive Multipath (dg: digraph):
  edges (* initial edges *) ->
  edges (* all involved edges *) ->
  vertices (* all involved vertices *) ->
  edges (* end edges *) -> Prop :=
| MultipathNil: forall es, Multipath dg es es nil es
| MultipathDiv:
    forall ies es vs ees e des,
      Multipath dg ies es vs ees ->
      EdgeIn e ees -> edge_to e <> None ->
      des <> nil -> NoDup (map edge_to des) ->
      Forall (fun de => edge_from de = edge_to e) des ->
      Multipath dg ies (es ++ des) (vs ++ o2l (edge_to e))
                (removeOnce edge_dec e ees ++ des)
| MultipathConv:
    forall ies es vs ees e ces,
      Multipath dg ies es vs ees ->
      Forall (fun ce => EdgeIn ce ees) ces ->
      ces <> nil -> NoDup (map edge_from ces) ->
      Forall (fun ce => edge_to ce = edge_from e) ces ->
      Multipath dg ies (es ++ [e])
                (oapp vs (map edge_from ces))
                (removeL edge_dec ees ces ++ [e]).

Section Topological.
  Variable (dg: digraph).

  Context {MsgT: Type}.
  
  Definition TopoValidLabel (l: RLabel MsgT) :=
    match l with
    | RlblEmpty _ => True
    | RlblIns eins =>
      exists ito,
      Forall (fun im =>
                In (Build_edge None (idOf im) (Some ito)) (dg_es dg)) eins
    | RlblInt oidx ridx ins outs =>
      Forall (fun im =>
                exists ifrom,
                  In (Build_edge ifrom (idOf im) (Some oidx))
                     (dg_es dg)) ins /\
      Forall (fun im =>
                exists ito,
                  In (Build_edge (Some oidx) (idOf im) ito)
                     (dg_es dg)) outs
    | RlblOuts eouts =>
      exists ifrom,
      Forall (fun im =>
                In (Build_edge ifrom (idOf im) None) (dg_es dg)) eouts
    end.

  Definition TopoValidHistory (hst: History MsgT) :=
    Forall TopoValidLabel hst.

End Topological.

Definition getInEdges {MsgT} (ins: list (Id MsgT)) (to: IdxT): edges :=
  map (fun im => Build_edge None (idOf im) (Some to)) ins.

Definition getOutEdges {MsgT} (from: IdxT) (outs: list (Id MsgT)): edges :=
  map (fun im => Build_edge (Some from) (idOf im) None) outs.

Definition getInitEdges {MsgT} (hst: History MsgT): edges :=
  (hd_error (rev hst)) >>=[nil]
  (fun lbl =>
     match lbl with
     | RlblInt oidx ridx ins outs => getInEdges ins oidx
     | _ => nil
     end).

(* TODO: may also need to derive [es], [vs], and [ees] from [hst]. *)
Lemma atomic_multipath:
  forall sys st1 hst st2,
    steps step_m sys st1 hst st2 ->
    forall inits ins outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall dg,
        TopoValidHistory dg hst ->
        exists es vs ees,
          Multipath dg (getInitEdges hst) es vs ees.
Proof.
Admitted.

