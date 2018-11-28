Require Import Peano_dec List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics StepM Serial.
Require Import Topology RqRs.

Open Scope list.
Open Scope fmap.

(** TODOs:
 * 0. Have a notion of transaction paths ([TrsPath]) that includes a 
 *    "transaction type" of each object (e.g., upward-request, downward-request,
 *    etc.).
 * 1. An [Atomic] step --> exists a corresponding [TrsPath]
 * 2. For each history [hst] between continuous histories [h1] and [h2]:
 *    we need to have a way to check whether [hst] is right- or left-pushable.
 * 3. 1) Theorem (disjointness between [h1] and [h2]):
 *    [h1 -*- h2], where 
 *    [h1 -*- h2 ≜ rqsOf(h1) -*- rqsOf(h2) /\ rssOf(h1) -*- rssOf(h2)].
 *    Note that [-*-] is not commutative.
 *    2) Theorem (disjointness of [hst]): [∀hst. h1 -*- hst \/ hst -*- h2]
 * 4. Theorem: [∀h1 h2. h1 -*- h2 -> Discontinuous h1 h2 -> Commutable h1 h2]
 *)

Inductive TrsType := RqUp | RqDown | Rs.

Definition TrsState := M.t TrsType. (* Object index -> TrsType *)

Section RqRsTopo.

  Inductive RqRsTopo: DTree -> Prop :=
  | RqRsNode:
      forall ridx cs,
        Forall (fun udc =>
                  List.length (fst (fst udc)) = 2 /\ (* Two upward channels *)
                  List.length (snd (fst udc)) = 1 /\ (* A single downward channel *)
                  RqRsTopo (snd udc)) cs ->
        RqRsTopo (Node ridx cs).

  (* NOTE: should have length 2 if [RqRsTopo gtr] *)
  Definition edgesUpFrom (gtr: DTree) (oidx: IdxT): list IdxT :=
    map (fun e => snd e.(edge_chn)) (upEdgesFrom gtr oidx).

  Definition edgesUpTo (gtr: DTree) (oidx: IdxT): list IdxT :=
    map (fun e => snd e.(edge_chn)) (upEdgesTo gtr oidx).

  (* NOTE: should have length 1 if [RqRsTopo gtr] *)
  Definition edgesDownFrom (gtr: DTree) (oidx: IdxT): list IdxT :=
    map (fun e => snd e.(edge_chn)) (downEdgesFrom gtr oidx).

  (* NOTE: should have length 1 if [RqRsTopo gtr] *)
  Definition edgesDownTo (gtr: DTree) (oidx: IdxT): list IdxT :=
    map (fun e => snd e.(edge_chn)) (downEdgesTo gtr oidx).

End RqRsTopo.

Section OnTreeTopo.

  Variable (gtr: DTree).

  Variables (oidx: IdxT) (oifc: OStateIfc).

  (** TODO: discuss whether it's fine to have a locking mechanism 
   * only for a single address. *)
  Definition LockFree: OPrec oifc :=
    fun ost orq mins => LockFree orq O.
  
  Section PerTransaction.

    Variable (trsId: IdxT).

    Definition RqUpRule ridx prec trs: Rule oifc :=
      {| rule_idx := ridx;
         rule_msg_ids_from := [trsId];
         rule_msg_ids_to := [trsId];
         rule_precond := prec;
         rule_trs := trs 
      |}.

    (** TODO: should also ensure that it emits a valid RqUp message. *)
    (* Definition RqUpRuleOk (rule: Rule oifc) := *)
    (*   rule.(rule_precond) *)
    (*   ->oprec (MsgsFrom [rqUpFrom gtr oidx] /\oprec LockFree). *)

    (** TODOs:
     * 1) Define [RqUpRule], [RqDownRule], and [RsRule]
     * 2) Define a system just using such rules.
     * 3) Prove that under such a system each [Atomic] step has a corresponding
     *    [TrsPath].
     *)
  
    (* NOTE: we cannot make both upward and downward requests at the same time,
     * thus we have separate constructors [TrsPathRqUp] and [TrsPathRqDown].
     *)
    Inductive TrsPath:
      edge DChn (* an initial edge *) ->
      edges DChn (* all involved edges *) ->
      TrsState (* all involved vertices *) ->
      edges DChn (* end edges *) -> Prop :=
    | TrsPathNil: forall ie, TrsPath ie [ie] [] [ie]
    | TrsPathRqUp:
        forall ie es tst ees e v ne,
          TrsPath ie es tst ees ->
          In e ees -> edge_to e = Some v ->
          edge_from ne = Some v -> fst ne.(edge_chn) = DUp ->
          tst@[v] = None ->
          TrsPath ie (ne :: es) (tst +[v <- RqUp])
                  (ne :: removeOnce (edge_dec dchn_dec) e ees)
    | TrsPathRqDown:
        forall ie es tst ees e v nes,
          TrsPath ie es tst ees ->
          In e ees -> edge_to e = Some v ->
          Forall (fun ne => edge_from ne = Some v /\ fst ne.(edge_chn) = DDown) nes ->
          (tst@[v] = None \/ tst@[v] = Some RqUp) ->
          TrsPath ie (nes ++ es) (tst +[v <- RqDown])
                  (nes ++ removeOnce (edge_dec dchn_dec) e ees)
    | TrsPathRs:
        forall ie es tst ees rss v rsb,
          TrsPath ie es tst ees ->
          SubList rss ees ->
          Forall (fun rse => edge_from rse <> None /\ edge_to rse = Some v) rss ->
          NoDup (map (@edge_from _) rss) ->
          (tst@[v] = Some RqUp \/ tst@[v] = Some RqDown) ->
          EdgeIn gtr rsb ->
          TrsPath ie (rsb :: es) (tst +[v <- Rs])
                  (rsb :: removeL (edge_dec dchn_dec) ees rss).

  End PerTransaction.

End OnTreeTopo.

(* Section Topological. *)
(*   Variable (dg: digraph). *)

(*   Context {MsgT: Type}. *)
  
(*   Definition TopoValidLabel (l: RLabel MsgT) := *)
(*     match l with *)
(*     | RlblEmpty _ => True *)
(*     | RlblIns eins => *)
(*       exists ito, *)
(*       Forall (fun im => *)
(*                 In (Build_edge None (idOf im) (Some ito)) (dg_es dg)) eins *)
(*     | RlblInt oidx ridx ins outs => *)
(*       Forall (fun im => *)
(*                 exists ifrom, *)
(*                   In (Build_edge ifrom (idOf im) (Some oidx)) *)
(*                      (dg_es dg)) ins /\ *)
(*       Forall (fun im => *)
(*                 exists ito, *)
(*                   In (Build_edge (Some oidx) (idOf im) ito) *)
(*                      (dg_es dg)) outs *)
(*     | RlblOuts eouts => *)
(*       exists ifrom, *)
(*       Forall (fun im => *)
(*                 In (Build_edge ifrom (idOf im) None) (dg_es dg)) eouts *)
(*     end. *)

(*   Definition TopoValidHistory (hst: History MsgT) := *)
(*     Forall TopoValidLabel hst. *)

(* End Topological. *)

(* Definition getInEdges {MsgT} (ins: list (Id MsgT)) (to: IdxT): edges := *)
(*   map (fun im => Build_edge None (idOf im) (Some to)) ins. *)

(* Definition getOutEdges {MsgT} (from: IdxT) (outs: list (Id MsgT)): edges := *)
(*   map (fun im => Build_edge (Some from) (idOf im) None) outs. *)

(* Definition getInitEdges {MsgT} (hst: History MsgT): edges := *)
(*   (hd_error (rev hst)) >>=[nil] *)
(*   (fun lbl => *)
(*      match lbl with *)
(*      | RlblInt oidx ridx ins outs => getInEdges ins oidx *)
(*      | _ => nil *)
(*      end). *)

(* (* TODO: may also need to derive [es], [vs], and [ees] from [hst]. *) *)
(* Lemma atomic_multipath: *)
(*   forall {oifc} (sys: System oifc) st1 hst st2, *)
(*     steps step_m sys st1 hst st2 -> *)
(*     forall inits ins outs eouts, *)
(*       Atomic msg_dec inits ins hst outs eouts -> *)
(*       forall dg, *)
(*         TopoValidHistory dg hst -> *)
(*         exists es vs ees, *)
(*           Multipath dg (getInitEdges hst) es vs ees. *)
(* Proof. *)
(* Admitted. *)

Close Scope list.
Close Scope fmap.

