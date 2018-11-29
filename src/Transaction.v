Require Import Peano_dec List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics StepM Serial.
Require Import Topology.

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

Section HalfLock.
  Variable (gtr: DTree).

  Definition upRq := 0.
  Definition downRq := 1.

  (** Preconditions to check the lock state *)

  Definition LockFree (orq: ORq Msg) (addr: AddrT) :=
    orq@[addr] >>=[True] (fun aorq => aorq = []).

  Definition HalfLockFree (orq: ORq Msg) (addr: AddrT) :=
    orq@[addr] >>=[True] (fun aorq => aorq@[downRq] = None).

  Definition Locked (orq: ORq Msg) (addr: AddrT) :=
    orq@[addr] >>=[False] (fun aorq => aorq@[downRq] <> None).

  Definition HalfLocked (orq: ORq Msg) (addr: AddrT) :=
    orq@[addr] >>=[False] (fun aorq => aorq@[downRq] = None /\
                                       aorq@[upRq] <> None).

End HalfLock.

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
  Definition LockFree0: OPrec oifc :=
    fun ost orq mins => LockFree orq O.

  Definition HalfLockFree0: OPrec oifc :=
    fun ost orq mins => HalfLockFree orq O.

  Definition Locking0 (otrs: OTrs oifc): Prop :=
    forall ost orq mins,
      Locked (snd (fst (otrs ost orq mins))) O.

  Definition HalfLocking0 (otrs: OTrs oifc): Prop :=
    forall ost orq mins,
      HalfLocked (snd (fst (otrs ost orq mins))) O.

  Section PerTransaction.

    Variable (trsId: IdxT).

    (* Definition OneToOneRule ridx prec trs: Rule oifc := *)
    (*   {| rule_idx := ridx; *)
    (*      rule_msg_ids_from := [trsId]; *)
    (*      rule_msg_ids_to := [trsId]; *)
    (*      rule_precond := prec; *)
    (*      rule_trs := trs *)
    (*   |}. *)

    (** * Rule predicates about which messages to handle *)

    (* A rule handling a request from one of its children *)
    Definition RqFromDownRule (rule: Rule oifc) :=
      exists rqFrom,
        In rqFrom (edgesUpTo gtr oidx) /\
        (rule.(rule_precond) ->oprec (MsgsFrom [rqFrom] /\oprec LockFree0)).

    (* A rule handling a request from the parent *)
    Definition RqFromUpRule (rule: Rule oifc) :=
      exists rqFrom,
        In rqFrom (edgesDownTo gtr oidx) /\
        (rule.(rule_precond) ->oprec (MsgsFrom [rqFrom] /\oprec HalfLockFree0)).

    (* A rule handling responses from some of its children *)
    (** NOTE: we don't need any lock conditions when dealing with responses.
     * To prove liveness, we may need some conditions about proper lock release.
     * But for correctness, we don't need any.
     *)
    Definition RsFromDownRule (rule: Rule oifc) :=
      exists rssFrom,
        SubList rssFrom (edgesUpTo gtr oidx) /\ NoDup rssFrom /\
        (rule.(rule_precond) ->oprec MsgsFrom rssFrom).

    (* A rule handling a response from the parent *)
    Definition RsFromUpRule (rule: Rule oifc) :=
      exists rsFrom,
        In rsFrom (edgesDownTo gtr oidx) /\
        (rule.(rule_precond) ->oprec MsgsFrom [rsFrom]).

    (** * Rule predicates about which messages to emit *)

    (* A rule making requests to some of its children *)
    Definition RqToDownRule (rule: Rule oifc) :=
      exists rqsTo,
        SubList rqsTo (edgesDownFrom gtr oidx) /\ NoDup rqsTo /\
        MsgsTo rqsTo rule.(rule_trs) /\
        Locking0 rule.(rule_trs).

    (* A rule making a request to the parent *)
    Definition RqToUpRule (rule: Rule oifc) :=
      exists rqTo,
        In rqTo (edgesUpFrom gtr oidx) /\
        MsgsTo [rqTo] rule.(rule_trs) /\
        HalfLocking0 rule.(rule_trs).

    (* A rule making a response to one of its children *)
    Definition RsToDownRule (rule: Rule oifc) :=
      exists rsTo,
        In rsTo (edgesDownFrom gtr oidx) /\
        MsgsTo [rsTo] rule.(rule_trs).
    
    (* A rule making a response to the parent *)
    Definition RsToUpRule (rule: Rule oifc) :=
      exists rsTo,
        In rsTo (edgesUpFrom gtr oidx) /\
        MsgsTo [rsTo] rule.(rule_trs).

    (* TODO: define it. *)
    (* Definition HalfLockPrec (oidx: IdxT) {oifc}: OPrec oifc := *)
    (*   fun (ost: OState oifc) (orq: ORq Msg) (ins: list (Id Msg)) => *)
    (*     True. *)

    (* Definition HalfLockRule (oidx: IdxT) {oifc} (rule: Rule oifc) := *)
    (*   (rule_precond rule) ->oprec (HalfLockPrec oidx). *)

    (* Definition HalfLockObj {oifc} (obj: Object oifc) := *)
    (*   Forall (HalfLockRule (obj_idx obj)) (obj_rules obj). *)
    
    (* Definition HalfLockSys {oifc} (sys: System oifc) := *)
    (*   Forall HalfLockObj (sys_objs sys). *)
    
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

