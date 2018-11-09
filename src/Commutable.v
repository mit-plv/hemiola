Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM StepT SemFacts.
Require Import Topology Serial SerialFacts Reduction.

Set Implicit Arguments.

Open Scope list.

(* Definition ruleOfL {MsgT} (lbl: RLabel MsgT): option Rule := *)
(*   match lbl with *)
(*   | RlblInt rule _ _ => Some rule *)
(*   | _ => None *)
(*   end. *)

(* Fixpoint rulesOfH (hst: MHistory) := *)
(*   match hst with *)
(*   | nil => nil *)
(*   | lbl :: hst' => (ruleOfL lbl) ::> (rulesOfH hst') *)
(*   end. *)

(* Definition insOfL {MsgT} (lbl: RLabel MsgT): list (Id MsgT) := *)
(*   match lbl with *)
(*   | RlblInt _ ins _ => ins *)
(*   | RlblOuts outs => outs *)
(*   | _ => nil *)
(*   end. *)

(* Definition outsOfL {MsgT} (lbl: RLabel MsgT): list (Id MsgT) := *)
(*   match lbl with *)
(*   | RlblIns ins => ins *)
(*   | RlblInt _ _ outs => outs *)
(*   | _ => nil *)
(*   end. *)

(* Fixpoint insOfH (hst: MHistory) := *)
(*   match hst with *)
(*   | nil => nil *)
(*   | lbl :: hst' => insOfH hst' ++ insOfL lbl *)
(*   end. *)

(* Fixpoint outsOfH (hst: MHistory) := *)
(*   match hst with *)
(*   | nil => nil *)
(*   | lbl :: hst' => outsOfH hst' ++ outsOfL lbl *)
(*   end. *)

(** TODO: need to check whether the disjointness between [ins1] and [ins2] 
 * (or [outs1] and [outs2]) is required. *)
Definition NonConflictingR {ifc: OStateIfc} (rule1 rule2: Rule ifc) :=
  forall post1 porq1 ins1 nost1 norq1 outs1 ins2,
    rule_precond rule1 post1 porq1 ins1 ->
    rule_trs rule1 post1 porq1 ins1 = (nost1, norq1, outs1) ->
    rule_precond rule2 nost1 norq1 ins2 ->
    (* 1) Precondition of [rule2] holds if the one of [rule1] holds. *)
    rule_precond rule2 post1 porq1 ins2 /\
    forall nost2 norq2 outs2,
      rule_trs rule2 post1 porq1 ins2 = (nost2, norq2, outs2) ->
      (* 2) Precondition of [rule1] holds after a transition by [rule2]. *)
      rule_precond rule1 nost2 norq2 ins1 /\
      (* 3) Transitions by [rule1; rule2] and [rule2; rule1] are same. *)
      fst (rule_trs rule2 nost1 norq1 ins2) =
      fst (rule_trs rule1 nost2 norq2 ins1).

Definition NonConflicting (sys: System) (hst1 hst2: MHistory) :=
  forall obj rule1 rule2 ins1 outs1 ins2 outs2,
    In obj (sys_objs sys) ->
    In rule1 (obj_rules obj) ->
    In rule2 (obj_rules obj) ->
    In (RlblInt (obj_idx obj) (rule_idx rule1) ins1 outs1) hst1 ->
    In (RlblInt (obj_idx obj) (rule_idx rule2) ins2 outs2) hst2 ->
    NonConflictingR rule1 rule2.

Definition Discontinuous (sys: System) (hst1 hst2: MHistory) :=
  forall inits1 ins1 outs1 eouts1 inits2 ins2 outs2 eouts2,
    Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 /\
    Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 /\
    DisjList (idsOf ins1) (idsOf ins2) /\
    DisjList inits1 eouts2 /\
    DisjList (idsOf outs1) (idsOf outs2).

Lemma nonconflicting_discontinuous_commutable_atomic:
  forall sys hst1 hst2,
    NonConflicting sys hst1 hst2 ->
    Discontinuous sys hst1 hst2 ->
    Reducible sys (hst2 ++ hst1) (hst1 ++ hst2).
Proof.
Admitted.

Close Scope list.

