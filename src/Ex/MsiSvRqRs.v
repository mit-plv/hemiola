Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Topology Semantics SemFacts StepM StepT.
Require Import RqRs.

Require Import MsiSv.

(* Inductive SvMsiRqRs := *)
(* | ChildGetImm | ChildGetRqS *)
  
(* | ImmUp | ImmDown | RqUp | RqDown | RsUp | RsDown. *)

(* Definition SVMRqRsSemiDisj (rr1 rr2: SVMRqRs) := *)
(*   match rr1 with *)
(*   | RqUp => *)
(*     match rr2 with *)
(*     | ImmUp => False *)
(*     | ImmDown => True *)
(*     | RqUp => False *)
(*     | RqDown => True *)
(*     | RsUp => True *)
(*     | RsDown => False *)
(*     end *)
(*   | _ => False *)
(*   end. *)

(* Definition SVMRqRsDec (rule: Rule) := *)

(* Lemma singleValue_RqRsSys: RqRsSys rrdec rrsd impl0 *)