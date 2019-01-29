Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

(* Inductive TrsType := RqUp | RqDown | RsUp | RsDown. *)
(* Object index -> TrsTypes (ordered, head is the oldest one) *)
(* Definition TrsState := M.t (list TrsType). *)

(* Definition addTrsState (oidx: IdxT) (tr: TrsType) (ts: TrsState): TrsState := *)
(*   match ts@[oidx] with *)
(*   | Some tts => ts +[oidx <- tr :: tts] *)
(*   | None => ts +[oidx <- [tr]] *)
(*   end. *)

(* Definition rssOfL (lbl: MLabel) := *)
(*   match lbl with *)
(*   | RlblInt oidx _ _ mouts => *)
(*     match mouts with *)
(*     | nil => Some oidx (* Requests are never ignored. *) *)
(*     | (midx, mout) :: _ => *)
(*       if eq_nat_dec (msg_type mout) MRs *)
(*       then Some oidx else None *)
(*     end *)
(*   | _ => None *)
(*   end. *)

(* Fixpoint rssOf (hst: MHistory): list IdxT := *)
(*   match hst with *)
(*   | nil => nil *)
(*   | lbl :: hst' => (rssOfL lbl) ::> (rssOf hst') *)
(*   end. *)

(* Section AtomicInv. *)
(*   Context {oifc: OStateIfc}. *)
(*   Variables (dtr: DTree) *)
(*             (sys: System oifc). *)

(*   Hypothesis (Hitr: GoodRqRsSys dtr sys). *)

(*   Definition rsUpCover (idm: Id Msg): list IdxT := *)
(*     nil. (** TODO: define it. *) *)

(*   Fixpoint rsUpCovers (eouts: list (Id Msg)): list IdxT := *)
(*     match eouts with *)
(*     | nil => nil *)
(*     | idm :: eouts' => rsUpCover idm ++ rsUpCovers eouts' *)
(*     end. *)

(*   Definition rsDownCover (idm: Id Msg): list IdxT := *)
(*     nil. (** TODO: define it. *) *)

(*   Fixpoint rsDownCovers (eouts: list (Id Msg)): list IdxT := *)
(*     match eouts with *)
(*     | nil => nil *)
(*     | idm :: eouts' => rsDownCover idm ++ rsDownCovers eouts' *)
(*     end. *)

(*   Definition AtomicInv (inits eouts: list (Id Msg)) (hst: MHistory) := *)
(*     NoDup (rssOf hst) /\ *)
(*     SubList (rssOf hst) (rsUpCovers eouts) /\ *)
(*     DisjList (rssOf hst) (rsDownCovers eouts). *)

(*   Lemma atomic_inv: *)
(*     forall inits ins hst outs eouts, *)
(*       Atomic msg_dec inits ins hst outs eouts -> *)
(*       forall s1 s2, *)
(*         steps step_m sys s1 hst s2 -> *)
(*         AtomicInv inits eouts hst. *)
(*   Proof. *)
  
(* End AtomicInv. *)

Close Scope list.
Close Scope fmap.

