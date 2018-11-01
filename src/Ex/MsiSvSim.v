Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Topology Semantics SemFacts StepM StepT.
Require Import Invariant Simulation SerialFacts.
Require Import Blocking.

Require Import MsiSv.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

(** * TODO: recover all below with new notations. *)

(* Section OPrecs. *)

(*   Definition ImplOStatusM: OPrec := *)
(*     fun ost _ _ => ost@[statusIdx] = Some (VNat stM). *)

(*   Definition ImplOStatusS: OPrec := *)
(*     fun ost _ _ => ost@[statusIdx] = Some (VNat stS). *)
  
(*   Definition ImplOStatusI: OPrec := *)
(*     fun ost _ _ => ost@[statusIdx] = Some (VNat stI). *)

(* End OPrecs. *)

(* Section Predicates. *)

(*   Definition ImplStateI: OStatesFP := *)
(*     OStateForallP *)
(*       (fun oidx ost => *)
(*          forall stt,  *)
(*            ost@[statusIdx] = Some (VNat stt) -> *)
(*            stt = stI). *)

(*   Definition ImplStateMI (v: Value): OStatesFP := *)
(*     fun inds ioss => *)
(*       exists midx, *)
(*         In midx inds /\ *)
(*         OStateExistsP *)
(*           (fun oidx ost => *)
(*              ost@[statusIdx] = Some (VNat stM) /\ *)
(*              ost@[valueIdx] = Some v) midx ioss /\ *)
(*         OStateForallP *)
(*           (fun oidx ost => *)
(*              oidx <> midx -> *)
(*              forall stt, *)
(*                ost@[statusIdx] = Some (VNat stt) -> *)
(*                stt = stI) inds ioss. *)

(*   Definition ImplStateSI (v: Value): OStatesFP := *)
(*     fun inds ioss => *)
(*       (exists midx, *)
(*           In midx inds /\ *)
(*           OStateExistsP *)
(*             (fun oidx ost => ost@[statusIdx] = Some (VNat stS)) midx ioss) /\ *)
(*       OStateForallP *)
(*         (fun oidx ost => *)
(*            forall stt, *)
(*              ost@[statusIdx] = Some (VNat stt) -> *)
(*              match stt with *)
(*              | 0 (* stI *) => True *)
(*              | 1 (* stS *) => ost@[valueIdx] = Some v *)
(*              | 2 (* stM *) => False *)
(*              | _ => False *)
(*              end) inds ioss. *)

(*   Definition ImplStateMSI (v: Value): OStatesFP := *)
(*     fun inds ioss => ImplStateMI v inds ioss \/ ImplStateSI v inds ioss. *)

(*   (* NOTE: Here indeed binary predicates are required; if the predicate only *)
(*    * takes a poststate, then we cannot specify that the coherence value should *)
(*    * not be changed. *)
(*    *) *)
(*   (** --(.)--> [MSI(v) -> MSI(v)] --(v)--> *) *)
(*   Definition PredGet (tinds: list IdxT): PredOS := *)
(*     fun _ poss outv noss => *)
(*       ImplStateMSI outv tinds poss /\ ImplStateMSI outv tinds noss. *)

(*   (** --(v)--> [. -> MSI(v)] --(.)--> *) *)
(*   Definition PredSet (tinds: list IdxT): PredOS := *)
(*     fun inv _ _ noss => ImplStateMI inv tinds noss. *)

(*   (** --(.)--> [MSI(v)|{tinds} -> SI(v)|{tinds}] --(v)--> *) *)
(*   Definition PredGetSI (tinds: list IdxT): PredOS := *)
(*     fun _ poss outv noss => *)
(*       ImplStateMSI outv tinds poss /\ *)
(*       ImplStateSI outv tinds noss. *)

(*   (** --(.)--> [. -> I|{tinds}] --(v)--> *) *)
(*   Definition PredSetI (tinds: list IdxT): PredOS := *)
(*     fun _ _ _ noss => *)
(*       ImplStateI tinds noss. *)

(*   Definition OPredGetS: OPred := *)
(*     fun inv post outv nost => *)
(*       nost@[statusIdx] = Some (VNat stS) /\ *)
(*       nost@[valueIdx] = Some outv. *)

(*   (* Definition getRqFwdF (topo: Tree unit) (rqpmid: PMsgId TMsg): list (PMsgId TMsg) := *) *)
(*   (*   let from := mid_from (pmid_mid rqpmid) in *) *)
(*   (*   let this := mid_to (pmid_mid rqpmid) in *) *)
(*   (*   map (fun tofwds => *) *)
(*   (*          {| pmid_mid := *) *)
(*   (*               {| mid_addr := *) *)
(*   (*                    {| ma_from := this; *) *)
(*   (*                       ma_to := fst tofwds; *) *)
(*   (*                       ma_chn := rqChn |}; *) *)
(*   (*                  mid_tid := mid_tid (pmid_mid rqpmid) |}; *) *)
(*   (*             pmid_pred := *) *)
(*   (*               {| pred_os := PredGetSI (snd tofwds); *) *)
(*   (*                  pred_mp := ⊤ |} *) *)
(*   (*          |}) *) *)
(*   (*       (getFwds topo from this). *) *)
  
(* End Predicates. *)

(* Section Sim. *)
(*   Variables erq1 erq2 ers1 ers2: nat. *)
(*   Hypothesis (Hmvalid: NoDup ([c1pRq; c1pRs; pc1; c2pRq; c2pRs; pc2] *)
(*                                 ++ [erq1; erq2; ers1; ers2])). *)

(*   Local Notation spec := (spec Hmvalid). *)
(*   Local Notation impl0 := (impl0 Hmvalid). *)

(*   (** Global invariants *) *)

(*   Definition SvmInvs := *)
(*     ValidTrss impl0 /\i BlockedInv /\i ValidTidState. *)

(*   (** Simulation between [TState]s *) *)

(*   Definition SvmSpecState (v: Value) (soss: OStates) := *)
(*     exists sost, *)
(*       soss@[specIdx] = Some sost /\ *)
(*       sost@[valueIdx] = Some v. *)

(*   Definition SvmR (tinds: list IdxT): OStates -> OStates -> Prop := *)
(*     fun ioss soss => *)
(*       exists cv, *)
(*         ImplStateMSI cv tinds ioss /\ SvmSpecState cv soss. *)

(*   Definition SvmSpecORqs (sorqs: ORqs TMsg) := *)
(*     exists sorq, *)
(*       sorqs@[specIdx] = Some sorq. *)

(*   Definition SvmSim {SysT} `{IsSystem SysT} (impl: SysT): TState -> TState -> Prop := *)
(*     fun ist sst => *)
(*       SvmR (oindsOf impl) (tst_oss ist) (tst_oss sst) /\ *)
(*       SvmSpecORqs (tst_orqs sst) /\ *)
(*       SimMP ist sst. *)

(*   Section Facts. *)

(*     Lemma SvmSim_init: *)
(*       SvmSim impl0 (initsOf impl0) (initsOf spec). *)
(*     Proof. *)
(*       repeat esplit. *)
(*       right; repeat econstructor; *)
(*         cbn; intros; inv H; cbn; reflexivity. *)
(*     Qed. *)

(*     Lemma SvmSim_MsgsSim: *)
(*       MsgsSim (SvmSim impl0). *)
(*     Proof. *)
(*     Admitted. *)

(*     Lemma SvmInvs_init: *)
(*       SvmInvs (initsOf impl0). *)
(*     Proof. *)
(*       repeat constructor. *)
(*       - hnf; intros. *)
(*         elim H. *)
(*       - apply ForallMP_emptyMP. *)
(*     Qed. *)
    
(*   End Facts. *)
  
(* End Sim. *)

