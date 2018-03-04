Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepDet.
Require Import PredMsg StepPred.
Require Import Serial.

(** Conversion from [PSystem] to [System] *)

Definition pToRule (prule: PRule): Rule :=
  {| rule_mids := midsOfPRule prule;
     rule_precond := precOfPRule prule;
     (** * TODO: how to convert? *)
     rule_postcond := ⊤⊤⊤ |}.

Definition pToSystem (psys: PSystem): System :=
  {| sys_inds := psys_inds psys;
     sys_inits := psys_inits psys;
     sys_rules := map pToRule (psys_rules psys) |}.

Theorem steps_pred_ok:
  forall sys st1 thst st2 ts rqin mouts,
    steps_det sys st1 thst st2 ->
    Atomic sys ts rqin thst mouts ->
    forall psys pst1 phst pst2,
      pToSystem psys = sys ->
      steps_pred psys pst1 phst pst2.
Proof.
Admitted.

