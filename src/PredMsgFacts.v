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

Definition pToTMsg (ts: TrsId) (rqin: Msg) (pmsg: PMsgSig): TMsg :=
  {| tmsg_msg := {| msg_id := pmsg_mid (projT2 pmsg);
                    msg_value := pmsg_val (projT2 pmsg)
                 |};
     tmsg_info := Some {| tinfo_tid := ts; tinfo_rqin := rqin :: nil |}
  |}.

Definition pToTState (ts: TrsId) (rqin: Msg) (pst: PState): TState :=
  {| tst_oss := pst_oss pst;
     tst_msgs := map (pToTMsg ts rqin) (pst_msgs pst);
     tst_tid := ts |}.

Definition pToTLabel (ts: TrsId) (rqin: Msg) (plbl: PLabel): TLabel :=
  match plbl with
  | PlblIn min => RlblIn (pToTMsg ts rqin (existT _ _ min))
  | PlblOuts oprule mins mouts =>
    RlblOuts (lift pToRule oprule)
             (map (pToTMsg ts rqin) mins)
             (map (pToTMsg ts rqin) mouts)
  end.

Definition pToTHistory (ts: TrsId) (rqin: Msg) (phst: PHistory): THistory :=
  map (pToTLabel ts rqin) phst.

Theorem steps_pred_ok:
  forall sys st1 thst st2 ts rqin mouts,
    steps_det sys st1 thst st2 ->
    Atomic sys ts rqin thst mouts ->
    forall psys,
      pToSystem psys = sys ->
      exists pst1 phst pst2,
        pToTState ts rqin pst1 = st1 /\
        pToTState ts rqin pst2 = st2 /\
        behaviorOf psys phst = behaviorOf sys thst /\
        steps_pred psys pst1 phst pst2.
Proof.
Admitted.

