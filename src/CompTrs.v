Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepDet Serial.
Require Import Synthesis TrsInv TrsSim.

Set Implicit Arguments.

(** Rules for compositional transactions. *)
Section CompTrsRules.
  
  Variable (tid: IdxT).

  Inductive CompTrsRules: MsgId -> System -> Prop :=
  | ARImm:
      forall oidx oinit prec rqFrom postc valOut immr,
        (* Just to make sure the message is valid; from the external world. *)
        rqFrom <> oidx ->
        immr = synImm tid oidx prec rqFrom postc valOut ->
        CompTrsRules (buildMsgId tid rqFrom oidx rqChn)
                     [{| obj_idx := oidx;
                         obj_state_init := oinit;
                         obj_rules := immr :: nil |}]
  | ARRqRs:
      forall oidx oinit locker rqFrom fwds rqPre rsPost rsOut rqf rsb (syss: list System),

        rqf = synRq tid oidx locker rqFrom fwds rqPre ->
        rsb = synRs tid oidx fwds rqFrom rsPost rsOut ->

        (* Each object index is unique. *)
        NoDup (oidx :: concat (map (map obj_idx) syss)) ->
        
        Forall (fun systo => CompTrsRules (buildMsgId tid oidx (snd systo) rqChn)
                                          (fst systo))
               (combine syss fwds) ->
        
        CompTrsRules (buildMsgId tid rqFrom oidx rqChn)
                     ({| obj_idx := oidx;
                         obj_state_init := oinit;
                         obj_rules := rqf :: rsb :: nil |}
                        :: concat syss).

End CompTrsRules.

(** Growing trees: each branch can grow only once. *)
Section GTree.
  Variable V: Type.

  Inductive GTree :=
  | GTreeLeaf: IdxT -> V (* value *) -> bool (* growing? *) -> GTree
  | GTreeNode: IdxT (* index *) -> list GTree (* children *) -> GTree.

  Fixpoint elementsOf (tr: GTree): list IdxT :=
    match tr with
    | GTreeLeaf idx _ _ => idx :: nil
    | GTreeNode idx chd => idx :: (concat (map elementsOf chd))
    end.

  Definition WfGTree (tr: GTree) := NoDup (elementsOf tr).

  Definition bud (iv: IdxT * V) := GTreeLeaf (fst iv) (snd iv) true.
  Definition buds (ivs: list (IdxT * V)) :=
    map bud ivs.

  Definition deadleaf (iv: IdxT * V) := GTreeLeaf (fst iv) (snd iv) false.
  Definition deadleaves (ivs: list (IdxT * V)) :=
    map deadleaf ivs.
  
End GTree.

Definition DualMsg {MsgT} `{HasMsg MsgT} (rq rs: MsgT) :=
  mid_tid (msg_id (getMsg rq)) = mid_tid (msg_id (getMsg rs)) /\
  mid_from (msg_id (getMsg rq)) = mid_to (msg_id (getMsg rs)) /\
  mid_to (msg_id (getMsg rq)) = mid_from (msg_id (getMsg rs)).

Inductive Combined {A}: list A -> list (list A) -> Prop :=
| CombinedNil: Combined nil nil
| CombinedCons:
    forall a cmb l ll1 ll2,
      Combined cmb (ll1 ++ l :: ll2) ->
      Combined (a :: cmb) (ll1 ++ (a :: l) :: ll2).

(** Hoare Logic for Compositional Transactions *)
Section HoareLogic.

  (* Collect all previous preconditions of requests *)
  Definition RqCond :=
    ObjectStates -> Prop.

  (* Collect all previous postconditions of responses *)
  Definition RsCond :=
    ObjectStates -> Msg (* response-back *) -> Prop.

  Definition ImpRqCond (p1 p2: RqCond) :=
    forall pre, p1 pre -> p2 pre.

  Definition ImpRsCond (p1 p2: RsCond) :=
    forall post back, p1 post back -> p2 post back.

  Definition joinRqCond (p1 p2: RqCond): RqCond :=
    fun pre => p1 pre /\ p2 pre.

  Definition joinRsCond (prevs: list RsCond) (oidx: IdxT) (postc: RPostcond): RsCond :=
    fun post back =>
      exists ifroms,
        Forall (fun pfr => (fst pfr) post (snd pfr))
               (combine prevs ifroms) /\
        post@[oidx] >>=[False]
        (fun opost => forall pre, postc pre ifroms opost (back :: nil)).

  Definition liftToRqCond (oidx: IdxT) (prec: RPrecond): RqCond :=
    fun pre =>
      pre@[oidx] >>=[False]
      (fun opre => forall ins, prec opre ins).

  Definition liftToRsCond (oidx: IdxT) (postc: RPostcond): RsCond :=
    fun post back =>
      post@[oidx] >>=[False]
      (fun opost => forall pre, postc pre nil opost (back :: nil)).

  Inductive Cond :=
  | CondTop: Cond
  | CondRq: RqCond -> Cond
  | CondRs: RsCond -> Cond.

  Definition CondSat (cond: Cond) (oss: ObjectStates) (oout: option Msg) :=
    match cond with
    | CondTop => True
    | CondRq rqc => rqc oss
    | CondRs rsc => oout >>=[False] (fun out => rsc oss out)
    end.

  Record CompTrs :=
    { ctrs_from: IdxT;
      ctrs_hst: History;
      ctrs_conds: GTree Cond }.

  Definition buildCompTrs from hst conds :=
    {| ctrs_from := from;
       ctrs_hst := hst;
       ctrs_conds := conds |}.

  Inductive HoareTripleCT: GTree Cond -> History -> GTree Cond -> Prop :=
  | HTNil:
      forall oidx cond,
        HoareTripleCT (bud (oidx, cond)) nil (bud (oidx, cond))

  | HTImm:
      forall oidx immr rqin rsout pcond,
        oidx = mid_to (msg_id (tmsg_msg rqin)) ->
        DualMsg rqin rsout ->
        HoareTripleCT (bud (oidx, pcond))
                      (IlblOuts (Some immr) (rqin :: nil) (rsout :: nil) :: nil)
                      (deadleaf (oidx, CondRs (liftToRsCond oidx (rule_postcond immr))))

  | HTRqF:
      forall oidx rqfr fwds rqin rqfwds prqc nrqc hst lcond,
        oidx = mid_to (msg_id (tmsg_msg rqin)) ->
        fwds = map (fun tmsg => mid_to (msg_id (tmsg_msg tmsg))) rqfwds ->
        nrqc = joinRqCond prqc (liftToRqCond oidx (rule_precond rqfr)) ->
        HoareTripleCT (GTreeNode oidx (buds (map (fun fwd => (fwd, CondRq nrqc)) fwds)))
                      hst lcond ->
        HoareTripleCT (bud (oidx, CondRq prqc))
                      (IlblOuts (Some rqfr) (rqin :: nil) rqfwds :: hst)
                      lcond

  | HTComp:
      forall oidx ctrss fwds rqhst hst prqc lcond,
        Forall (fun ctrs => HoareTripleCT
                              (bud (ctrs_from ctrs, CondRq prqc))
                              (ctrs_hst ctrs)
                              (ctrs_conds ctrs)) ctrss ->
        fwds = map ctrs_from ctrss ->
        HoareTripleCT
          (GTreeNode oidx (map ctrs_conds ctrss)) hst lcond ->
        Combined rqhst (map ctrs_hst ctrss) ->
        HoareTripleCT
          (GTreeNode oidx (buds (map (fun fwd => (fwd, CondRq prqc)) fwds)))
          (rqhst ++ hst) lcond

  | HTRsB:
      forall oidx rsbr rsfroms rsback (prscs: list (IdxT * RsCond)),
        map fst prscs = map (fun tmsg => mid_from (msg_id (tmsg_msg tmsg))) rsfroms ->
        HoareTripleCT
          (GTreeNode oidx (deadleaves (map (fun irc => (fst irc, CondRs (snd irc))) prscs)))
          (IlblOuts (Some rsbr) rsfroms (rsback :: nil) :: nil)
          (deadleaf (oidx, CondRs (joinRsCond (map snd prscs) oidx (rule_postcond rsbr)))).

End HoareLogic.

Section Correctness.

  Definition lastOut (hst: History) :=
    (hd_error hst) >>=[None]
    (fun lbl =>
       match lbl with
       | IlblOuts _ _ outs =>
         (hd_error outs) >>= (fun out => Some (tmsg_msg out))
       | _ => None
       end).

  Theorem HoareTripleCT_ok:
    forall sys tid ts rq v hst mouts prec postc st1 st2,
      CompTrsRules tid rq sys ->
      Atomic sys ts (buildMsg rq v) hst mouts ->
      steps_det sys st1 hst st2 ->
      HoareTripleCT (bud (mid_to rq, prec)) (rev hst) (deadleaf (mid_to rq, postc)) ->
      CondSat prec (tst_oss st1) None ->
      CondSat postc (tst_oss st2) (lastOut hst).
  Proof.
  Admitted.

End Correctness.

