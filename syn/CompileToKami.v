Require Import Numbers.DecimalString.

Require Import Hemiola.Common Hemiola.Index Hemiola.Syntax.
Require Import Hemiola.Ex.TopoTemplate.
Require Import HemiolaDeep.

Require Import Kami.Lib.Struct Kami.

Set Implicit Arguments.

Import MonadNotations.
Module H := Hemiola.Syntax.
Module K := Kami.Syntax.

Definition nat_to_string (n: nat): string :=
  NilEmpty.string_of_uint (Nat.to_uint n).

Fixpoint idxToNat (deg: nat) (idx: IdxT): nat :=
  match idx with
  | nil => 0
  | d :: ds => d + deg * (idxToNat deg ds)
  end.
Notation "% i %: d" :=
  (Const _ (natToWord _ (idxToNat d i))) (at level 5): kami_expr_scope.

Fixpoint idx_to_string (idx: IdxT): string :=
  match idx with
  | nil => ""
  | i :: idx' => idx_to_string idx' ++ "_" ++ nat_to_string i
  end.
(* Eval compute in (idx_to_string (0~>1~>2)). *)

Fixpoint array_of_list {A} (def: A) (l: list A) sz: Vector.t A sz :=
  match l with
  | nil => vector_repeat sz def
  | a :: l' =>
    match sz with
    | O => Vector.nil _
    | S sz' => Vector.cons _ a _ (@array_of_list A def l' sz')
    end
  end.

Section Compile.
  Context `{dv: DecValue} `{oifc: OStateIfc} `{hconfig}
          `{hoifc: @HOStateIfc dv oifc}.

  Definition KIdxO := Bit hcfg_oidx_sz.
  Definition KIdxQ := Bit hcfg_midx_sz.
  Definition KIdxM := Bit hcfg_msg_id_sz.
  Definition KValue := Bit hcfg_value_sz.

  Definition KMsg :=
    STRUCT { "id" :: KIdxM;
             "type" :: Bool;
             "value" :: KValue }.

  Definition UpLock :=
    STRUCT { "ul_valid" :: Bool;
             "ul_rsb" :: Bool;
             "ul_msg" :: Struct KMsg;
             "ul_rsFrom" :: KIdxQ;
             "ul_rsbTo" :: KIdxQ }.

  Definition DownLock :=
    STRUCT { "dl_valid" :: Bool;
             "dl_rsb" :: Bool;
             "dl_msg" :: Struct KMsg;
             "dl_rss_size" :: Bit hcfg_children_max_lg;
             "dl_rssFrom" :: Array KIdxQ (Nat.pow 2 hcfg_children_max_lg);
             "dl_rsbTo" :: KIdxQ }.

  Fixpoint kind_of_hbtype (hbt: hbtype): Kind :=
    match hbt with
    | HBool => Bool
    | HIdx w => Bit w
    | HNat w => Bit w
    | HValue => Bit hcfg_value_sz
    | HMsg => Struct KMsg
    end.

  Definition compile_const {hbt} (hc: hbconst hbt)
    : ConstT (kind_of_hbtype hbt) :=
    match hc with
    | HBConstBool b => ConstBool b
    | HBConstNat w n => ConstBit (natToWord w n)
    | HBConstIdx w i =>
      (** FIXME: "16" should be in [hconfig] *)
      ConstBit (natToWord w (idxToNat 16 i)) 
    end.

  Section ExtComp.
    Context `{het: ExtType} `{@ExtExp dv oifc het}.
  
    Class CompExtType :=
      { kind_of_hetype: hetype -> Kind }.
    Context `{CompExtType}.

    Definition kind_of (ht: htype): Kind :=
      match ht with
      | HBType hbt => kind_of_hbtype hbt
      | HEType het => kind_of_hetype het
      end.

    Definition hbvar_of (var: Kind -> Type): hbtype -> Type :=
      fun hbt => var (kind_of (HBType hbt)).

    Definition hvar_of (var: Kind -> Type): htype -> Type :=
      fun ht => var (kind_of ht).

    Section QueueIfc.

      Definition fifoBaseName: string := "fifo".

      Definition deqFrom (midx: IdxT): Attribute K.SignatureT :=
        {| attrName := fifoBaseName ++ idx_to_string midx ++ ".deq";
           attrType := {| K.arg := Void;
                          K.ret := Struct KMsg |} |}.

      Definition enqTo (midx: IdxT): Attribute K.SignatureT :=
        {| attrName := fifoBaseName ++ idx_to_string midx ++ ".enq";
           attrType := {| K.arg := Struct KMsg;
                          K.ret := Void |} |}.

      Definition pcBaseName: string := "parentChildren".
      
      Definition deqFromChild (oidx: IdxT): Attribute K.SignatureT :=
        {| attrName := pcBaseName ++ idx_to_string oidx ++ ".deq";
           attrType := {| K.arg := KIdxQ;
                          K.ret := Struct KMsg |} |}.

      Definition EnqToCs :=
        STRUCT { "cs_size" :: Bit hcfg_children_max_lg;
                 "cs_q_inds" :: Array KIdxQ (Nat.pow 2 hcfg_children_max_lg);
                 "cs_msg" :: Struct KMsg
               }.
      
      Definition enqToCs (oidx: IdxT): Attribute K.SignatureT :=
        {| attrName := pcBaseName ++ idx_to_string oidx ++ ".enq";
           attrType := {| K.arg := Struct EnqToCs;
                          K.ret := Void |} |}.

    End QueueIfc.

    Local Notation deqFromParent := deqFrom.
    Local Notation deqFromExt := deqFrom.
    Local Notation enqToParent := enqTo.
    Local Notation enqToExt := enqTo.

    Section Phoas.
      Context {var: K.Kind -> Type}.
      Variable oidx: IdxT.

      Class CompOStateIfc :=
        { comp_ostval:
            forall (var: K.Kind -> Type) (i: Fin.t ost_sz) {hbt},
              Vector.nth host_ty i = Some hbt ->
              var (kind_of_hbtype hbt)
        }.
      Context `{CompOStateIfc}.

      Fixpoint compile_bexp {hbt} (he: hbexp (hbvar_of var) hbt)
        : Expr var (SyntaxKind (kind_of_hbtype hbt)) :=
        match he with
        | HBConst _ c => Const _ (compile_const c)
        | HVar _ _ v => Var _ (SyntaxKind _) v
        | HMsgB mid mty mval =>
          (STRUCT { "id" ::= compile_bexp mid;
                    "type" ::= compile_bexp mty;
                    "value" ::= compile_bexp mval })%kami_expr
        | HOstVal _ i Heq => Var _ (SyntaxKind _) (comp_ostval var i Heq)
        end.

      Class CompExtExp :=
        { compile_eexp:
            forall (var: K.Kind -> Type) {het},
              heexp (hvar_of var) het ->
              Expr var (SyntaxKind (kind_of het))
        }.
      Context `{CompExtExp}.

      Definition compile_exp {ht} (he: hexp (hvar_of var) ht)
        : Expr var (SyntaxKind (kind_of ht)) :=
        match he with
        | HBExp hbe => compile_bexp hbe
        | HEExp _ hee => compile_eexp var hee
        end.

      Definition compile_Rule_msg_from (mf: HMsgFrom)
                 (cont: var (Struct KMsg) -> ActionT var Void): ActionT var Void :=
        (match mf with
         | HMsgFromParent =>
           (Call msgIn <- (deqFromParent (downTo oidx))(); cont msgIn)
         | HMsgFromChild cmidx =>
           (Call msgIn <-
            (deqFromChild oidx)(compile_exp (HBExp (HBConst _ (HBConstIdx _ cmidx))));
           cont msgIn)
         | HMsgFromExt emidx =>
           (Call msgIn <- (deqFromExt emidx)(); cont msgIn)
         end)%kami_action.

      Variables (msgIn: var (Struct KMsg))
                (uln: string) (ul: var (Struct UpLock))
                (dln: string) (dl: var (Struct DownLock)).

      Definition compile_Rule_uplock
                 (cont: var (Struct UpLock) -> ActionT var Void): ActionT var Void :=
        (Read ul: Struct UpLock <- uln; cont ul)%kami_action.

      Definition compile_Rule_downlock
                 (cont: var (Struct DownLock) -> ActionT var Void): ActionT var Void :=
        (Read dl: Struct DownLock <- dln; cont dl)%kami_action.

      Definition compile_Rule_rqrs_prec (rrp: HOPrecR)
                 (cont: ActionT var Void): ActionT var Void :=
        (match rrp with
         | HRqAccepting => (Assert (!(#msgIn!KMsg@."type")); cont)
         | HRsAccepting => (Assert (#msgIn!KMsg@."type"); cont)
         | HUpLockFree => (Assert (!(#ul!UpLock@."ul_valid")); cont)
         | HDownLockFree => (Assert (!(#dl!DownLock@."dl_valid")); cont)
         | HUpLockMsgId mty mid =>
           (Assert (#ul!UpLock@."ul_valid");
           Assert (#ul!UpLock@."ul_rsb");
           Assert (#ul!UpLock@."ul_msg"!KMsg@."type" == Const _ (ConstBool mty));
           Assert (#ul!UpLock@."ul_msg"!KMsg@."id" == %mid%:5);
           cont)
         | HUpLockMsg =>
           (Assert (#ul!UpLock@."ul_valid"); Assert (#ul!UpLock@."ul_rsb"); cont)
         | HUpLockIdxBack =>
           (Assert (#ul!UpLock@."ul_valid"); Assert (#ul!UpLock@."ul_rsb"); cont)
         | HUpLockBackNone =>
           (Assert (#ul!UpLock@."ul_valid"); Assert (!(#ul!UpLock@."ul_rsb")); cont)
         | HDownLockMsgId mty mid =>
           (Assert (#dl!DownLock@."dl_valid");
           Assert (#dl!DownLock@."dl_rsb");
           Assert (#dl!DownLock@."dl_msg"!KMsg@."type" == Const _ (ConstBool mty));
           Assert (#dl!DownLock@."dl_msg"!KMsg@."id" == %mid%:5);
           cont)
         | HDownLockMsg =>
           (Assert (#dl!DownLock@."dl_valid"); Assert (#dl!DownLock@."dl_rsb"); cont)
         | HDownLockIdxBack =>
           (Assert (#dl!DownLock@."dl_valid"); Assert (#dl!DownLock@."dl_rsb"); cont)
         | HMsgIdFrom msgId => (Assert (#msgIn!KMsg@."id" == %msgId%:5); cont)
         end)%kami_action.

      Fixpoint compile_Rule_prop_prec (pp: HOPrecP (hvar_of var))
        : Expr var (SyntaxKind Bool) :=
        (match pp with
         | HAnd pp1 pp2 =>
           (compile_Rule_prop_prec pp1) && (compile_Rule_prop_prec pp2)
         | HOr pp1 pp2 =>
           (compile_Rule_prop_prec pp1) || (compile_Rule_prop_prec pp2)
         | HBoolT b => compile_exp b == $$true
         | HBoolF b => compile_exp b == $$false
         | HEq v1 v2 => compile_exp v1 == compile_exp v2
         | HNe v1 v2 => compile_exp v1 != compile_exp v2
         | HNatLt v1 v2 => compile_exp v1 < compile_exp v2
         | HNatLe v1 v2 => compile_exp v1 <= compile_exp v2
         | HNatGt v1 v2 => compile_exp v1 > compile_exp v2
         | HNatGe v1 v2 => compile_exp v1 >= compile_exp v2
         end)%kami_expr.

      Fixpoint compile_Rule_prec (rp: HOPrecT (hvar_of var))
               (cont: ActionT var Void): ActionT var Void :=
        match rp with
        | HOPrecAnd prec1 prec2 =>
          let crule2 := compile_Rule_prec prec2 cont in
          compile_Rule_prec prec1 crule2
        | HOPrecRqRs _ rrprec => compile_Rule_rqrs_prec rrprec cont
        | HOPrecProp pprec =>
          (Assert (compile_Rule_prop_prec pprec); cont)%kami_action
        end.

      Definition compile_bval {hbt} (hv: hbval hbt)
        : Expr var (SyntaxKind (kind_of_hbtype hbt)) :=
        (match hv with
         | HGetFirstMsg => #msgIn
         | HGetUpLockMsg => (#ul!UpLock@."ul_msg")
         | HGetDownLockMsg => (#dl!DownLock@."dl_msg")
         | HGetUpLockIdxBack => (#ul!UpLock@."ul_rsbTo")
         | HGetDownLockIdxBack => (#dl!DownLock@."dl_rsbTo")
         end)%kami_expr.

      Variable ostin: string.

      Definition ostValName {sz} (i: Fin.t sz) :=
        (ostin ++ "_" ++ nat_to_string (proj1_sig (Fin.to_nat i)))%string.

      Fixpoint compile_OState_trs (host: HOState (hvar_of var))
               (cont: ActionT var Void): ActionT var Void :=
        (match host with
         | HOStateI _ => cont
         | @HOstUpdate _ _ _ _ _ _ _ i ht Heq he host' =>
           (Write (ostValName i) : (kind_of ht) <- (compile_exp he);
           compile_OState_trs host' cont)
         end)%kami_action.

      Fixpoint compile_ORq_trs (horq: HORq (hvar_of var))
               (cont: ActionT var Void): ActionT var Void :=
        (match horq with
         | HORqI _ => cont
         | HUpdUpLock rq rsf rsb =>
           (Write uln: Struct UpLock <- STRUCT { "ul_valid" ::= $$true;
                                                 "ul_rsb" ::= $$true;
                                                 "ul_msg" ::= compile_exp rq;
                                                 "ul_rsFrom" ::= compile_exp rsf;
                                                 "ul_rsbTo" ::= compile_exp rsb }; cont)
         | HUpdUpLockS rsf =>
           (Write uln: Struct UpLock <- STRUCT { "ul_valid" ::= $$true;
                                                 "ul_rsb" ::= $$false;
                                                 "ul_msg" ::= $$Default;
                                                 "ul_rsFrom" ::= compile_exp rsf;
                                                 "ul_rsbTo" ::= $$Default }; cont)
         | HRelUpLock _ =>
           (Write uln: Struct UpLock <- STRUCT { "ul_valid" ::= $$false;
                                                 "ul_rsb" ::= $$Default;
                                                 "ul_msg" ::= $$Default;
                                                 "ul_rsFrom" ::= $$Default;
                                                 "ul_rsbTo" ::= $$Default }; cont)
         | HUpdDownLock rq rssf rsb =>
           (Write dln: Struct DownLock <- STRUCT { "dl_valid" ::= $$true;
                                                   "dl_rsb" ::= $$true;
                                                   "dl_msg" ::= compile_exp rq;
                                                   "dl_rss_size" ::=
                                                     $$(natToWord _ (List.length rssf));
                                                   "dl_rssFrom" ::=
                                                     BuildArray
                                                       (array_of_list
                                                          $$Default (List.map compile_exp rssf) _);
                                                   "dl_rsbTo" ::= compile_exp rsb }; cont)
         | HUpdDownLockS rssf =>
           (Write dln: Struct DownLock <- STRUCT { "dl_valid" ::= $$true;
                                                   "dl_rsb" ::= $$false;
                                                   "dl_msg" ::= $$Default;
                                                   "dl_rss_size" ::=
                                                     $$(natToWord _ (List.length rssf));
                                                   "dl_rssFrom" ::=
                                                     BuildArray
                                                       (array_of_list
                                                          $$Default (List.map compile_exp rssf) _);
                                                   "dl_rsbTo" ::= $$Default }; cont)
         | HRelDownLock _ =>
           (Write dln: Struct DownLock <- STRUCT { "dl_valid" ::= $$false;
                                                   "dl_rsb" ::= $$Default;
                                                   "dl_msg" ::= $$Default;
                                                   "dl_rss_size" ::= $$Default;
                                                   "dl_rssFrom" ::= $$Default;
                                                   "dl_rsbTo" ::= $$Default }; cont)
         end)%kami_action.

      (** FIXME: compile [midx] to the *name* of the target fifo.. huh? *)
      Definition compile_MsgsOut_trs (hmsgs: HMsgsOut (hvar_of var))
                 (cont: ActionT var Void): ActionT var Void :=
        (match hmsgs with (** FIXME: TODOs *)
         | HMsgOutUp midx msg =>
           (Call (enqToParent (TODO _))(compile_exp msg); cont)
         | HMsgsOutDown minds msg =>
           (Call (enqToCs oidx)(STRUCT { "cs_size" ::= TODO _;
                                         "cs_q_inds" ::=
                                           BuildArray
                                             (array_of_list
                                                $$Default (List.map compile_exp minds) _);
                                         "cs_msg" ::= compile_exp msg });
           cont)
         | HMsgOutExt midx msg =>
           (Call (enqToExt (TODO _))(compile_exp msg); cont)
         end)%kami_action.

      Fixpoint compile_MonadT (hm: HMonadT (hvar_of var)): ActionT var Void :=
        (match hm with
         | HBind hv cont =>
           Let_ (compile_bval hv) (fun x: var (kind_of_hbtype _) => compile_MonadT (cont x))
         | HRet host horq hmsgs =>
           compile_OState_trs host (compile_ORq_trs horq (compile_MsgsOut_trs hmsgs Retv))
         end)%kami_action.

      Definition compile_Monad (hm: HMonad): ActionT var Void :=
        compile_MonadT (hm (hvar_of var)).
      
      Definition compile_state_trs (mtrs: HStateMTrs): ActionT var Void :=
        match mtrs with
        | HMTrs mn => compile_Monad mn
        end.
      
      Definition compile_Rule_trs (rtrs: HOTrs): ActionT var Void :=
        match rtrs with
        | HTrsMTrs mtrs => compile_state_trs mtrs
        end.

    End Phoas.

  End ExtComp.

  Context `{CompOStateIfc} `{CompExtExp}.

  Section WithObj.
    Variables (oidx: IdxT) (uln dln ostin: string).

    Definition ruleNameBase: string := "rule".
    Definition ruleNameI (ridx: IdxT) :=
      (ruleNameBase ++ "_" ++ idx_to_string oidx ++ "_" ++ idx_to_string ridx)%string.

    Definition compile_Rule (rule: {sr: H.Rule & HRule sr}):
      Attribute (Action Void) :=
      let hr := projT2 rule in
      {| attrName := ruleNameI (rule_idx (projT1 rule));
         attrType :=
           fun var =>
             compile_Rule_msg_from
               oidx (hrule_msg_from hr)
               (fun msgIn =>
                  compile_Rule_uplock
                    uln (fun ul =>
                           compile_Rule_downlock
                             dln (fun dl =>
                                    compile_Rule_prec
                                      msgIn ul dl (hrule_precond hr (hvar_of var))
                                      (compile_Rule_trs
                                         oidx msgIn uln ul dln dl ostin (hrule_trs hr)))))
      |}.
    
    Definition compile_Rules (rules: list {sr: H.Rule & HRule sr}):
      list (Attribute (Action Void)) :=
      map compile_Rule rules.

  End WithObj.

  Definition upLockReg (oidx: IdxT): string :=
    "ul" ++ idx_to_string oidx.
  Definition downLockReg (oidx: IdxT): string :=
    "dl" ++ idx_to_string oidx.
  Definition ostIReg (oidx: IdxT): string :=
    "ost" ++ idx_to_string oidx.

  Definition compile_OState_init: list K.RegInitT :=
    TODO _.
  
  Definition compile_Object (obj: {sobj: H.Object & HObject sobj})
    : option K.Modules :=
    let cregs := compile_OState_init in
    let crules := compile_Rules (obj_idx (projT1 obj))
                                (upLockReg (obj_idx (projT1 obj)))
                                (downLockReg (obj_idx (projT1 obj)))
                                (ostIReg (obj_idx (projT1 obj)))
                                (hobj_rules (projT2 obj)) in
    Some (K.Mod cregs crules nil).
  
  Fixpoint compile_Objects (objs: list {sobj: H.Object & HObject sobj})
    : option Kami.Syntax.Modules :=
    match objs with
    | nil => None
    | obj :: objs' =>
      (cmod <-- compile_Object obj;
      cmods <-- compile_Objects objs';
      Some (ConcatMod cmod cmods))
    end.
  
  Definition compile_System (sys: {ssys: H.System & HSystem ssys})
    : option Kami.Syntax.Modules :=
    compile_Objects (hsys_objs (projT2 sys)).

End Compile.




(** * Temporary Testing Section *)
Require Import Hemiola.Ex.TopoTemplate Hemiola.Ex.RuleTemplate.
Require Import Hemiola.Ex.Mesi.Mesi.

Section Tests.

  Definition oidx: IdxT := 1.
  Definition uln: string := "UpLock". 
  Definition dln: string := "DownLock".
  Definition ostin: string := "ost".

  Context `{@CompOStateIfc SpecInds.NatDecValue
                           Mesi.ImplOStateIfc
                           mesiHConfig
                           MesiHOStateIfc}.

  Context `{cet: @CompExtType DirExtType}
          `{@CompExtExp SpecInds.NatDecValue
                        Mesi.ImplOStateIfc
                        mesiHConfig
                        DirExtType
                        DirExtExp
                        cet}.

  Definition cl1GetSImm := compile_Rule oidx uln dln ostin (existT _ _ (hl1GetSImm oidx)).

  Goal True.
    pose cl1GetSImm as r.
    compute in r.
  Abort.

End Tests.
