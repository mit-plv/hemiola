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

Section Compile.
  Context `{dv: DecValue} `{oifc: OStateIfc} `{hconfig}
          `{hoifc: @HOStateIfc dv oifc}.

  Definition compile_OState_init: list K.RegInitT :=
    TODO _.

  Definition Pair (k1 k2: Kind) :=
    STRUCT { "pair_1" :: k1; "pair_2" :: k2 }.

  Definition KIdxO := Bit hcfg_oidx_sz.
  Definition KIdxM := Bit hcfg_midx_sz.
  Definition KMid := Bit hcfg_msg_id_sz.
  Definition KValue := Bit hcfg_value_sz.

  Definition KMsg :=
    STRUCT { "id" :: KMid;
             "type" :: Bool;
             "value" :: KValue }.

  Definition UpLock :=
    STRUCT { "ul_valid" :: Bool;
             "ul_rsb" :: Bool;
             "ul_msg" :: Struct KMsg;
             "ul_rssFrom" :: Array KIdxM 8;
             "ul_rsbTo" :: KIdxM }.

  Definition DownLock :=
    STRUCT { "dl_valid" :: Bool;
             "dl_rsb" :: Bool;
             "dl_msg" :: Struct KMsg;
             "dl_rssFrom" :: Array KIdxM 8;
             "dl_rsbTo" :: KIdxM }.

  Fixpoint kind_of_hbtype (hbt: hbtype): Kind :=
    match hbt with
    | HBool => Bool
    | HIdx w => Bit w
    | HNat w => Bit w
    | HValue => Bit hcfg_value_sz
    | HMsg => Struct KMsg
    | HPair ht1 ht2 => Struct (Pair (kind_of_hbtype ht1) (kind_of_hbtype ht2))
    end.

  Definition compile_const {hbt} (hc: hbconst hbt)
    : ConstT (kind_of_hbtype hbt) :=
    match hc with
    | HBConstBool b => ConstBool b
    | HBConstNat w n => ConstBit (natToWord w n)
    | HBConstIdx w deg i => ConstBit (natToWord w (idxToNat deg i)) 
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

    Section Phoas.
      Context {var: K.Kind -> Type}.
      Variable oidx: IdxT.

      Definition kamiDeqOf (midx: IdxT): Attribute K.SignatureT :=
        {| attrName := "fifo" ++ idx_to_string midx;
           attrType := {| K.arg := Void;
                          K.ret := Struct KMsg |} |}.

      Definition compile_Rule_msg_from (mf: HMsgFrom)
                 (cont: var (Struct KMsg) -> ActionT var Void): ActionT var Void :=
        (match mf with
         | HMsgFromParent =>
           (Call msgIn <- (kamiDeqOf (downTo oidx))(); cont msgIn)
         | HMsgFromChild cidx =>
           (Call msgIn <- (kamiDeqOf (rsUpFrom oidx))(); cont msgIn)
         end)%kami_action.

      Variables (msgIn: var (Struct KMsg))
                (ul: var (Struct UpLock))
                (dl: var (Struct DownLock)).

      Definition compile_Rule_uplock (uln: string)
                 (cont: var (Struct UpLock) -> ActionT var Void): ActionT var Void :=
        (Read ul: Struct UpLock <- uln; cont ul)%kami_action.

      Definition compile_Rule_downlock (dln: string)
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
        | HIdm i m =>
          (STRUCT { "pair_1" ::= compile_bexp i;
                    "pair_2" ::= compile_bexp m })%kami_expr
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

      Fixpoint compile_MonadT (hm: HMonadT (hvar_of var)): ActionT var Void :=
        (match hm with
         | HBind hv cont =>
           Let_ (compile_bval hv) (fun x: var (kind_of_hbtype _) => compile_MonadT (cont x))
         | HRet _ _ _ => TODO _
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
    Variables (oidx: IdxT) (uln dln: string).

    Definition compile_Rule (rule: {sr: H.Rule & HRule sr}):
      Attribute (Action Void) :=
      let hr := projT2 rule in
      {| attrName := "";
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
                                      (compile_Rule_trs msgIn ul dl (hrule_trs hr)))))
      |}.
    
    Definition compile_Rules (rules: list {sr: H.Rule & HRule sr}):
      list (Attribute (Action Void)) :=
      map compile_Rule rules.

  End WithObj.

  Definition upLockReg (oidx: IdxT): string :=
    "ul" ++ idx_to_string oidx.
  Definition downLockReg (oidx: IdxT): string :=
    "dl" ++ idx_to_string oidx.
  
  Definition compile_Object (obj: {sobj: H.Object & HObject sobj})
    : option K.Modules :=
    let cregs := compile_OState_init in
    let crules := compile_Rules (obj_idx (projT1 obj))
                                (upLockReg (obj_idx (projT1 obj)))
                                (downLockReg (obj_idx (projT1 obj)))
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

