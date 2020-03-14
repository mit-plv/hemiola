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

Section Compile.
  Context `{DecValue} `{oifc: OStateIfc}.

  Definition compile_OState_init: list K.RegInitT :=
    nil. (** TODO *)

  Section PreEval.

    Definition KOIdx := Bit 8.
    Definition KMsgId := Bit 5.
    Definition KValue := Bit 32.

    Definition KMsg :=
      STRUCT { "id" :: KMsgId;
               "type" :: Bool;
               "value" :: KValue }.

    Definition UpLock :=
      STRUCT { "ul_valid" :: Bool;
               "ul_rsb" :: Bool;
               "ul_msg" :: Struct KMsg;
               "ul_rssFrom" :: Array KOIdx 8;
               "ul_rsbTo" :: KOIdx }.

    Definition DownLock :=
      STRUCT { "dl_valid" :: Bool;
               "dl_rsb" :: Bool;
               "dl_msg" :: Struct KMsg;
               "dl_rssFrom" :: Array KOIdx 8;
               "dl_rsbTo" :: KOIdx }.

    Fixpoint idxToNat (deg: nat) (idx: IdxT): nat :=
      match idx with
      | nil => 0
      | d :: ds => d + deg * (idxToNat deg ds)
      end.
    Notation "% i %: d" :=
      (Const _ (natToWord _ (idxToNat d i))) (at level 5): kami_expr_scope.

    Definition kind_of (ht: htype): Kind :=
      match ht with
      | HMsg => Struct KMsg
      end.

    Definition hvar_of (var: Kind -> Type): htype -> Type :=
      fun ht => var (kind_of ht).

    Context {var: K.Kind -> Type}.
    Variables (oidx: IdxT)
              (ul: var (Struct UpLock))
              (dl: var (Struct DownLock)).

    Fixpoint idx_to_string (idx: IdxT): string :=
      match idx with
      | nil => ""
      | i :: idx' => idx_to_string idx' ++ "_" ++ nat_to_string i
      end.
    (* Eval compute in (idx_to_string (0~>1~>2)). *)

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

    Variable msgIn: var (Struct KMsg).

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

    Definition compile_bool (hv: HValue bool): Expr var (SyntaxKind Bool) :=
      match hv in (HValue T) return (T = bool -> Expr var (SyntaxKind Bool)) with
      | @HConst _ ty c =>
        fun Heq => eq_rect _ (fun ty => ty -> Expr var (SyntaxKind Bool))
                           (fun b => (Const _ (ConstBool b))) _ (eq_sym Heq) c
      | HOstVal idx => cheat _ (** FIXME *)
      end eq_refl.

    Definition compile_nat (sz: nat) (hv: HValue nat): Expr var (SyntaxKind (Bit sz)) :=
      match hv in (HValue T) return (T = nat -> Expr var (SyntaxKind (Bit sz))) with
      | @HConst _ ty c =>
        fun Heq => eq_rect _ (fun ty => ty -> Expr var (SyntaxKind (Bit sz)))
                           (fun c => ($c)%kami_expr) _ (eq_sym Heq) c
      | HOstVal idx => cheat _ (** FIXME *)
      end eq_refl.
    
    Fixpoint compile_Rule_prop_prec (pp: HOPrecP): Expr var (SyntaxKind Bool) :=
      (match pp with
       | HAnd pp1 pp2 =>
         (compile_Rule_prop_prec pp1) && (compile_Rule_prop_prec pp2)
       | HOr pp1 pp2 =>
         (compile_Rule_prop_prec pp1) || (compile_Rule_prop_prec pp2)
       | HBoolT b => compile_bool b == $$true
       | HBoolF b => compile_bool b == $$false
       | HNatEq sz v1 v2 => compile_nat sz v1 == compile_nat sz v2
       | HNatNe sz v1 v2 => compile_nat sz v1 != compile_nat sz v2
       | HNatLt sz v1 v2 => compile_nat sz v1 < compile_nat sz v2
       | HNatLe sz v1 v2 => compile_nat sz v1 <= compile_nat sz v2
       | HNatGt sz v1 v2 => compile_nat sz v1 > compile_nat sz v2
       | HNatGe sz v1 v2 => compile_nat sz v1 >= compile_nat sz v2
       end)%kami_expr.

    Fixpoint compile_Rule_prec (rp: HOPrec)
             (cont: ActionT var Void): ActionT var Void :=
      match rp with
      | HOPrecAnd prec1 prec2 =>
        let crule2 := compile_Rule_prec prec2 cont in
        compile_Rule_prec prec1 crule2
      | HOPrecRqRs rrprec => compile_Rule_rqrs_prec rrprec cont
      | HOPrecProp pprec =>
        (Assert (compile_Rule_prop_prec pprec); cont)%kami_action
      end.

    Definition compile_BindValue {ht} (hv: HBindValue ht)
      : Expr var (SyntaxKind (kind_of ht)) :=
      (match hv with
       | HNatGetFirstMsg => #msgIn
       end)%kami_expr.

    Fixpoint compile_MonadT (hm: HMonadT (hvar_of var)): ActionT var Void :=
      (match hm with
       | @HBind _ ht hv cont =>
         Let_ (compile_BindValue hv) (fun x: var (kind_of ht) => compile_MonadT (cont x))
       | @HRet _ _ _ _ => cheat _
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

  End PreEval.

  Definition compile_Rule (rule: {sr: H.Rule & HRule sr}):
    Attribute (Action Void) :=
    (* let ctrs := compile_Rule_trs (hrule_trs (projT2 rule)) in *)
    (* let crule := compile_Rule_prec (hrule_precond (projT2 rule)) ctrs in *)
    (* {| attrName := ""; attrType := crule |}. *)
    cheat _. (** FIXME *)
  
  Definition compile_Rules (rules: list {sr: H.Rule & HRule sr}):
    list (Attribute (Action Void)) :=
    map compile_Rule rules.
  
  Definition compile_Object (obj: HObject): option K.Modules :=
    let cregs := compile_OState_init in
    let crules := compile_Rules (hobj_rules obj) in
    Some (K.Mod cregs crules nil).
  
  Fixpoint compile_Objects (objs: list HObject): option Kami.Syntax.Modules :=
    match objs with
    | nil => None
    | obj :: objs' =>
      (cmod <-- compile_Object obj;
      cmods <-- compile_Objects objs';
      Some (ConcatMod cmod cmods))
    end.
  
  Definition compile_System (sys: HSystem): option Kami.Syntax.Modules :=
    compile_Objects sys.(hsys_objs).

End Compile.

