Require Import Numbers.DecimalString.

Require Import Hemiola.Common Hemiola.Index Hemiola.Syntax.
Require Import Hemiola.Ex.TopoTemplate.

Require Import Compiler.HemiolaDeep. (* source *)
Require Import Kami.Lib.Struct Kami. (* target *)

Set Implicit Arguments.

Section VectorComp.

  Lemma Vector_nth_map_comp {A B} (f: A -> B) {n} (v: Vector.t A n) (p: Fin.t n):
    Vector.nth (Vector.map f v) p = f (Vector.nth v p).
  Proof.
    induction p.
    - revert n v; refine (@Vector.caseS _ _ _); now simpl.
    - revert n v p IHp; refine (@Vector.caseS _  _ _); now simpl.
  Defined.

End VectorComp.

Import MonadNotations.
Module H := Hemiola.Syntax.
Module K := Kami.Syntax.

Notation "∘ sz" := (fst sz + snd sz) (at level 0).

Definition nat_to_string (n: nat): string :=
  NilEmpty.string_of_uint (Nat.to_uint n).

Fixpoint idx_to_nat (deg: nat) (idx: IdxT): nat :=
  match idx with
  | nil => 0
  | d :: ds => d + deg * (idx_to_nat deg ds)
  end.

Definition idx_to_word (sz: nat * nat) (idx: IdxT): word ∘sz :=
  natToWord _ (idx_to_nat (fst sz) idx).

Notation "% i %: sz" := (idx_to_word sz i) (at level 5): kami_expr_scope.

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
          `{het: ExtType}
          `{hoifc: @HOStateIfc dv oifc}
          `{hoifcf: @HOStateIfcFull dv oifc hoifc het}.

  Definition KIdxO := Bit ∘hcfg_oidx_sz.
  Definition KIdxQ := Bit ∘hcfg_midx_sz.
  Definition KIdxM := Bit ∘hcfg_msg_id_sz.
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
    | HIdx w => Bit ∘w
    | HNat w => Bit w
    | HValue => Bit hcfg_value_sz
    | HMsg => Struct KMsg
    end.

  Definition compile_const {hbt} (hc: hbconst hbt)
    : ConstT (kind_of_hbtype hbt) :=
    match hc with
    | HBConstBool b => ConstBool b
    | HBConstNat w n => ConstBit (natToWord w n)
    | HBConstIdx w i => ConstBit (idx_to_word w i)
    end.

  Section ExtComp.
    Context `{@ExtExp dv oifc het}.
  
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

      Variable ostin: string.

      Definition ostValNameN (n: nat) :=
        (ostin ++ "_" ++ nat_to_string n)%string.

      Definition ostValNameI {sz} (i: Fin.t sz) :=
        ostValNameN (proj1_sig (Fin.to_nat i)).

      Fixpoint compile_Rule_ost_vars_fix (n: nat) {sz} (htys: Vector.t htype sz)
               (cont: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) htys) ->
                      ActionT var Void) {struct htys}: ActionT var Void :=
        match htys in Vector.t _ sz
              return (HVector.hvec (Vector.map (fun hty => var (kind_of hty)) htys) ->
                      ActionT var Void) -> ActionT var Void with
        | Vector.nil _ => fun cont => cont tt
        | Vector.cons _ hty _ htys =>
          fun cont =>
            (Read ov: (kind_of hty) <- (ostValNameN n);
            compile_Rule_ost_vars_fix
              (S n) htys (fun vars => cont (HVector.hvcons ov vars)))%kami_action
        end cont.

      Definition compile_Rule_ost_vars :=
        compile_Rule_ost_vars_fix O hostf_ty.
      
      Variable (ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty)).

      Fixpoint compile_bexp {hbt} (he: hbexp (hbvar_of var) hbt)
        : Expr var (SyntaxKind (kind_of_hbtype hbt)) :=
        match he with
        | HBConst _ c => Const _ (compile_const c)
        | HVar _ _ v => Var _ (SyntaxKind _) v
        | HMsgB mid mty mval =>
          (STRUCT { "id" ::= compile_bexp mid;
                    "type" ::= compile_bexp mty;
                    "value" ::= compile_bexp mval })%kami_expr
        | @HOstVal _ _ _ _ _ i hbt0 Heq =>
          Var _ (SyntaxKind _)
              (eq_rect
                 hostf_ty[@i]
                 (fun h => var (kind_of h))
                 (eq_rect (Vector.map (fun h => var (kind_of h)) hostf_ty)[@i]
                          (fun T => T)
                          (HVector.hvec_ith ostVars i)
                          (var (kind_of hostf_ty[@i]))
                          (Vector_nth_map_comp (fun h => var (kind_of h)) hostf_ty i))
                 (HBType hbt0)
                 (hostf_ty_compat i Heq))
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
           Assert (#ul!UpLock@."ul_msg"!KMsg@."id" == $$%mid%:hcfg_msg_id_sz);
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
           Assert (#dl!DownLock@."dl_msg"!KMsg@."id" == $$%mid%:hcfg_msg_id_sz);
           cont)
         | HDownLockMsg =>
           (Assert (#dl!DownLock@."dl_valid"); Assert (#dl!DownLock@."dl_rsb"); cont)
         | HDownLockIdxBack =>
           (Assert (#dl!DownLock@."dl_valid"); Assert (#dl!DownLock@."dl_rsb"); cont)
         | HMsgIdFrom msgId => (Assert (#msgIn!KMsg@."id" == $$%msgId%:hcfg_msg_id_sz); cont)
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

      Fixpoint compile_OState_trs (host: HOState (hvar_of var))
               (cont: ActionT var Void): ActionT var Void :=
        (match host with
         | HOStateI _ => cont
         | @HOstUpdate _ _ _ _ _ _ _ i ht Heq he host' =>
           (Write (ostValNameI i) : (kind_of ht) <- (compile_exp he);
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

      Definition compile_MsgsOut_trs (hmsgs: HMsgsOut (hvar_of var))
                 (cont: ActionT var Void): ActionT var Void :=
        (match hmsgs with
         | HMsgOutUp midx msg =>
           (Call (enqToParent midx)(compile_exp msg); cont)
         | HMsgsOutDown minds msg =>
           (Call (enqToCs oidx)(STRUCT { "cs_size" ::=
                                           $$(natToWord _ (List.length minds));
                                         "cs_q_inds" ::=
                                           BuildArray
                                             (array_of_list
                                                $$Default (List.map compile_exp minds) _);
                                         "cs_msg" ::= compile_exp msg });
           cont)
         | HMsgOutExt midx msg =>
           (Call (enqToExt midx)(compile_exp msg); cont)
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

  Context `{CompExtExp}.

  Section WithObj.
    Variables (oidx: IdxT) (uln dln ostin: string).

    Definition ruleNameBase: string := "rule".
    Definition ruleNameI (ridx: IdxT) :=
      (ruleNameBase ++ "_" ++ idx_to_string oidx ++ "_" ++ idx_to_string ridx)%string.

    Local Notation "v <- f ; cont" := (f (fun v => cont)) (at level 99, right associativity).
    Local Notation "f ;; cont" := (f cont) (at level 60, right associativity).
    Definition compile_Rule (rule: {sr: H.Rule & HRule sr}):
      Attribute (Action Void) :=
      let hr := projT2 rule in
      {| attrName := ruleNameI (rule_idx (projT1 rule));
         attrType :=
           fun var =>
             (ostVars <- compile_Rule_ost_vars ostin;
             msgIn <- compile_Rule_msg_from oidx ostVars (hrule_msg_from hr);
             ul <- compile_Rule_uplock uln;
             dl <- compile_Rule_downlock dln;
             compile_Rule_prec
               ostVars msgIn ul dl (hrule_precond hr (hvar_of var));;
             compile_Rule_trs
               oidx ostin ostVars msgIn uln ul dln dl (hrule_trs hr))
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
