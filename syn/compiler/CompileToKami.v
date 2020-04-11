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
  Context `{hcfg: hconfig} `{dv: DecValue} `{hdv: @HDecValue dv hcfg}
          `{oifc: OStateIfc} 
          `{het: ExtType}
          `{hoifc: @HOStateIfc dv oifc}
          `{hoifcf: @HOStateIfcFull dv oifc hoifc het}.

  Definition KIdxO := Bit ∘hcfg_oidx_sz.
  Definition KIdxQ := Bit ∘hcfg_midx_sz.
  Definition KIdxM := Bit ∘hcfg_msg_id_sz.
  Definition KValue := Bit hcfg_value_sz.
  Definition hcfg_children_max_lg := Nat.log2 (S hcfg_children_max).

  Definition KObjIdxOf {var} (midx: Expr var (SyntaxKind KIdxQ))
    : Expr var (SyntaxKind KIdxO) :=
    TODO _.

  Definition KRqUpFrom {var} (midx: Expr var (SyntaxKind KIdxO))
    : Expr var (SyntaxKind KIdxQ) :=
    TODO _.

  Definition KRsUpFrom {var} (midx: Expr var (SyntaxKind KIdxO))
    : Expr var (SyntaxKind KIdxQ) :=
    TODO _.

  Definition KDownTo {var} (midx: Expr var (SyntaxKind KIdxO))
    : Expr var (SyntaxKind KIdxQ) :=
    TODO _.

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
             "dl_rss_from" :: Array KIdxQ (S hcfg_children_max);
             "dl_rss_recv" :: Array Bool (S hcfg_children_max);
             "dl_rss" :: Array (Struct KMsg) (S hcfg_children_max);
             "dl_rsbTo" :: KIdxQ }.

  Definition KIdm :=
    STRUCT { "midx" :: KIdxQ; "msg" :: Struct KMsg }.
  
  Fixpoint kind_of_hbtype (hbt: hbtype): Kind :=
    match hbt with
    | HBool => Bool
    | HIdx w => Bit ∘w
    | HNat w => Bit w
    | HMsg => Struct KMsg
    | HIdm => Struct KIdm
    | HList hbt' =>
      (* This is very arbitrary, but [HList] is only used for
       * sharer indices in a directory.. *)
      Array (kind_of_hbtype hbt') (S hcfg_children_max)
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

      Definition deqFrom (midx: IdxT): Attribute SignatureT :=
        {| attrName := fifoBaseName ++ idx_to_string midx ++ ".deq";
           attrType := {| arg := Void;
                          ret := Struct KMsg |} |}.

      Definition enqTo (midx: IdxT): Attribute SignatureT :=
        {| attrName := fifoBaseName ++ idx_to_string midx ++ ".enq";
           attrType := {| arg := Struct KMsg;
                          ret := Void |} |}.

      Definition pcBaseName: string := "parentChildren".
      
      Definition deqFromChild (oidx: IdxT): Attribute SignatureT :=
        {| attrName := pcBaseName ++ idx_to_string oidx ++ ".deq";
           attrType := {| arg := KIdxQ;
                          ret := Struct KMsg |} |}.

      Definition EnqToCs :=
        STRUCT { "cs_size" :: Bit hcfg_children_max_lg;
                 "cs_q_inds" :: Array KIdxQ (S hcfg_children_max);
                 "cs_msg" :: Struct KMsg
               }.
      
      Definition enqToCs (oidx: IdxT): Attribute SignatureT :=
        {| attrName := pcBaseName ++ idx_to_string oidx ++ ".enq";
           attrType := {| arg := Struct EnqToCs;
                          ret := Void |} |}.

    End QueueIfc.

    Local Notation deqFromParent := deqFrom.
    Local Notation deqFromExt := deqFrom.
    Local Notation enqToParent := enqTo.
    Local Notation enqToExt := enqTo.

    Section Phoas.
      Context {var: Kind -> Type}.
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
        | HIdmId pe => ((compile_bexp pe)!KIdm@."midx")%kami_expr
        | HIdmMsg pe => ((compile_bexp pe)!KIdm@."msg")%kami_expr
        | HObjIdxOf midx => KObjIdxOf (compile_bexp midx)
        | HMsgB mid mty mval =>
          (STRUCT { "id" ::= compile_bexp mid;
                    "type" ::= compile_bexp mty;
                    "value" ::= compile_bexp mval })%kami_expr
        | HMsgId msg => ((compile_bexp msg)!KMsg@."id")%kami_expr
        | HMsgType msg => ((compile_bexp msg)!KMsg@."type")%kami_expr
        | HMsgValue msg => ((compile_bexp msg)!KMsg@."value")%kami_expr
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
            forall (var: Kind -> Type) {het},
              HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty) ->
              heexp (hvar_of var) het ->
              Expr var (SyntaxKind (kind_of het))
        }.
      Context `{CompExtExp}.

      Definition compile_exp {ht} (he: hexp (hvar_of var) ht)
        : Expr var (SyntaxKind (kind_of ht)) :=
        match he with
        | HBExp hbe => compile_bexp hbe
        | HEExp _ hee => compile_eexp var ostVars hee
        end.

      Variables (msgIn: var (Struct KMsg))
                (uln: string) (ul: var (Struct UpLock))
                (dln: string) (dl: var (Struct DownLock)).

      Definition compile_Rule_uplock
                 (cont: var (Struct UpLock) -> ActionT var Void): ActionT var Void :=
        (Read ul: Struct UpLock <- uln; cont ul)%kami_action.

      Definition compile_Rule_downlock
                 (cont: var (Struct DownLock) -> ActionT var Void): ActionT var Void :=
        (Read dl: Struct DownLock <- dln; cont dl)%kami_action.

      Definition compile_Rule_msg_from (mf: HMsgFrom)
                 (cont: var (Struct KMsg) -> ActionT var Void): ActionT var Void :=
        (match mf with
         | HMsgFromNil =>
           (* This is a hack, just by feeding a random value to the continuation *)
           (LET msgIn <- $$Default; cont msgIn)
         | HMsgFromParent pmidx =>
           (Call msgIn <- (deqFromParent pmidx)(); cont msgIn)
         | HMsgFromChild cmidx =>
           (Call msgIn <-
            (deqFromChild oidx)(compile_exp (HBExp (HBConst _ (HBConstIdx _ cmidx))));
           cont msgIn)
         | HMsgFromExt emidx =>
           (Call msgIn <- (deqFromExt emidx)(); cont msgIn)
         | HMsgFromUpLock =>
           (Call msgIn <- (deqFromParent (downTo oidx))(); cont msgIn)
         | HMsgFromDownLock cidx =>
           (Call msgIn <-
            (deqFromChild oidx)(compile_exp (HBExp (HBConst _ (HBConstIdx _ (rqUpFrom cidx)))));
           cont msgIn)
         end)%kami_action.

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
         | HRssFull => (Assert (#dl!DownLock@."dl_rss_recv" ==
                                              $$(ConstArray (vector_repeat _ (ConstBool true)))); cont)
         end)%kami_action.

      Fixpoint compile_Rule_prop_prec (pp: HOPrecP (hvar_of var))
        : Expr var (SyntaxKind Bool) :=
        (match pp with
         | HTrue _ => $$true
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
        | HOPrecNative _ _ => cont
        end.

      Definition compile_bval {hbt} (hv: hbval hbt)
        : Expr var (SyntaxKind (kind_of_hbtype hbt)) :=
        (match hv in hbval hbt' return Expr var (SyntaxKind (kind_of_hbtype hbt')) with
         | HGetFirstMsg => #msgIn
         | HGetUpLockMsg => (#ul!UpLock@."ul_msg")
         | HGetDownLockMsg => (#dl!DownLock@."dl_msg")
         | HGetUpLockIdxBack => (#ul!UpLock@."ul_rsbTo")
         | HGetDownLockIdxBack => (#dl!DownLock@."dl_rsbTo")
         | HGetDownLockFirstRs =>
           (STRUCT { "midx" ::= (#dl!DownLock@."dl_rss_from")#[$$(natToWord hcfg_children_max 0)];
                     "msg" ::= (#dl!DownLock@."dl_rss")#[$$(natToWord hcfg_children_max 0)]
           })
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
         | HUpdUpLock porq rq rsf rsb =>
           (Write uln: Struct UpLock <- STRUCT { "ul_valid" ::= $$true;
                                                 "ul_rsb" ::= $$true;
                                                 "ul_msg" ::= compile_exp rq;
                                                 "ul_rsFrom" ::= compile_exp rsf;
                                                 "ul_rsbTo" ::= compile_exp rsb };
           compile_ORq_trs porq cont)
         | HUpdUpLockS porq rsf =>
           (Write uln: Struct UpLock <- STRUCT { "ul_valid" ::= $$true;
                                                 "ul_rsb" ::= $$false;
                                                 "ul_msg" ::= $$Default;
                                                 "ul_rsFrom" ::= compile_exp rsf;
                                                 "ul_rsbTo" ::= $$Default };
           compile_ORq_trs porq cont)
         | HRelUpLock _ =>
           (Write uln: Struct UpLock <- $$Default; cont)
         | HUpdDownLock porq rq rssf rsb =>
           (Write dln: Struct DownLock <- STRUCT { "dl_valid" ::= $$true;
                                                   "dl_rsb" ::= $$true;
                                                   "dl_msg" ::= compile_exp rq;
                                                   "dl_rss_size" ::= $$(natToWord _ (TODO _));
                                                   "dl_rss_from" ::= compile_exp rssf;
                                                   "dl_rss_recv" ::= $$Default;
                                                   "dl_rss" ::= $$Default;
                                                   "dl_rsbTo" ::= compile_exp rsb };
           compile_ORq_trs porq cont)
         | HUpdDownLockS porq rssf =>
           (Write dln: Struct DownLock <- STRUCT { "dl_valid" ::= $$true;
                                                   "dl_rsb" ::= $$false;
                                                   "dl_msg" ::= $$Default;
                                                   "dl_rss_size" ::= $$(natToWord _ (TODO _));
                                                   "dl_rss_from" ::= compile_exp rssf;
                                                   "dl_rss_recv" ::= $$Default;
                                                   "dl_rss" ::= $$Default;
                                                   "dl_rsbTo" ::= $$Default };
           compile_ORq_trs porq cont)
         | HRelDownLock porq =>
           (Write dln: Struct DownLock <- $$Default;
           compile_ORq_trs porq cont)
         | HAddRs porq midx msg => TODO _
         end)%kami_action.

      Definition compile_MsgsOut_trs (hmsgs: HMsgsOut (hvar_of var))
                 (cont: ActionT var Void): ActionT var Void :=
        (match hmsgs with
         | HMsgOutNil _ => cont
         | HMsgOutUp midx msg =>
           (Call (enqToParent midx)(compile_exp msg); cont)
         | HMsgOutDown midx msg =>
           (Call (enqToCs oidx)(STRUCT { "cs_size" ::= $1;
                                         "cs_q_inds" ::=
                                           UpdateArray
                                             $$Default
                                             $$(natToWord (S hcfg_children_max) 0)
                                             (compile_exp midx);
                                         "cs_msg" ::= compile_exp msg });
           cont)
         | HMsgsOutDown minds msg =>
           (Call (enqToCs oidx)(STRUCT { "cs_size" ::= $$(natToWord _ (TODO _));
                                         "cs_q_inds" ::= compile_exp minds;
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
    Definition compile_Rule (rule: {sr: Hemiola.Syntax.Rule & HRule sr}):
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
    
    Definition compile_Rules (rules: list {sr: Hemiola.Syntax.Rule & HRule sr}):
      list (Attribute (Action Void)) :=
      map compile_Rule rules.

  End WithObj.

  Definition upLockReg (oidx: IdxT): string :=
    "ul" ++ idx_to_string oidx.
  Definition downLockReg (oidx: IdxT): string :=
    "dl" ++ idx_to_string oidx.
  Definition ostIReg (oidx: IdxT): string :=
    "ost" ++ idx_to_string oidx.

  Fixpoint compile_inits (oidx: IdxT) (n: nat) (hts: list htype): list RegInitT :=
    match hts with
    | nil => nil
    | ht :: hts' =>
      {| attrName := ostValNameN (ostIReg oidx) n;
         attrType := RegInitDefault (SyntaxKind (kind_of ht)) |}
        :: compile_inits oidx (S n) hts'
    end.
  
  Definition compile_OState_init (oidx: IdxT): list RegInitT :=
    compile_inits oidx 0 (Vector.to_list hostf_ty).
  
  Definition compile_Object (obj: {sobj: Hemiola.Syntax.Object & HObject sobj})
    : option Modules :=
    let cregs := compile_OState_init (obj_idx (projT1 obj)) in
    let crules := compile_Rules (obj_idx (projT1 obj))
                                (upLockReg (obj_idx (projT1 obj)))
                                (downLockReg (obj_idx (projT1 obj)))
                                (ostIReg (obj_idx (projT1 obj)))
                                (hobj_rules (projT2 obj)) in
    Some (Mod cregs crules nil).
  
  Fixpoint compile_Objects (objs: list {sobj: Hemiola.Syntax.Object & HObject sobj})
    : option Kami.Syntax.Modules :=
    match objs with
    | nil => None
    | obj :: objs' =>
      (cmod <-- compile_Object obj;
      cmods <-- compile_Objects objs';
      Some (ConcatMod cmod cmods))
    end.
  
  Definition compile_System (sys: {ssys: Hemiola.Syntax.System & HSystem ssys})
    : option Kami.Syntax.Modules :=
    compile_Objects (hsys_objs (projT2 sys)).

End Compile.
