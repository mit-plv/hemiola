Require Import Numbers.DecimalString.

Require Import Hemiola.Common Hemiola.Index Hemiola.Syntax.
Require Import Hemiola.Ex.TopoTemplate.

Require Import Compiler.HemiolaDeep. (* source *)
Require Import Kami.Lib.Struct Kami Kami.PrimFifo Kami.PrimBram. (* target *)
Require Export Compiler.Components.

Set Implicit Arguments.

Lemma Vector_nth_map_comp {A B} (f: A -> B) {n} (v: Vector.t A n) (p: Fin.t n):
  Vector.nth (Vector.map f v) p = f (Vector.nth v p).
Proof.
  induction p.
  - revert n v; refine (@Vector.caseS _ _ _); now simpl.
  - revert n v p IHp; refine (@Vector.caseS _  _ _); now simpl.
Defined.

Import MonadNotations.

Section Compile.
  Context `{hcfg: hconfig} `{dv: DecValue} `{hdv: @HDecValue dv hcfg}
          `{oifc: OStateIfc}
          `{het: ExtType}
          `{hoifc: @HOStateIfc dv oifc}
          `{hoifcf: @HOStateIfcFull dv oifc hoifc het}.

  Definition KCIdm :=
    STRUCT { "cidx" :: KQIdx; "msg" :: Struct KMsg }.

  Section QueueIfc.

    Definition fifoBaseName: string := "fifo".
    Definition pcBaseName: string := "parentChildren".
    Definition enqN: string := "enq".
    Definition broadcastN: string := "broadcast".
    Definition deqN: string := "deq".

    Definition enqFn (midx: IdxT) :=
      (fifoBaseName ++ idx_to_string midx) -- enqN.
    Definition deqFn (midx: IdxT) :=
      (fifoBaseName ++ idx_to_string midx) -- deqN.
    Definition enqToChildFn (oidx: IdxT) :=
      (pcBaseName ++ idx_to_string oidx) -- enqN.
    Definition broadcastFn (oidx: IdxT) :=
      (pcBaseName ++ idx_to_string oidx) -- broadcastN.

    Definition deqFrom (midx: IdxT): Attribute SignatureT :=
      {| attrName := deqFn midx;
         attrType := {| arg := Void;
                        ret := Struct KMsg |} |}.
    Definition deqFromParent := deqFrom.
    Definition deqFromExt := deqFrom.
    Definition deqFromChild := deqFrom.

    Definition enqTo (midx: IdxT): Attribute SignatureT :=
      {| attrName := enqFn midx;
         attrType := {| arg := Struct KMsg;
                        ret := Void |} |}.
    Definition enqToParent := enqTo.
    Definition enqToExt := enqTo.

    Definition EnqToChild :=
      STRUCT { "ch_idx" :: KCIdx;
               "ch_msg" :: Struct KMsg
             }.

    Definition enqToChild (oidx: IdxT): Attribute SignatureT :=
      {| attrName := enqToChildFn oidx;
         attrType := {| arg := Struct EnqToChild;
                        ret := Void |} |}.

    Definition BroadcastToCs :=
      STRUCT { "cs_inds" :: KCBv;
               "cs_msg" :: Struct KMsg
             }.

    Definition broadcastToCs (oidx: IdxT): Attribute SignatureT :=
      {| attrName := broadcastFn oidx;
         attrType := {| arg := Struct BroadcastToCs;
                        ret := Void |} |}.

  End QueueIfc.

  Fixpoint kind_of_hbtype (hbt: hbtype): Kind :=
    match hbt with
    | HBool => Bool
    | HIdxO => KCIdx
    | HIdxQ => KQIdx
    | HIdxM => Bit ∘hcfg_msg_id_sz
    | HAddr => Bit hcfg_addr_sz
    | HNat w => Bit w
    | HMsg => Struct KMsg
    | HIdm => Struct KCIdm
    (* This is very arbitrary, but [HList] is only used for
     * sharer indices in a directory.. *)
    | HList hbt' => KCBv
    end.

  Definition compile_midx_to_qidx_const (midx: IdxT): ConstT KQIdx :=
    match midx with
    | (qidx :: cidx :: _)%list => combine $cidx $qidx
    | _ => Default
    end.

  Definition compile_midx_to_cidx_const (midx: IdxT): ConstT KCIdx :=
    match midx with
    | (_ :: cidx :: _)%list => $cidx
    | _ => Default
    end.

  Definition compile_oidx_to_cidx_const (oidx: IdxT): ConstT KCIdx :=
    match oidx with
    | (cidx :: _)%list => $cidx
    | _ => Default
    end.

  Definition compile_const {hbt} (hc: hbconst hbt)
    : ConstT (kind_of_hbtype hbt) :=
    match hc with
    | HBConstBool b => ConstBool b
    | HBConstNat w n => ConstBit (natToWord w n)
    | HBConstIdxO i => compile_oidx_to_cidx_const i
    | HBConstIdxQ i => compile_midx_to_qidx_const i
    | HBConstIdxM i => ConstBit (idx_to_word hcfg_msg_id_sz i)
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

      Variables (msgIn: var (Struct KMsg))
                (uln: string) (ul: var (Struct UL))
                (dln: string) (dl: var (Struct DL))
                (ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty)).

      Fixpoint compile_bexp {hbt} (he: hbexp (hbvar_of var) hbt)
        : Expr var (SyntaxKind (kind_of_hbtype hbt)) :=
        (match he with
         | HBConst _ c => Const _ (compile_const c)
         | HVar _ _ v => Var _ (SyntaxKind _) v
         | HIdmId pe => ((compile_bexp pe)!KCIdm@."cidx")
         | HIdmMsg pe => ((compile_bexp pe)!KCIdm@."msg")
         | HObjIdxOf midx => (_truncate_ (compile_bexp midx))
         | HAddrB _ => $0 (** Used only when making an eviction request with a nondet. addr *)
         | HMsgB mid mty maddr mval =>
           (STRUCT { "id" ::= compile_bexp mid;
                     "type" ::= compile_bexp mty;
                     "addr" ::= compile_bexp maddr;
                     "value" ::= compile_bexp mval })
         | HMsgId msg => ((compile_bexp msg)!KMsg@."id")
         | HMsgType msg => ((compile_bexp msg)!KMsg@."type")
         | HMsgAddr msg => ((compile_bexp msg)!KMsg@."addr")
         | HMsgValue msg => ((compile_bexp msg)!KMsg@."value")
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
         | HUpLockIdxBackI _ => ({$downIdx, #ul!UL@."ul_rsbTo"})
         | HDownLockIdxBackI _ => (#dl!DL@."dl_rsbTo")
         end)%kami_expr.

      Class CompExtExp :=
        { compile_eexp:
            forall (var: Kind -> Type) {het},
              var (Struct UL) -> var (Struct DL) ->
              HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty) ->
              heexp (hvar_of var) het ->
              Expr var (SyntaxKind (kind_of het));
          compile_eoprec:
            forall (var: Kind -> Type),
              var (Struct UL) -> var (Struct DL) ->
              HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty) ->
              heoprec (hvar_of var) ->
              Expr var (SyntaxKind Bool);
        }.
      Context `{CompExtExp}.

      Definition compile_exp {ht} (he: hexp (hvar_of var) ht)
        : Expr var (SyntaxKind (kind_of ht)) :=
        match he with
        | HBExp hbe => compile_bexp hbe
        | HEExp _ hee => compile_eexp var ul dl ostVars hee
        end.

      Definition compile_Rule_uplock
                 (cont: var (Struct UL) -> ActionT var Void): ActionT var Void :=
        (Read ul: Struct UL <- uln; cont ul)%kami_action.

      Definition compile_Rule_downlock
                 (cont: var (Struct DL) -> ActionT var Void): ActionT var Void :=
        (Read dl: Struct DL <- dln; cont dl)%kami_action.

      Definition compile_Rule_msg_from (mf: HMsgFrom)
                 (cont: var (Struct KMsg) -> ActionT var Void): ActionT var Void :=
        (match mf with
         | HMsgFromNil =>
           (* This is a hack, just by feeding a random value to the continuation *)
           (LET msgIn <- $$Default; cont msgIn)
         | HMsgFromParent pmidx =>
           (Call msgIn <- (deqFromParent pmidx)(); cont msgIn)
         | HMsgFromChild cmidx =>
           (Call msgIn <- (deqFromChild cmidx)(); cont msgIn)
         | HMsgFromExt emidx =>
           (Call msgIn <- (deqFromExt emidx)(); cont msgIn)
         | HMsgFromUpLock =>
           (Call msgIn <- (deqFromParent (downTo oidx))(); cont msgIn)
         | HMsgFromDownLock cidx =>
           (Call msgIn <- (deqFromChild cidx)(); cont msgIn)
         end)%kami_action.

      Definition compile_Rule_rqrs_prec (rrp: HOPrecR)
                 (cont: ActionT var Void): ActionT var Void :=
        (match rrp with
         | HRqAccepting => (Assert (!(#msgIn!KMsg@."type")); cont)
         | HRsAccepting => (Assert (#msgIn!KMsg@."type"); cont)
         | HUpLockFree =>
           (Call canUl <- (upLockable oidx) (#msgIn!KMsg@."addr"); Assert #canUl; cont)
         | HDownLockFree =>
           (Call canDl <- (downLockable oidx) (#msgIn!KMsg@."addr"); Assert #canDl; cont)
         | HUpLockMsgId _ _ =>
           (Call ul <- (upLockGet oidx) (#msgIn!KMsg@."addr");
           Assert #ul!(MaybeStr (Struct UL))@."valid";
           Write uln <- #ul!(MaybeStr (Struct UL))@."data";
           cont)
         | HUpLockMsg => cont
         | HUpLockIdxBack => cont
         | HUpLockBackNone => cont
         | HDownLockMsgId _ _ =>
           (Call dl <- (downLockGet oidx) (#msgIn!KMsg@."addr");
           Assert #dl!(MaybeStr (Struct DL))@."valid";
           Write dln <- #dl!(MaybeStr (Struct DL))@."data";
           cont)
         | HDownLockMsg => cont
         | HDownLockIdxBack => cont
         | HMsgIdFrom msgId => cont
         | HRssFull =>
           (Call dl <- (downLockRssFull oidx) (#msgIn!KMsg@."addr");
           Assert #dl!(MaybeStr (Struct DL))@."valid";
           Write dln <- #dl!(MaybeStr (Struct DL))@."data";
           cont)
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
         | HExtP _ ep => compile_eoprec _ ul dl ostVars ep
         | HNativeP _ _ => $$true
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
        (match hv in hbval hbt' return Expr var (SyntaxKind (kind_of_hbtype hbt')) with
         | HGetFirstMsg => #msgIn
         | HGetUpLockMsg => (#ul!UL@."ul_msg")
         | HGetDownLockMsg => (#dl!DL@."dl_msg")
         | HGetUpLockIdxBack => {$downIdx, (#ul!UL@."ul_rsbTo")}
         | HGetDownLockIdxBack => (#dl!DL@."dl_rsbTo")
         | HGetDownLockFirstRs =>
           (let fs := bvFirstSet (#dl!DL@."dl_rss_from") in
            STRUCT { "cidx" ::= {$rsUpIdx, fs};
                     "msg" ::= (#dl!DL@."dl_rss")#[fs] })
         end)%kami_expr.

      Fixpoint compile_OState_trs (host: HOState (hvar_of var))
               (cont: ActionT var Void): ActionT var Void :=
        (match host with
         | HOStateI _ => cont
         | @HOstUpdate _ _ _ _ _ _ _ i ht Heq he host' =>
           (Write (ostValNameI i) : (kind_of ht) <- (compile_exp he);
           compile_OState_trs host' cont)
         end)%kami_action.

      Definition compile_midx_to_cidx (midx: IdxT): Expr var (SyntaxKind KCIdx) :=
        Const _ (compile_midx_to_cidx_const midx).

      Definition compile_midx_to_qidx (midx: IdxT): Expr var (SyntaxKind KQIdx) :=
        Const _ (compile_midx_to_qidx_const midx).

      Definition compile_oidx_to_cidx (oidx: IdxT): Expr var (SyntaxKind KCIdx) :=
        Const _ (compile_oidx_to_cidx_const oidx).

      Fixpoint compile_ORq_trs (horq: HORq (hvar_of var))
               (cont: ActionT var Void): ActionT var Void :=
        (match horq with
         | HORqI _ => cont
         | HUpdUpLock rq _ rsb =>
           (Call (registerUL oidx)
                 (STRUCT { "r_ul_rsb" ::= $$true;
                           "r_ul_msg" ::= compile_exp rq;
                           "r_ul_rsbTo" ::= _truncate_ (compile_exp rsb) });
           cont)
         | HUpdUpLockS _ =>
           (Call (registerUL oidx)
                 (STRUCT { "r_ul_rsb" ::= $$false;
                           (** FIXME: [msg] should contain a nondet. address *)
                           "r_ul_msg" ::= $$Default;
                           "r_ul_rsbTo" ::= $$Default });
           cont)
         | HRelUpLock _ =>
           (Call (releaseUL oidx) (#msgIn!KMsg@."addr"); cont)
         | HUpdDownLock rq rssf rsb =>
           (Call (registerDL oidx)
                 (STRUCT { "r_dl_rsb" ::= $$true;
                           "r_dl_msg" ::= compile_exp rq;
                           "r_dl_rss_from" ::= compile_exp rssf;
                           "r_dl_rsbTo" ::= compile_exp rsb });
           cont)
         | HUpdDownLockS rssf =>
           (Call (registerDL oidx)
                 (STRUCT { "r_dl_rsb" ::= $$false;
                           (** FIXME: [msg] should contain a nondet. address *)
                           "r_dl_msg" ::= $$Default;
                           "r_dl_rss_from" ::= compile_exp rssf;
                           "r_dl_rsbTo" ::= $$Default });
           cont)
         | HRelDownLock _ =>
           (Call (releaseDL oidx) (#msgIn!KMsg@."addr"); cont)
         | HTrsfUpDown rq rssf rsb =>
           (Call (transferUpDown oidx)
                 (STRUCT { "r_dl_addr" ::= #msgIn!KMsg@."addr";
                           "r_dl_rss_from" ::= compile_exp rssf });
           cont)
         | HAddRs midx msg =>
           (Call (addRs oidx) (STRUCT { "r_dl_addr" ::= #msgIn!KMsg@."addr";
                                        "r_dl_midx" ::= _truncate_ (compile_exp midx);
                                        "r_dl_msg" ::= compile_exp msg });
           cont)
         end)%kami_action.

      Definition compile_MsgsOut_trs (hmsgs: HMsgsOut (hvar_of var))
                 (cont: ActionT var Void): ActionT var Void :=
        (match hmsgs with
         | HMsgOutNil _ => cont
         | HMsgOutOne midx msg =>
           (let kqidx := compile_exp midx in
            If (_truncLsb_ kqidx == $downIdx)
            then Call (enqToChild oidx)(STRUCT { "ch_idx" ::= _truncate_ kqidx;
                                                 "ch_msg" ::= compile_exp msg }); Retv
            else (If (_truncLsb_ kqidx == $rqUpIdx)
                  then Call (enqToParent (rqUpFrom oidx))(compile_exp msg); Retv
                  else Call (enqToParent (rsUpFrom oidx))(compile_exp msg); Retv; Retv);
           cont)
         | HMsgsOutDown minds msg =>
           (Call (broadcastToCs oidx)(STRUCT { "cs_inds" ::= compile_exp minds;
                                               "cs_msg" ::= compile_exp msg });
           cont)
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

    Local Notation "v <- f ; cont" :=
      (f (fun v => cont)) (at level 99, right associativity, only parsing).
    Local Notation "f ;; cont" :=
      (f cont) (at level 60, right associativity, only parsing).
    Definition compile_Rule (rule: {sr: Hemiola.Syntax.Rule & HRule sr}):
      Attribute (Action Void) :=
      let hr := projT2 rule in
      {| attrName := ruleNameI (rule_idx (projT1 rule));
         attrType :=
           fun var =>
             (ostVars <- compile_Rule_ost_vars ostin;
             msgIn <- compile_Rule_msg_from oidx (hrule_msg_from hr);
             ul <- compile_Rule_uplock uln;
             dl <- compile_Rule_downlock dln;
             compile_Rule_prec
               oidx msgIn uln ul dln dl ostVars (hrule_precond hr (hvar_of var));;
             compile_Rule_trs
               oidx ostin msgIn ul dl ostVars (hrule_trs hr))
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
    {| attrName := upLockReg oidx;
       attrType := RegInitDefault (SyntaxKind (Struct UL)) |}
      :: {| attrName := downLockReg oidx;
            attrType := RegInitDefault (SyntaxKind (Struct DL)) |}
      :: compile_inits oidx 0 (Vector.to_list hostf_ty).

  Definition build_int_fifos (oidx: IdxT): Modules :=
    ((fifo primNormalFifoName
           (fifoBaseName ++ idx_to_string (rqUpFrom oidx)) (Struct KMsg))
       ++ (fifo primNormalFifoName
                (fifoBaseName ++ idx_to_string (rsUpFrom oidx)) (Struct KMsg))
       ++ (fifo primNormalFifoName
                (fifoBaseName ++ idx_to_string (downTo oidx)) (Struct KMsg))
    )%kami.

  Definition build_ext_fifos (oidx: IdxT): Modules :=
    ((fifo primNormalFifoName
           (fifoBaseName ++ idx_to_string (rqUpFrom (l1ExtOf oidx)))
           (Struct KMsg))
       ++ (fifo primNormalFifoName
                (fifoBaseName ++ idx_to_string (downTo (l1ExtOf oidx)))
                (Struct KMsg))
    )%kami.

  Definition build_down_forward (oidx: IdxT): Modules :=
    MODULE {
      Method (enqToChildFn oidx)(e: Struct EnqToChild): Void :=
        LET msg <- #e!EnqToChild@."ch_msg";
        Call (enqTo (downTo (l1ExtOf oidx)))(#msg);
        Retv
    }.

  Fixpoint build_enq_child_fix (oidx: IdxT)
           {var} (cidx: KCIdx @ var) (msg: (Struct KMsg) @ var) (n: nat)
    : ActionT var Void :=
    (match n with
     | O => (If (cidx == $0) then (Call (enqTo (downTo (oidx~>0)))(msg); Retv); Retv)
     | S n' => (If (cidx == $n)
                then (Call (enqTo (downTo (oidx~>n)))(msg); Retv)
                else (build_enq_child_fix oidx cidx msg n');
               Retv)
     end)%kami_action.

  Fixpoint build_broadcast_fix (oidx: IdxT)
           {var} (cinds: KCBv @ var) (msg: (Struct KMsg) @ var) (n: nat)
    : ActionT var Void :=
    (match n with
     | O => (If (bvTest cinds $0) then (Call (enqTo (downTo (oidx~>0)))(msg); Retv); Retv)
     | S n' => (If (bvTest cinds $n) then (Call (enqTo (downTo (oidx~>n)))(msg); Retv);
                build_broadcast_fix oidx cinds msg n')
     end)%kami_action.

  Definition build_broadcaster (oidx: IdxT): Modules :=
    MODULE {
      Method (enqToChildFn oidx)(e: Struct EnqToChild): Void :=
        LET cidx <- #e!EnqToChild@."ch_idx";
        LET msg <- #e!EnqToChild@."ch_msg";
        build_enq_child_fix oidx (#cidx)%kami_expr (#msg)%kami_expr
                            hcfg_children_max_pred
      with Method (broadcastFn oidx)
           (e: Struct BroadcastToCs): Void :=
        LET cinds <- #e!BroadcastToCs@."cs_inds";
        LET msg <- #e!BroadcastToCs@."cs_msg";
        build_broadcast_fix oidx (#cinds)%kami_expr (#msg)%kami_expr
                            hcfg_children_max_pred
    }.

  Definition compile_Object (obj: {sobj: Hemiola.Syntax.Object & HObject sobj})
    : Modules :=
    let cregs := compile_OState_init (obj_idx (projT1 obj)) in
    let crules := compile_Rules (obj_idx (projT1 obj))
                                (upLockReg (obj_idx (projT1 obj)))
                                (downLockReg (obj_idx (projT1 obj)))
                                (ostIReg (obj_idx (projT1 obj)))
                                (hobj_rules (projT2 obj)) in
    Mod cregs crules nil.

  Definition compile_Object_with_init
             (obj: {sobj: Hemiola.Syntax.Object & HObject sobj})
             (kinit: list RegInitT) :=
    let crules := compile_Rules (obj_idx (projT1 obj))
                                (upLockReg (obj_idx (projT1 obj)))
                                (downLockReg (obj_idx (projT1 obj)))
                                (ostIReg (obj_idx (projT1 obj)))
                                (hobj_rules (projT2 obj)) in
    Mod kinit crules nil.

  Fixpoint compile_Objects (objs: list {sobj: Hemiola.Syntax.Object & HObject sobj})
    : option Kami.Syntax.Modules :=
    match objs with
    | nil => None
    | obj :: nil => Some (compile_Object obj)
    | obj :: objs' =>
      (let cmod := compile_Object obj in
       cmods <-- compile_Objects objs';
      Some (ConcatMod cmod cmods))
    end.

  Definition compile_System (sys: {ssys: Hemiola.Syntax.System & HSystem ssys})
    : option Kami.Syntax.Modules :=
    compile_Objects (hsys_objs (projT2 sys)).

End Compile.
