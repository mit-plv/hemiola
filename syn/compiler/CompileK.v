Require Import Numbers.DecimalString.

Require Import Hemiola.Common Hemiola.Index Hemiola.Syntax.
Require Import Hemiola.Ex.TopoTemplate.

Require Import Compiler.HemiolaDeep. (* source *)
Require Import Kami.Lib.Struct Kami Kami.PrimFifo Kami.PrimBram. (* target *)
Require Export Compiler.Components.

Set Implicit Arguments.

Import MonadNotations.

Section Compile.
  Context `{rcfg: ReifyConfig} `{tcfg: TopoConfig}
          `{dv: DecValue} `{hdv: @HDecValue dv}
          `{oifc: OStateIfc}
          `{het: ExtType}
          `{hoifc: @HOStateIfc dv oifc}
          `{hoifcf: @HOStateIfcFull dv oifc hoifc het}.

  Definition KCIdm :=
    STRUCT { "cidx" :: KQIdx; "msg" :: Struct KMsg }.

  Section QueueIfc.

    Definition fifoBaseName: string := "fifo".

    (* Input messages (deq) *)
    Definition deqN: string := "deq".
    Definition deqFn (midx: IdxT) :=
      (fifoBaseName ++ idx_to_string midx) -- deqN.
    Definition deqFrom (midx: IdxT): Attribute SignatureT :=
      {| attrName := deqFn midx;
         attrType := {| arg := Void;
                        ret := Struct KMsg |} |}.
    Definition deqFromParent := deqFrom.
    Definition deqFromExt := deqFrom.
    Definition deqFromChild := deqFrom.

    (* Output messages (enq) *)
    Definition enqN: string := "enq".
    Definition enqFn (midx: IdxT) :=
      (fifoBaseName ++ idx_to_string midx) -- enqN.
    Definition enqTo (midx: IdxT): Attribute SignatureT :=
      {| attrName := enqFn midx;
         attrType := {| arg := Struct KMsg;
                        ret := Void |} |}.

    Definition msgOutName: string := "parentChildren".
    Definition broadcastN: string := "broadcast".
    Definition broadcastFn (oidx: IdxT) :=
      (msgOutName ++ idx_to_string oidx) -- broadcastN.

    Definition MakeEnq :=
      STRUCT { "enq_type" :: Bit 2; (* rqUp(0), rsUp(1), down-to-child(2) *)
               "enq_ch_idx" :: KCIdx; (* only for down-to-child *)
               "enq_msg" :: Struct KMsg
             }.
    Definition MakeEnqK := Struct MakeEnq.

    Definition makeEnqN: string := "makeEnq".
    Definition makeEnqFn (oidx: IdxT) :=
      (msgOutName ++ idx_to_string oidx) -- makeEnqN.
    Definition makeEnq (oidx: IdxT): Attribute SignatureT :=
      {| attrName := makeEnqFn oidx;
         attrType := {| arg := MakeEnqK; ret := Void |} |}.

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
    | HValue => KValue
    | HNat w => Bit w
    | HMsg => Struct KMsg
    | HIdm => Struct KCIdm
    (* This is very arbitrary, but [HList] is only used for
     * sharer indices in a directory.. *)
    | HList hbt' => KCBv
    end.

  Definition compile_midx_to_qidx (midx: IdxT) {var}: Expr var (SyntaxKind KQIdx) :=
    match midx with
    | (qidx :: cidx :: _)%list => Const _ (combine $cidx $qidx)
    | _ => Default _ _
    end.

  Definition compile_midx_to_cidx (midx: IdxT) {var}: Expr var (SyntaxKind KCIdx) :=
    match midx with
    | (_ :: cidx :: _)%list => ($cidx)%kami_expr
    | _ => Default _ _
    end.

  Definition compile_oidx_to_cidx (oidx: IdxT) {var}: Expr var (SyntaxKind KCIdx) :=
    match oidx with
    | (cidx :: _)%list => ($cidx)%kami_expr
    | _ => Default _ _
    end.

  Definition compile_const {hbt} (hc: hbconst hbt) {var}
    : Expr var (SyntaxKind (kind_of_hbtype hbt)) :=
    match hc with
    | HBConstBool b => Const _ (ConstBool b)
    | HBConstNat w n => Const _ (ConstBit (natToWord w n))
    | HBConstIdxO i => compile_oidx_to_cidx i
    | HBConstIdxQ i => compile_midx_to_qidx i
    | HBConstIdxM i => Const _ (ConstBit (idx_to_word hcfg_msg_id_sz i))
    end.

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

  Section Pipeline.
    Context {var: Kind -> Type}.
    Variable oidx: IdxT.

    Variables indexSz lgWay edirLgWay: nat.

    Definition LineWrite infoK := LineWrite infoK KValue hcfg_addr_sz lgWay edirLgWay.
    Let LineWriteK infoK := Struct (LineWrite infoK).

    (** Information/value read and write *)
    Class CompLineRW :=
      { infoK: Kind;
        (* get_info_addr: *)
        (*   forall (var: Kind -> Type), *)
        (*     var infoK -> Expr var (SyntaxKind KAddr); *)
        (* set_info_addr: *)
        (*   forall (var: Kind -> Type), *)
        (*     Expr var (SyntaxKind infoK) -> Expr var (SyntaxKind KAddr) -> *)
        (*     Expr var (SyntaxKind infoK); *)
        (* compile_info_read: *)
        (*   forall (var: Kind -> Type), *)
        (*     var infoK -> Expr var (SyntaxKind infoK); *)
        compile_info_to_ostVars:
          forall (var: Kind -> Type),
            var infoK ->
            (HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty) ->
             ActionT var Void) ->
            ActionT var Void;
        compile_line_update:
          forall (var: Kind -> Type),
            var (LineWriteK infoK) ->
            forall (i: Fin.t ost_sz) ht,
              hostf_ty[@i] = ht ->
              Expr var (SyntaxKind (kind_of ht)) ->
              Expr var (SyntaxKind (LineWriteK infoK));
        (* check_inv_response: Fin.t ost_sz -> nat -> bool *)
      }.
    Context `{CompLineRW}.

    (** MSHRs *)
    Variable mshrNumPRqs mshrNumCRqs: nat.
    Let predMshrNumSlots := mshrNumPRqs + mshrNumCRqs - 1.
    Let mshrNumSlots := S predMshrNumSlots.
    Let mshrSlotSz := S (Nat.log2 predMshrNumSlots).
    Let MshrId := Bit mshrSlotSz.

    (*! Pipeline Stages *)
    (** * TODO: entry (or execution) rules for
     * 1) [InvRq], 2) [InvRs], 3) [RsRelease], and 4) [MSHRRetry]. *)

    Variables deqP2LRN deqC2LRN enqIR2LRN: string.

    Section InfoReadStage.

      Definition PPFrom := Bit 2.
      Definition PPFromPRq: Expr var (SyntaxKind PPFrom) := ($0)%kami_expr.
      Definition PPFromPRs: Expr var (SyntaxKind PPFrom) := ($1)%kami_expr.
      Definition PPFromCRq: Expr var (SyntaxKind PPFrom) := ($2)%kami_expr.
      Definition PPFromCRs: Expr var (SyntaxKind PPFrom) := ($3)%kami_expr.
      Definition IRPipe :=
        STRUCT { "ir_from" :: PPFrom;
                 "ir_cidx" :: KCIdx;
                 "ir_msg" :: Struct KMsg;
                 "ir_mshr_id" :: MshrId }.
      Definition IRPipeK := Struct IRPipe.
      Definition deqP2LR := MethodSig deqP2LRN(): IRPipeK.
      Definition deqC2LR := MethodSig deqC2LRN(): IRPipeK.
      Definition enqIR2LR := MethodSig enqIR2LRN(IRPipeK): Void.
      Local Notation getPRqSlot := (getPRqSlot oidx mshrNumPRqs mshrNumCRqs).
      Local Notation getCRqSlot := (getCRqSlot oidx mshrNumPRqs mshrNumCRqs).
      Local Notation findUL := (findUL oidx mshrNumPRqs mshrNumCRqs).
      Local Notation findDL := (findDL oidx mshrNumPRqs mshrNumCRqs).
      Local Notation infoRq := (infoRq oidx hcfg_addr_sz).
      Local Notation addRs := (addRs oidx).

      Definition infoReadStageRulePRq: ActionT var Void :=
        (Call pelt <- deqP2LR();
        LET msg <- #pelt!IRPipe@."ir_msg";
        Assert !(#msg!KMsg@."type");
        Call mmid <- getPRqSlot();
        Assert (#mmid!(MaybeStr MshrId)@."valid");
        LET mid <- #mmid!(MaybeStr MshrId)@."data";
        Call infoRq(#msg!KMsg@."addr");
        LET nelt <- STRUCT { "ir_from" ::= #pelt!IRPipe@."ir_from";
                             "ir_cidx" ::= #pelt!IRPipe@."ir_cidx";
                             "ir_msg" ::= #pelt!IRPipe@."ir_msg";
                             "ir_mshr_id" ::= #mid };
        Call enqIR2LR(#nelt);
        Retv)%kami_action.

      Definition infoReadStageRulePRs: ActionT var Void :=
        (Call pelt <- deqP2LR();
        LET msg <- #pelt!IRPipe@."ir_msg";
        Assert (#msg!KMsg@."type");
        Call mid <- findUL(#msg!KMsg@."addr");
        Call infoRq(#msg!KMsg@."addr");
        LET nelt <- STRUCT { "ir_from" ::= #pelt!IRPipe@."ir_from";
                             "ir_cidx" ::= #pelt!IRPipe@."ir_cidx";
                             "ir_msg" ::= #pelt!IRPipe@."ir_msg";
                             "ir_mshr_id" ::= #mid };
        Call enqIR2LR(#nelt);
        Retv)%kami_action.

      Definition infoReadStageRuleCRq: ActionT var Void :=
        (Call pelt <- deqC2LR();
        LET msg <- #pelt!IRPipe@."ir_msg";
        Assert !(#msg!KMsg@."type");
        Call mmid <- getCRqSlot();
        Assert (#mmid!(MaybeStr MshrId)@."valid");
        LET mid <- #mmid!(MaybeStr MshrId)@."data";
        Call infoRq(#msg!KMsg@."addr");
        LET nelt <- STRUCT { "ir_from" ::= #pelt!IRPipe@."ir_from";
                             "ir_cidx" ::= #pelt!IRPipe@."ir_cidx";
                             "ir_msg" ::= #pelt!IRPipe@."ir_msg";
                             "ir_mshr_id" ::= #mid };
        Call enqIR2LR(#nelt);
        Retv)%kami_action.

      Definition infoReadStageRuleCRs: ActionT var Void :=
        (Call pelt <- deqC2LR();
        LET msg <- #pelt!IRPipe@."ir_msg";
        Assert (#msg!KMsg@."type");
        Call addRs(STRUCT { "r_dl_midx" ::= #pelt!IRPipe@."ir_cidx";
                            "r_dl_msg" ::= #msg });
        (* No enq to the next stage *)
        Retv)%kami_action.

    End InfoReadStage.

    Variables deqIR2LRN enqLR2EXN: string.
    Local Notation InfoRead := (InfoRead infoK indexSz lgWay edirLgWay).

    Section LineReadStage.

      Definition LRPipe :=
        STRUCT { "lr_ir_pp" :: IRPipeK;
                 "lr_ir" :: Struct InfoRead
               }.
      Definition LRPipeK := Struct LRPipe.

      Definition deqIR2LR := MethodSig deqIR2LRN(): IRPipeK.
      Definition enqLR2EX := MethodSig enqLR2EXN(LRPipeK): Void.
      Local Notation infoRsValueRq := (infoRsValueRq oidx infoK indexSz lgWay edirLgWay).

      Definition lineReadStageRule: ActionT var Void :=
        (Call ir <- deqIR2LR();
        Call rinfo <- infoRsValueRq();
        LET lr <- STRUCT { "lr_ir_pp" ::= #ir; "lr_ir" ::= #rinfo };
        Call enqLR2EX(#lr);
        Retv)%kami_action.

    End LineReadStage.

    Class CompExtExp :=
      { compile_eexp:
          forall (var: Kind -> Type) {het},
            var (Struct KMsg) -> var (Struct MSHR) ->
            HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty) ->
            heexp (hvar_of var) het ->
            Expr var (SyntaxKind (kind_of het));
        compile_eoprec:
          forall (var: Kind -> Type),
            var (Struct KMsg) -> var (Struct MSHR) ->
            HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty) ->
            heoprec (hvar_of var) ->
            Expr var (SyntaxKind Bool);
      }.
    Context `{CompExtExp}.

    Class ValueInOst :=
      { valueOstIdx: Fin.t ost_sz;
        value_ost_idx_ok: kind_of hostf_ty[@valueOstIdx] = KValue
      }.
    Context `{ValueInOst}.

    Section CompileExec.
      Variables (msgIn: var (Struct KMsg))
                (mshrId: var MshrId) (mshr: var (Struct MSHR)).

      Section OstVarsNoValue.
        Variable ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty).

        Fixpoint compile_bexp {hbt} (he: hbexp (hbvar_of var) hbt)
          : Expr var (SyntaxKind (kind_of_hbtype hbt)) :=
          (match he with
           | HBConst _ c => compile_const c
           | HVar _ _ v => Var _ (SyntaxKind _) v
           | HIdmId pe => ((compile_bexp pe)!KCIdm@."cidx")
           | HIdmMsg pe => ((compile_bexp pe)!KCIdm@."msg")
           | HObjIdxOf midx => (_truncate_ (compile_bexp midx))
           | HAddrRep _ =>
             (* NOTE: [HAddrRep] is the representative address that is currently being
              * handled by the cache controller. Thus it is reasonable to take the address
              * from the input message. *)
             (#msgIn!KMsg@."addr")
           | HValueB _ => $$Default
           | HMsgB mid mty maddr mval =>
             (STRUCT { "id" ::= compile_bexp mid;
                       "type" ::= compile_bexp mty;
                       "addr" ::= compile_bexp maddr;
                       "value" ::= compile_bexp mval })
           | HMsgId msg => ((compile_bexp msg)!KMsg@."id")
           | HMsgType msg => ((compile_bexp msg)!KMsg@."type")
           | HMsgAddr msg => ((compile_bexp msg)!KMsg@."addr")
           | HMsgValue msg => ((compile_bexp msg)!KMsg@."value")
           | @HOstVal _ _ _ _ i hbt0 Heq =>
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
           (* The expressions below are used only when dealing with responses. *)
           | HUpLockIdxBackI _ => ({$downIdx, _truncate_ (#mshr!MSHR@."m_rsbTo")})
           | HDownLockIdxBackI _ => (#mshr!MSHR@."m_rsbTo")
           end)%kami_expr.

        Definition compile_exp {ht} (he: hexp (hvar_of var) ht)
          : Expr var (SyntaxKind (kind_of ht)) :=
          match he with
          | HBExp hbe => compile_bexp hbe
          | HEExp _ hee => compile_eexp var msgIn mshr ostVars hee
          end.

        Fixpoint compile_rule_prop_prec (pp: HOPrecP (hvar_of var))
          : Expr var (SyntaxKind Bool) :=
          (match pp with
           | HTrue _ => $$true
           | HAnd pp1 pp2 =>
             (compile_rule_prop_prec pp1) && (compile_rule_prop_prec pp2)
           | HOr pp1 pp2 =>
             (compile_rule_prop_prec pp1) || (compile_rule_prop_prec pp2)
           | HBoolT b => compile_exp b == $$true
           | HBoolF b => compile_exp b == $$false
           | HEq v1 v2 => compile_exp v1 == compile_exp v2
           | HNe v1 v2 => compile_exp v1 != compile_exp v2
           | HNatLt v1 v2 => compile_exp v1 < compile_exp v2
           | HNatLe v1 v2 => compile_exp v1 <= compile_exp v2
           | HNatGt v1 v2 => compile_exp v1 > compile_exp v2
           | HNatGe v1 v2 => compile_exp v1 >= compile_exp v2
           | HExtP _ ep => compile_eoprec _ msgIn mshr ostVars ep
           | HNativeP _ _ => $$true
           end)%kami_expr.

        Definition compile_rule_rqrs_prec (rrp: HOPrecR)
                   (cont: ActionT var Void): ActionT var Void :=
          (match rrp with
           | HRqAccepting => (Assert (!(#msgIn!KMsg@."type")); cont)
           | HRsAccepting => (Assert (#msgIn!KMsg@."type"); cont)
           | HUpLockFree =>
             (Call canUl <- (canRegUL oidx) (#msgIn!KMsg@."addr"); Assert #canUl; cont)
           | HDownLockFree =>
             (Call canDl <- (canRegDL oidx) (#msgIn!KMsg@."addr"); Assert #canDl; cont)
           | HUpLockMsgId mty mid =>
             (Assert (#mshr!MSHR@."m_valid");
             Assert (#mshr!MSHR@."m_rsb");
             Assert (#mshr!MSHR@."m_msg"!KMsg@."type" == Const _ (ConstBool mty));
             Assert (#mshr!MSHR@."m_msg"!KMsg@."id" == $$%mid%:hcfg_msg_id_sz);
             cont)
           | HUpLockMsg =>
             (Assert (#mshr!MSHR@."m_valid"); Assert (#mshr!MSHR@."m_rsb"); cont)
           | HUpLockIdxBack =>
             (Assert (#mshr!MSHR@."m_valid"); Assert (#mshr!MSHR@."m_rsb"); cont)
           | HUpLockBackNone =>
             (Assert (#mshr!MSHR@."m_valid"); Assert (!(#mshr!MSHR@."m_rsb")); cont)
           | HDownLockMsgId mty mid =>
             (Assert (#mshr!MSHR@."m_valid");
             Assert (#mshr!MSHR@."m_rsb");
             Assert (#mshr!MSHR@."m_msg"!KMsg@."type" == Const _ (ConstBool mty));
             Assert (#mshr!MSHR@."m_msg"!KMsg@."id" == $$%mid%:hcfg_msg_id_sz);
             cont)
           | HDownLockMsg =>
             (Assert (#mshr!MSHR@."m_valid"); Assert (#mshr!MSHR@."m_rsb"); cont)
           | HDownLockIdxBack =>
             (Assert (#mshr!MSHR@."m_valid"); Assert (#mshr!MSHR@."m_rsb"); cont)
           | HMsgIdFrom msgId => (Assert (#msgIn!KMsg@."id" == $$%msgId%:hcfg_msg_id_sz); cont)
           | HRssFull => (Assert (#mshr!MSHR@."dl_rss_recv" == #mshr!MSHR@."dl_rss_from"); cont)
           end)%kami_action.

        Fixpoint compile_rule_prec (rp: HOPrecT (hvar_of var))
                 (cont: ActionT var Void): ActionT var Void :=
          match rp with
          | HOPrecAnd prec1 prec2 =>
            let crule2 := compile_rule_prec prec2 cont in
            compile_rule_prec prec1 crule2
          | HOPrecRqRs _ rrprec => compile_rule_rqrs_prec rrprec cont
          | HOPrecProp pprec =>
            (Assert (compile_rule_prop_prec pprec); cont)%kami_action
          end.

        Definition compile_bval {hbt} (hv: hbval hbt)
          : Expr var (SyntaxKind (kind_of_hbtype hbt)) :=
          (match hv in hbval hbt' return Expr var (SyntaxKind (kind_of_hbtype hbt')) with
           | HGetFirstMsg => #msgIn
           | HGetUpLockMsg => (#mshr!MSHR@."m_msg")
           | HGetDownLockMsg => (#mshr!MSHR@."m_msg")
           | HGetUpLockIdxBack => {$downIdx, _truncate_ (#mshr!MSHR@."m_rsbTo")}
           | HGetDownLockIdxBack => (#mshr!MSHR@."m_rsbTo")
           | HGetDownLockFirstRs =>
             (let fs := bvFirstSet (#mshr!MSHR@."m_dl_rss_from") in
              STRUCT { "cidx" ::= {$rsUpIdx, fs};
                       "msg" ::= (#mshr!MSHR@."m_rss")#[fs] })
           end)%kami_expr.

        Fixpoint compile_OState_write_fix
                 (host: HOState (hvar_of var))
                 (rlw: var (LineWriteK infoK))
                 {retK} (cont: var (LineWriteK infoK) -> ActionT var retK): ActionT var retK :=
          (match host with
           | HOStateI _ => cont rlw
           | @HOstUpdate _ _ _ _ _ _ _ i ht Heq he host' =>
             (LET ninfo <- compile_line_update rlw _ Heq (compile_exp he);
             compile_OState_write_fix host' ninfo cont)
           end)%kami_action.

        Local Notation valueRsLineRq :=
          (valueRsLineRq oidx infoK KValue hcfg_addr_sz lgWay edirLgWay).

        Definition compile_OState_request_write
                   (host: HOState (hvar_of var)) (pline: var (LineWriteK infoK))
                   (cont: var KValue -> ActionT var Void): ActionT var Void :=
          match host with
          | HOStateI _ =>
            (** Feeding [$$Default] for [LineWrite] means "no writes." *)
            (Call rvalue <- valueRsLineRq($$Default); cont rvalue)
          | _ => compile_OState_write_fix
                   host pline
                   (fun nline => Call rvalue <- valueRsLineRq(#nline); cont rvalue)
          end%kami_action.

      End OstVarsNoValue.

      Section OstVarsWithValue.
        Variable ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty).
        Local Notation compile_exp := (compile_exp ostVars).

        Local Notation registerUL := (registerUL oidx mshrNumPRqs mshrNumCRqs).
        Local Notation registerDL := (registerDL oidx mshrNumPRqs mshrNumCRqs).
        Local Notation release := (release oidx mshrNumPRqs mshrNumCRqs).
        Local Notation transferUpDown := (transferUpDown oidx mshrNumPRqs mshrNumCRqs).
        Local Notation addRs := (addRs oidx).

        Fixpoint compile_ORq_trs (horq: HORq (hvar_of var))
                 (cont: ActionT var Void): ActionT var Void :=
          (match horq with
           | HORqI _ => cont
           | HUpdUpLock rq _ rsb =>
             (* Call hasV <- (hasVictim oidx)(); Assert (!#hasV); *)
             (Call registerUL(STRUCT { "r_id" ::= #mshrId;
                                       "r_ul_msg" ::= compile_exp rq;
                                       "r_ul_rsb" ::= $$true;
                                       "r_ul_rsbTo" ::= _truncate_ (compile_exp rsb) }); cont)
           | HUpdUpLockS _ =>
             (Call registerUL(STRUCT { "r_id" ::= #mshrId;
                                       (* already properly set for eviction;
                                        * see [compile_rule_get_readlock_msg]. *)
                                       "r_ul_msg" ::= #msgIn;
                                       "r_ul_rsb" ::= $$false;
                                       "r_ul_rsbTo" ::= $$Default }); cont)
           | HRelUpLock _ => (Call release(#mshrId); cont)
           | HUpdDownLock rq rssf rsb =>
             (Call registerDL(STRUCT { "r_id" ::= #mshrId;
                                       "r_dl_msg" ::= compile_exp rq;
                                       "r_dl_rss_from" ::= compile_exp rssf;
                                       "r_dl_rsb" ::= $$true;
                                       "r_dl_rsbTo" ::= compile_exp rsb }); cont)
           | HUpdDownLockS rssf =>
             (** NOTE: silent down-requests;
              * not used in non-inclusive cache-coherence protocols *)
             (Call registerDL (STRUCT { "r_id" ::= #mshrId;
                                        "r_dl_msg" ::= $$Default;
                                        "r_dl_rss_from" ::= compile_exp rssf;
                                        "r_dl_rsb" ::= $$false;
                                        "r_dl_rsbTo" ::= $$Default });
             cont)
           | HRelDownLock _ => (Call release(#mshrId); cont)
           | HTrsfUpDown rq rssf rsb =>
             (Call transferUpDown (STRUCT { "r_id" ::= #mshrId;
                                            "r_dl_rss_from" ::= compile_exp rssf });
             cont)
           | HAddRs midx msg =>
             (Call addRs (STRUCT { "r_dl_midx" ::= _truncate_ (compile_exp midx);
                                   "r_dl_msg" ::= compile_exp msg });
             cont)
           end)%kami_action.

        Definition compile_MsgsOut_trs (hmsgs: HMsgsOut (hvar_of var))
                   (cont: ActionT var Void): ActionT var Void :=
          (match hmsgs with
           | HMsgOutNil _ => cont
           | HMsgOutOne midx msg =>
             (let kqidx := compile_exp midx in
              LET menqv <- STRUCT { "enq_type" ::=
                                      (IF (_truncLsb_ kqidx == $downIdx) then $2
                                       else IF (_truncLsb_ kqidx == $rqUpIdx)
                                       then $0 else $1);
                                    "enq_ch_idx" ::= _truncate_ kqidx;
                                    "enq_msg" ::= compile_exp msg };
             Call (makeEnq oidx)(#menqv);
             cont)
           | HMsgsOutDown minds msg =>
             (Call (broadcastToCs oidx)(STRUCT { "cs_inds" ::= compile_exp minds;
                                                 "cs_msg" ::= compile_exp msg });
             cont)
           end)%kami_action.

      End OstVarsWithValue.

      Variables (pir: var (Struct InfoRead)).

      Fixpoint compile_MonadT_trs
               (ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
               (hm: HMonadT (hvar_of var))
               (cont: ActionT var Void): ActionT var Void :=
        (match hm with
         | HBind hv mcont =>
           Let_ (compile_bval hv)
                (fun x: var (kind_of_hbtype _) => compile_MonadT_trs ostVars (mcont x) cont)
         | HRet host horq hmsgs =>
           (LET pline: (LineWriteK infoK) <- STRUCT { "addr" ::= #msgIn!KMsg@."addr";
                                                      "info_write" ::= $$false;
                                                      "info_hit" ::= #pir!InfoRead@."info_hit";
                                                      "info_way" ::= #pir!InfoRead@."info_way";
                                                      "edir_hit" ::= #pir!InfoRead@."edir_hit";
                                                      "edir_way" ::= #pir!InfoRead@."edir_way";
                                                      "edir_slot" ::= #pir!InfoRead@."edir_slot";
                                                      "info" ::= #pir!InfoRead@."info";
                                                      "value_write" ::= $$false;
                                                      (* The previous value is not used for
                                                       * local state updates; it may be used for
                                                       * [OTrs] updates or output messages. *)
                                                      "value" ::= $$Default };
           compile_OState_request_write
             ostVars host pline
             (fun rvalue: var KValue =>
                let nostVars := HVector.hvec_upd
                                  ostVars valueOstIdx
                                  (eq_rect_r
                                     id (eq_rect_r var rvalue value_ost_idx_ok)
                                     (Vector_nth_map_comp
                                        (fun hty => var (kind_of hty)) hostf_ty valueOstIdx)) in
                compile_ORq_trs nostVars horq (compile_MsgsOut_trs nostVars hmsgs cont)))
         end)%kami_action.

      Definition compile_rule_trs
                 (ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
                 (trs: HOTrs) (cont: ActionT var Void): ActionT var Void :=
        match trs with
        | HTrsMTrs (HMTrs mn) => compile_MonadT_trs ostVars (mn (hvar_of var)) cont
        end.

    End CompileExec.

    Variables deqLR2EXN: string.

    Section ExecStage.

      Definition deqLR2EX := MethodSig deqLR2EXN(): LRPipeK.

      (** Message-execution cases:
       * - [execStageRuleHit]: the precondition holds and the MSHR slot is properly lockable
       * - [execStageRuleWait]: the precondition holds but need to wait another
       *   lock to be released. Push the message to the waiting queue in the MSHR module.
       * - [execStageRuleRetry]: pull the message from the waiting queue and retry handling it.
       * + maybe something more?
       *)

      Local Notation valueRsLineRq :=
        (valueRsLineRq oidx infoK KValue hcfg_addr_sz lgWay edirLgWay).
      Local Notation getMSHR := (getMSHR oidx mshrNumPRqs mshrNumCRqs).

      Variables (rule: {sr: Hemiola.Syntax.Rule & HRule sr}).
      Let hr := projT2 rule.

      Local Notation "v <- f ; cont" :=
        (f (fun v => cont)) (at level 12, right associativity, only parsing): kami_action_scope.
      Local Notation ": f ; cont" :=
        (f cont) (at level 12, right associativity, only parsing): kami_action_scope.

      Definition execStageRuleHit: ActionT var Void :=
        (Call lr <- deqLR2EX();
        LET pir <- #lr!LRPipe@."lr_ir";
        LET pinfo <- #pir!InfoRead@."info";
        LET msgIn <- #lr!LRPipe@."lr_ir_pp"!IRPipe@."ir_msg";
        LET mshrId <- #lr!LRPipe@."lr_ir_pp"!IRPipe@."ir_mshr_id";
        Call mshr <- getMSHR(#mshrId);
        ostVars <- compile_info_to_ostVars pinfo;
        :compile_rule_prec
           msgIn mshr ostVars (hrule_precond hr (hvar_of var));
        :compile_rule_trs msgIn mshrId mshr pir ostVars (hrule_trs hr);
        Retv)%kami_action.

      (** * TODO: how to define [execStageRuleWait]?? *)

    End ExecStage.

  End Pipeline.

  Context `{ee: @ExtExp dv oifc het} `{cet: CompExtType}
          `{CompExtExp} `{CompLineRW}.

  Section WithObj.
    Variables (oidx: IdxT).

    Definition ruleNameBase: string := "rule".
    Definition ruleNameI (ridx: IdxT) :=
      (ruleNameBase
         ++ "_" ++ idx_to_string oidx
         ++ "_" ++ idx_to_string ridx)%string.

    Definition compile_rules (dtr: Topology.DTree)
               (rules: list {sr: Hemiola.Syntax.Rule & HRule sr}):
      list (Attribute (Action Void)) :=
      (** * TODO: add compiled rules. *)
      nil.

  End WithObj.

  Definition compile_OState_init (oidx: IdxT): list RegInitT :=
    (** * TODO: add necessary registers. *)
    (* {| attrName := rrReg oidx; attrType := RegInitDefault (SyntaxKind (Bit 1)) |} *)
    nil.

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

  Section MsgOuts.
    Variable oidx: IdxT.
    Local Notation "s '+o'" := (s ++ "_" ++ idx_to_string oidx)%string (at level 60).

    Definition build_l1_down {var} (msg: (Struct KMsg) @ var): ActionT var Void :=
      (Call (enqTo (downTo (l1ExtOf oidx)))(msg); Retv)%kami_action.

    Fixpoint build_enq_child_fix {var}
             (cidx: KCIdx @ var) (msg: (Struct KMsg) @ var) (n: nat)
      : ActionT var Void :=
      (match n with
       | O => (If (cidx == $0) then (Call (enqTo (downTo (oidx~>0)))(msg); Retv); Retv)
       | S n' => (If (cidx == $n)
                  then (Call (enqTo (downTo (oidx~>n)))(msg); Retv)
                  else (build_enq_child_fix cidx msg n');
                 Retv)
       end)%kami_action.

    Fixpoint build_broadcast_fix {var}
             (cinds: KCBv @ var) (msg: (Struct KMsg) @ var) (n: nat)
      : ActionT var Void :=
      (match n with
       | O => (If (bvTest cinds $0) then (Call (enqTo (downTo (oidx~>0)))(msg); Retv); Retv)
       | S n' => (If (bvTest cinds $n) then (Call (enqTo (downTo (oidx~>n)))(msg); Retv);
                  build_broadcast_fix cinds msg n')
       end)%kami_action.

    Definition enqRqN := "enqRq"+o.
    Definition enqValidN := "enqValid"+o.

    Definition enqRqUp {var}: ActionT var Void :=
      (Read enqValid <- enqValidN;
      Assert (#enqValid);
      Write enqValidN <- $$false;
      Read enqRq: MakeEnqK <- enqRqN;
      Assert (#enqRq!MakeEnq@."enq_type" == $0);
      Call (enqTo (rqUpFrom oidx))(#enqRq!MakeEnq@."enq_msg");
      Retv)%kami_action.

    Definition enqRsUp {var}: ActionT var Void :=
      (Read enqValid <- enqValidN;
      Assert (#enqValid);
      Write enqValidN <- $$false;
      Read enqRq: MakeEnqK <- enqRqN;
      Assert (#enqRq!MakeEnq@."enq_type" == $1);
      Call (enqTo (rsUpFrom oidx))(#enqRq!MakeEnq@."enq_msg");
      Retv)%kami_action.

    Definition enqDownToL1 {var}: ActionT var Void :=
      (Read enqValid <- enqValidN;
      Assert (#enqValid);
      Write enqValidN <- $$false;
      Read enqRq: MakeEnqK <- enqRqN;
      Assert (#enqRq!MakeEnq@."enq_type" == $2);
      LET msg <- #enqRq!MakeEnq@."enq_msg";
      build_l1_down (#msg)%kami_expr)%kami_action.

    Definition enqDownToChild {var}: ActionT var Void :=
      (Read enqValid <- enqValidN;
      Assert (#enqValid);
      Write enqValidN <- $$false;
      Read enqRq: MakeEnqK <- enqRqN;
      Assert (#enqRq!MakeEnq@."enq_type" == $2);
      LET cidx <- #enqRq!MakeEnq@."enq_ch_idx";
      LET msg <- #enqRq!MakeEnq@."enq_msg";
      build_enq_child_fix (#cidx)%kami_expr (#msg)%kami_expr
                          hcfg_children_max_pred)%kami_action.

    Definition build_msg_outs_l1_async: Modules :=
      MODULE {
        Register enqRqN: MakeEnqK <- Default
        with Register enqValidN: Bool <- Default
        with Method (makeEnqFn oidx)(e: MakeEnqK): Void :=
          Read enqValid <- enqValidN;
          Assert (!#enqValid);
          Write enqValidN <- $$true;
          Write enqRqN <- #e;
          Retv
        with Rule "make_enq_rqUp"+o := enqRqUp
        with Rule "make_enq_rsUp"+o := enqRsUp
        with Rule "make_enq_down_to_child"+o := enqDownToL1
      }.

    Definition build_msg_outs_l1: Modules :=
      MODULE {
        Method (makeEnqFn oidx)(e: MakeEnqK): Void :=
          (If (#e!MakeEnq@."enq_type" == $0)
           then (Call (enqTo (rqUpFrom oidx))(#e!MakeEnq@."enq_msg"); Retv)
           else (If (#e!MakeEnq@."enq_type" == $1)
                 then (Call (enqTo (rsUpFrom oidx))(#e!MakeEnq@."enq_msg"); Retv)
                 else (LET msg <- #e!MakeEnq@."enq_msg";
                      build_l1_down (#msg)%kami_expr);
                Retv);
          Retv)
      }.

    Definition build_msg_outs_li_async: Modules :=
      MODULE {
        Register enqRqN: MakeEnqK <- Default
        with Register enqValidN: Bool <- Default
        with Method (makeEnqFn oidx)(e: MakeEnqK): Void :=
          Read enqValid <- enqValidN;
          Assert (!#enqValid);
          Write enqValidN <- $$true;
          Write enqRqN <- #e;
          Retv
        with Method (broadcastFn oidx)(e: Struct BroadcastToCs): Void :=
          LET cinds <- #e!BroadcastToCs@."cs_inds";
          LET msg <- #e!BroadcastToCs@."cs_msg";
          build_broadcast_fix (#cinds)%kami_expr (#msg)%kami_expr
                              hcfg_children_max_pred
        with Rule "make_enq_rqUp"+o := enqRqUp
        with Rule "make_enq_rsUp"+o := enqRsUp
        with Rule "make_enq_down_to_child"+o := enqDownToChild
      }.

    Definition build_msg_outs_li: Modules :=
      MODULE {
        Method (makeEnqFn oidx)(e: MakeEnqK): Void :=
          (If (#e!MakeEnq@."enq_type" == $0)
           then (Call (enqTo (rqUpFrom oidx))(#e!MakeEnq@."enq_msg"); Retv)
           else (If (#e!MakeEnq@."enq_type" == $1)
                 then (Call (enqTo (rsUpFrom oidx))(#e!MakeEnq@."enq_msg"); Retv)
                 else (LET cidx <- #e!MakeEnq@."enq_ch_idx";
                      LET msg <- #e!MakeEnq@."enq_msg";
                      build_enq_child_fix (#cidx)%kami_expr (#msg)%kami_expr
                                          hcfg_children_max_pred);
                Retv);
          Retv)
        with Method (broadcastFn oidx)(e: Struct BroadcastToCs): Void :=
          LET cinds <- #e!BroadcastToCs@."cs_inds";
          LET msg <- #e!BroadcastToCs@."cs_msg";
          build_broadcast_fix (#cinds)%kami_expr (#msg)%kami_expr
                              hcfg_children_max_pred
      }.

    Definition build_msg_outs_mem: Modules :=
      MODULE {
        Method (makeEnqFn oidx)(e: MakeEnqK): Void :=
          LET msg <- #e!MakeEnq@."enq_msg";
          Call (enqTo (downTo (oidx~>0)))(#msg);
          Retv
      }.

  End MsgOuts.

  Definition compile_Object (dtr: Topology.DTree)
             (obj: {sobj: Hemiola.Syntax.Object & HObject sobj})
    : Modules :=
    let oidx := obj_idx (projT1 obj) in
    let cregs := compile_OState_init oidx in
    let crules := compile_rules dtr (hobj_rules (projT2 obj)) in
    Mod cregs crules nil.

  Fixpoint compile_Objects (dtr: Topology.DTree)
           (objs: list {sobj: Hemiola.Syntax.Object & HObject sobj})
    : option Kami.Syntax.Modules :=
    match objs with
    | nil => None
    | obj :: nil => Some (compile_Object dtr obj)
    | obj :: objs' =>
      (let cmod := compile_Object dtr obj in
       cmods <-- compile_Objects dtr objs';
      Some (ConcatMod cmod cmods))
    end.

  Definition compile_System (dtr: Topology.DTree)
             (sys: {ssys: Hemiola.Syntax.System & HSystem ssys})
    : option Kami.Syntax.Modules :=
    compile_Objects dtr (hsys_objs (projT2 sys)).

End Compile.
