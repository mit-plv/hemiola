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

  (** Caches *)
  Variables indexSz lgWay edirLgWay: nat.

  (** MSHRs *)
  Variables mshrNumPRqs mshrNumCRqs: nat.
  Let predMshrNumSlots := mshrNumPRqs + mshrNumCRqs - 1.
  Let mshrNumSlots := S predMshrNumSlots.
  Let mshrSlotSz := S (Nat.log2 predMshrNumSlots).
  Let MshrId := Bit mshrSlotSz.
  Local Notation MSHR := (MSHR mshrNumPRqs mshrNumCRqs).

  (** Victims *)
  Variable predNumVictims: nat.
  Let victimIdxSz := Nat.log2 predNumVictims.

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

    Definition LineWrite infoK := LineWrite infoK KValue hcfg_addr_sz lgWay edirLgWay.
    Let LineWriteK infoK := Struct (LineWrite infoK).

    (** Information/value read and write *)
    Class CompLineRW :=
      { infoK: Kind;
        invRsId: word ∘hcfg_msg_id_sz;
        compile_info_to_ostVars:
          forall (var: Kind -> Type),
            var infoK ->
            (HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty) ->
             ActionT var Void) ->
            ActionT var Void;
        compile_value_read_to_ostVars:
          forall (var: Kind -> Type),
            HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty) ->
            var KValue ->
            HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty);
        compile_line_update:
          forall (var: Kind -> Type),
            var (LineWriteK infoK) ->
            forall (i: Fin.t ost_sz) ht,
              hostf_ty[@i] = ht ->
              Expr var (SyntaxKind (kind_of ht)) ->
              Expr var (SyntaxKind (LineWriteK infoK))
      }.
    Context `{CompLineRW}.

    (*! Inputs *)

    (** Gathering messages from children *)

    Definition ChildInput :=
      STRUCT { "ch_idx" :: KCIdx;
               "ch_msg" :: Struct KMsg }.
    Let ChildInputK := Struct ChildInput.

    Definition IRPipe :=
      STRUCT { "ir_is_rs_rel" :: Bool;
               "ir_msg" :: Struct KMsg;
               "ir_msg_from" :: KQIdx;
               "ir_mshr_id" :: MshrId }.
    Let IRPipeK := Struct IRPipe.

    Variables enqCRqN enqCRsN: string.

    Definition cRqAcceptor4 (cidx0 cidx1 cidx2 cidx3: IdxT): Modules :=
      acceptor4
        oidx (eltT:= ChildInputK)
        (fun _ msg => STRUCT { "ch_idx" ::= $0; "ch_msg" ::= #msg })%kami_expr
        (fun _ msg => STRUCT { "ch_idx" ::= $1; "ch_msg" ::= #msg })%kami_expr
        (fun _ msg => STRUCT { "ch_idx" ::= $2; "ch_msg" ::= #msg })%kami_expr
        (fun _ msg => STRUCT { "ch_idx" ::= $3; "ch_msg" ::= #msg })%kami_expr
        (deqFn (rqUpFrom cidx0)) (deqFn (rqUpFrom cidx1))
        (deqFn (rqUpFrom cidx2)) (deqFn (rqUpFrom cidx3)) enqCRqN.

    Definition cRsAcceptor4 (cidx0 cidx1 cidx2 cidx3: IdxT): Modules :=
      acceptor4
        oidx (eltT:= ChildInputK)
        (fun _ msg => STRUCT { "ch_idx" ::= $0; "ch_msg" ::= #msg })%kami_expr
        (fun _ msg => STRUCT { "ch_idx" ::= $1; "ch_msg" ::= #msg })%kami_expr
        (fun _ msg => STRUCT { "ch_idx" ::= $2; "ch_msg" ::= #msg })%kami_expr
        (fun _ msg => STRUCT { "ch_idx" ::= $3; "ch_msg" ::= #msg })%kami_expr
        (deqFn (rqUpFrom cidx0)) (deqFn (rqUpFrom cidx1))
        (deqFn (rqUpFrom cidx2)) (deqFn (rqUpFrom cidx3)) enqCRsN.

    Variables deqCRqN deqCRsN enqInputN: string.

    Definition inputAcceptor2: Modules :=
      acceptor2
        oidx (peltT0:= Struct KMsg) (peltT1:= Struct KMsg) (eltT:= IRPipeK)
        (fun _ msg => STRUCT { "ir_is_rs_rel" ::= $$false;
                               "ir_msg" ::= #msg;
                               "ir_msg_from" ::= {$downIdx, compile_oidx_to_cidx oidx};
                               "ir_mshr_id" ::= $$Default })%kami_expr
        (fun _ msg => STRUCT { "ir_is_rs_rel" ::= $$false;
                               "ir_msg" ::= #msg;
                               "ir_msg_from" ::= {$rqUpIdx, compile_oidx_to_cidx (l1ExtOf oidx)};
                               "ir_mshr_id" ::= $$Default })%kami_expr
        (deqFn (downTo oidx)) (deqFn (rqUpFrom (l1ExtOf oidx))) enqInputN.

    Definition inputAcceptor3: Modules :=
      acceptor3
        oidx (peltT0:= Struct KMsg) (peltT1:= ChildInputK) (peltT2:= ChildInputK) (eltT:= IRPipeK)
        (fun _ msg => STRUCT { "ir_is_rs_rel" ::= $$false;
                               "ir_msg" ::= #msg;
                               "ir_msg_from" ::= {$downIdx, compile_oidx_to_cidx oidx};
                               "ir_mshr_id" ::= $$Default })%kami_expr
        (fun _ ci => STRUCT { "ir_is_rs_rel" ::= $$false;
                              "ir_msg" ::= #ci!ChildInput@."ch_msg";
                              "ir_msg_from" ::= {$rqUpIdx, #ci!ChildInput@."ch_idx"};
                              "ir_mshr_id" ::= $$Default })%kami_expr
        (fun _ ci => STRUCT { "ir_is_rs_rel" ::= $$false;
                              "ir_msg" ::= #ci!ChildInput@."ch_msg";
                              "ir_msg_from" ::= {$rsUpIdx, #ci!ChildInput@."ch_idx"};
                              "ir_mshr_id" ::= $$Default })%kami_expr
        (deqFn (downTo oidx)) deqCRqN deqCRsN enqInputN.

    (*! Pipeline Stages *)

    Variables deqInputN enqIR2LRN: string.

    Section InfoReadStage.

      Definition deqInput := MethodSig deqInputN(): IRPipeK.
      Definition enqIR2LR := MethodSig enqIR2LRN(IRPipeK): Void.

      Local Notation infoRq := (infoRq oidx hcfg_addr_sz).
      Local Notation releaseVictim := (releaseVictim oidx hcfg_addr_sz mshrSlotSz).

      Local Notation getPRqSlot := (getPRqSlot oidx mshrNumPRqs mshrNumCRqs).
      Local Notation getCRqSlot := (getCRqSlot oidx mshrNumPRqs mshrNumCRqs).
      Local Notation GetSlot := (GetSlot mshrNumPRqs mshrNumCRqs).
      Let GetSlotK := Struct GetSlot.
      Local Notation findUL := (findUL oidx mshrNumPRqs mshrNumCRqs).
      Local Notation findDL := (findDL oidx mshrNumPRqs mshrNumCRqs).
      Local Notation addRs := (addRs oidx).
      Local Notation getRsReady := (getRsReady oidx mshrNumPRqs mshrNumCRqs).
      Local Notation RsReady := (RsReady mshrNumPRqs mshrNumCRqs).
      Let RsReadyK := Struct RsReady.
      Local Notation releaseMSHR := (releaseMSHR oidx mshrNumPRqs mshrNumCRqs).
      Local Notation getWait := (getWait oidx mshrNumPRqs mshrNumCRqs).
      Local Notation PreMSHR := (PreMSHR mshrNumPRqs mshrNumCRqs).
      Let PreMSHRK := Struct PreMSHR.

      Definition irPRq: ActionT var Void :=
        (Call pelt <- deqInput();
        LET mf <- #pelt!IRPipe@."ir_msg_from";
        Assert (#mf == {$downIdx, compile_oidx_to_cidx oidx});
        LET msg <- #pelt!IRPipe@."ir_msg";
        Assert !(#msg!KMsg@."type");
        Call gs <- getPRqSlot(STRUCT { "r_id" ::= $$Default;
                                       "r_msg" ::= #msg;
                                       "r_msg_from" ::= #pelt!IRPipe@."ir_msg_from" });
        Assert (#gs!GetSlot@."s_has_slot");
        If !(#gs!GetSlot@."s_conflict")
        then (Call infoRq(#msg!KMsg@."addr");
             LET nelt <- STRUCT { "ir_is_rs_rel" ::= $$false;
                                  "ir_msg" ::= #pelt!IRPipe@."ir_msg";
                                  "ir_msg_from" ::= #mf;
                                  "ir_mshr_id" ::= #gs!GetSlot@."s_id" };
             Call enqIR2LR(#nelt);
             Retv);
        Retv)%kami_action.

      Definition irPRs: ActionT var Void :=
        (Call pelt <- deqInput();
        LET mf <- #pelt!IRPipe@."ir_msg_from";
        Assert (#mf == {$downIdx, compile_oidx_to_cidx oidx});
        LET msg <- #pelt!IRPipe@."ir_msg";
        Assert (#msg!KMsg@."type" && #msg!KMsg@."id" != $$invRsId);
        Call mid <- findUL(#msg!KMsg@."addr");
        Call infoRq(#msg!KMsg@."addr");
        LET nelt <- STRUCT { "ir_is_rs_rel" ::= $$false;
                             "ir_msg" ::= #pelt!IRPipe@."ir_msg";
                             "ir_msg_from" ::= #mf;
                             "ir_mshr_id" ::= #mid };
        Call enqIR2LR(#nelt);
        Retv)%kami_action.

      Definition irCRq: ActionT var Void :=
        (Call pelt <- deqInput();
        LET mf <- #pelt!IRPipe@."ir_msg_from";
        Assert (_truncLsb_ #mf == $rqUpIdx);
        LET msg <- #pelt!IRPipe@."ir_msg";
        Assert !(#msg!KMsg@."type");
        Call gs <- getCRqSlot(STRUCT { "r_id" ::= $$Default;
                                       "r_msg" ::= #msg;
                                       "r_msg_from" ::= #mf });
        Assert (#gs!GetSlot@."s_has_slot");
        If !(#gs!GetSlot@."s_conflict")
        then (Call infoRq(#msg!KMsg@."addr");
             LET nelt <- STRUCT { "ir_is_rs_rel" ::= $$false;
                                  "ir_msg" ::= #pelt!IRPipe@."ir_msg";
                                  "ir_msg_from" ::= #mf;
                                  "ir_mshr_id" ::= #gs!GetSlot@."s_id" };
             Call enqIR2LR(#nelt);
             Retv);
        Retv)%kami_action.

      Definition irCRs: ActionT var Void :=
        (Call pelt <- deqInput();
        LET mf <- #pelt!IRPipe@."ir_msg_from";
        Assert (_truncLsb_ #mf == $rsUpIdx);
        LET msg <- #pelt!IRPipe@."ir_msg";
        Assert (#msg!KMsg@."type");
        Call addRs(STRUCT { "r_dl_midx" ::= _truncate_ #mf; "r_dl_msg" ::= #msg });
        (** No enq to the next stage *)
        Retv)%kami_action.

      Definition irRetry: ActionT var Void :=
        (Call mpmshr <- getWait();
        Assert (#mpmshr!(MaybeStr PreMSHRK)@."valid");
        LET pmshr <- #mpmshr!(MaybeStr PreMSHRK)@."data";
        LET msg <- #pmshr!PreMSHR@."r_msg";
        Call infoRq(#msg!KMsg@."addr");
        LET nelt <- STRUCT { "ir_is_rs_rel" ::= $$false;
                             "ir_msg" ::= #msg;
                             "ir_msg_from" ::= #pmshr!PreMSHR@."r_msg_from";
                             "ir_mshr_id" ::= #pmshr!PreMSHR@."r_id" };
        Call enqIR2LR(#nelt);
        Retv)%kami_action.

      Definition irInvRs: ActionT var Void :=
        (Call pelt <- deqInput();
        LET mf <- #pelt!IRPipe@."ir_msg_from";
        Assert (#mf == {$downIdx, compile_oidx_to_cidx oidx});
        LET msg <- #pelt!IRPipe@."ir_msg";
        Assert (#msg!KMsg@."type" && #msg!KMsg@."id" == $$invRsId);
        Call vmid <- releaseVictim(#msg!KMsg@."addr");
        Call releaseMSHR(#vmid);
        Retv)%kami_action.

      Definition irRsRel: ActionT var Void :=
        (Call rsr <- getRsReady();
        LET msg: Struct KMsg <- STRUCT { "id" ::= $$Default;
                                         "type" ::= $$Default;
                                         "addr" ::= #rsr!RsReady@."r_addr";
                                         "value" ::= $$Default };
        Call infoRq(#rsr!RsReady@."r_addr");
        LET nelt <- STRUCT { "ir_is_rs_rel" ::= $$true;
                             "ir_msg" ::= #msg;
                             "ir_msg_from" ::= $$Default;
                             "ir_mshr_id" ::= #rsr!RsReady@."r_id" };
        Call enqIR2LR(#nelt);
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

      Definition lrRule: ActionT var Void :=
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
           | HUpLockIdxBackI _ => ({$downIdx, _truncate_ (#mshr!MSHR@."m_qidx")})
           | HDownLockIdxBackI _ => (#mshr!MSHR@."m_qidx")
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
           | HUpLockFree => cont
           | HDownLockFree => cont
           | HUpLockMsgId mty mid =>
             (Assert (#mshr!MSHR@."m_status" == mshrValid);
             Assert (#mshr!MSHR@."m_rsb");
             Assert (#mshr!MSHR@."m_msg"!KMsg@."type" == Const _ (ConstBool mty));
             Assert (#mshr!MSHR@."m_msg"!KMsg@."id" == $$%mid%:hcfg_msg_id_sz);
             cont)
           | HUpLockMsg =>
             (Assert (#mshr!MSHR@."m_status" == mshrValid); Assert (#mshr!MSHR@."m_rsb"); cont)
           | HUpLockIdxBack =>
             (Assert (#mshr!MSHR@."m_status" == mshrValid); Assert (#mshr!MSHR@."m_rsb"); cont)
           | HUpLockBackNone =>
             (Assert (#mshr!MSHR@."m_status" == mshrValid); Assert (!(#mshr!MSHR@."m_rsb")); cont)
           | HDownLockMsgId mty mid =>
             (Assert (#mshr!MSHR@."m_status" == mshrValid);
             Assert (#mshr!MSHR@."m_rsb");
             Assert (#mshr!MSHR@."m_msg"!KMsg@."type" == Const _ (ConstBool mty));
             Assert (#mshr!MSHR@."m_msg"!KMsg@."id" == $$%mid%:hcfg_msg_id_sz);
             cont)
           | HDownLockMsg =>
             (Assert (#mshr!MSHR@."m_status" == mshrValid); Assert (#mshr!MSHR@."m_rsb"); cont)
           | HDownLockIdxBack =>
             (Assert (#mshr!MSHR@."m_status" == mshrValid); Assert (#mshr!MSHR@."m_rsb"); cont)
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

        Definition compile_rule_msg_from (mf: HMsgFrom)
                   (vmf: var KQIdx) (cont: ActionT var Void): ActionT var Void :=
          (match mf with
           | HMsgFromNil => cont
           | HMsgFromParent pmidx =>
             (Assert (#vmf == compile_midx_to_qidx pmidx); cont)
           | HMsgFromChild cmidx =>
             (Assert (#vmf == compile_midx_to_qidx cmidx); cont)
           | HMsgFromExt emidx =>
             (Assert (#vmf == compile_midx_to_qidx emidx); cont)
           | HMsgFromUpLock =>
             (Assert (#vmf == {$downIdx, compile_oidx_to_cidx oidx}); cont)
           | HMsgFromDownLock cidx =>
             (Assert (#vmf == {$rsUpIdx, compile_oidx_to_cidx cidx}); cont)
           end)%kami_action.

        Definition compile_bval {hbt} (hv: hbval hbt)
          : Expr var (SyntaxKind (kind_of_hbtype hbt)) :=
          (match hv in hbval hbt' return Expr var (SyntaxKind (kind_of_hbtype hbt')) with
           | HGetFirstMsg => #msgIn
           | HGetUpLockMsg => (#mshr!MSHR@."m_msg")
           | HGetDownLockMsg => (#mshr!MSHR@."m_msg")
           | HGetUpLockIdxBack => {$downIdx, _truncate_ (#mshr!MSHR@."m_qidx")}
           | HGetDownLockIdxBack => (#mshr!MSHR@."m_qidx")
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
        Local Notation releaseMSHR := (releaseMSHR oidx mshrNumPRqs mshrNumCRqs).
        Local Notation transferUpDown := (transferUpDown oidx mshrNumPRqs mshrNumCRqs).
        Local Notation addRs := (addRs oidx).

        Local Notation getULCount := (getULCount oidx mshrNumPRqs mshrNumCRqs).
        Local Notation getVictimCount := (getVictimCount oidx predNumVictims).

        Fixpoint compile_ORq_trs (horq: HORq (hvar_of var))
                 (cont: ActionT var Void): ActionT var Void :=
          (match horq with
           | HORqI _ => cont
           | HUpdUpLock rq _ rsb =>
             (** TODO: is here the best spot to check the counts? *)
             (Call ulCnt <- getULCount();
             Call vcCnt <- getVictimCount();
             Assert (#ulCnt < _zeroExtend_ (UniBit (Neg _) #vcCnt));
             Call registerUL(STRUCT { "r_id" ::= #mshrId;
                                      "r_ul_rsb" ::= $$true;
                                      "r_ul_rsbTo" ::= _truncate_ (compile_exp rsb) }); cont)
           | HUpdUpLockS _ =>
             (Call registerUL(STRUCT { "r_id" ::= #mshrId;
                                       "r_ul_rsb" ::= $$false;
                                       "r_ul_rsbTo" ::= $$Default }); cont)
           | HRelUpLock _ => (Call releaseMSHR(#mshrId); cont)
           | HUpdDownLock rq rssf rsb =>
             (Call registerDL(STRUCT { "r_id" ::= #mshrId;
                                       "r_dl_rss_from" ::= compile_exp rssf;
                                       "r_dl_rsb" ::= $$true;
                                       "r_dl_rsbTo" ::= compile_exp rsb }); cont)
           | HUpdDownLockS rssf =>
             (** NOTE: silent down-requests;
              * not used in non-inclusive cache-coherence protocols *)
             (Call registerDL (STRUCT { "r_id" ::= #mshrId;
                                        "r_dl_rss_from" ::= compile_exp rssf;
                                        "r_dl_rsb" ::= $$false;
                                        "r_dl_rsbTo" ::= $$Default });
             cont)
           | HRelDownLock _ => (Call releaseMSHR(#mshrId); cont)
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

      Definition compile_MonadT_ret_ord
                 (ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
                 (cont: ActionT var Void)
                 (host: HOState (hvar_of var))
                 (horq: HORq (hvar_of var))
                 (hmsgs: HMsgsOut (hvar_of var)): ActionT var Void :=
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
             let nostVars := compile_value_read_to_ostVars _ ostVars rvalue in
             compile_ORq_trs nostVars horq (compile_MsgsOut_trs nostVars hmsgs cont)))%kami_action.

      Definition compile_MonadT_ret_nowrite
                 (ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
                 (cont: ActionT var Void)
                 (horq: HORq (hvar_of var))
                 (hmsgs: HMsgsOut (hvar_of var)): ActionT var Void :=
        (compile_ORq_trs ostVars horq (compile_MsgsOut_trs ostVars hmsgs cont))%kami_action.

      Fixpoint compile_MonadT_trs
               (ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
               (hm: HMonadT (hvar_of var))
               (retCont: HOState (hvar_of var) ->
                         HORq (hvar_of var) ->
                         HMsgsOut (hvar_of var) ->
                         ActionT var Void): ActionT var Void :=
        match hm with
        | HBind hv mcont =>
          Let_ (compile_bval hv)
               (fun x: var (kind_of_hbtype _) => compile_MonadT_trs ostVars (mcont x) retCont)
        | HRet host horq hmsgs => retCont host horq hmsgs
        end.

      Definition compile_rule_trs
                 (ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
                 (trs: HOTrs)
                 (retCont: HOState (hvar_of var) ->
                           HORq (hvar_of var) ->
                           HMsgsOut (hvar_of var) ->
                           ActionT var Void): ActionT var Void :=
        match trs with
        | HTrsMTrs (HMTrs mn) => compile_MonadT_trs ostVars (mn (hvar_of var)) retCont
        end.

      Definition compile_rule_trs_ord
                 (ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
                 (trs: HOTrs) (cont: ActionT var Void): ActionT var Void :=
        compile_rule_trs ostVars trs (compile_MonadT_ret_ord ostVars cont).

      Definition compile_rule_trs_nowrite
                 (ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
                 (trs: HOTrs) (cont: ActionT var Void): ActionT var Void :=
        compile_rule_trs
          ostVars trs
          (fun _ horq hmsgs => compile_MonadT_ret_nowrite ostVars cont horq hmsgs).

    End CompileExec.

    Variables deqLR2EXN: string.

    Section ExecStage.

      (** A static checker whether the rule is for eviction requests *)
      Definition check_rule_rq_prec_rqrs (rrp: HOPrecR): bool :=
        match rrp with
        | HRqAccepting => true
        | _ => false
        end.

      Definition hvarU: htype -> Type := fun _ => unit.
      Fixpoint check_rule_rq_prec (rp: HOPrecT hvarU): bool :=
        match rp with
        | HOPrecAnd prec1 prec2 => check_rule_rq_prec prec1 || check_rule_rq_prec prec1
        | HOPrecRqRs _ rrprec => check_rule_rq_prec_rqrs rrprec
        | HOPrecProp _ => false
        end.

      Definition check_rule_msg_from_nil (mf: HMsgFrom): bool :=
        match mf with
        | HMsgFromNil => true
        | _ => false
        end.

      Definition deqLR2EX := MethodSig deqLR2EXN(): LRPipeK.

      Local Notation valueRsLineRq :=
        (valueRsLineRq oidx infoK KValue hcfg_addr_sz lgWay edirLgWay).
      Local Notation getMSHR := (getMSHR oidx mshrNumPRqs mshrNumCRqs).
      Local Notation Victim := (Victim infoK KValue hcfg_addr_sz mshrSlotSz).
      Local Notation getVictim := (getVictim oidx infoK KValue hcfg_addr_sz mshrSlotSz).
      Local Notation setVictimRq := (setVictimRq oidx hcfg_addr_sz mshrSlotSz).
      Local Notation getULImm := (getULImm oidx mshrNumPRqs mshrNumCRqs).

      Variables (rule: {sr: Hemiola.Syntax.Rule & HRule sr}).
      Let hr := projT2 rule.

      Local Notation "v <- f ; cont" :=
        (f (fun v => cont)) (at level 12, right associativity, only parsing): kami_action_scope.
      Local Notation ": f ; cont" :=
        (f cont) (at level 12, right associativity, only parsing): kami_action_scope.

      Definition execPP: ActionT var Void :=
        (Call lr <- deqLR2EX();
        LET irpp <- #lr!LRPipe@."lr_ir_pp";
        LET mf <- #irpp!IRPipe@."ir_msg_from";
        LET msgIn <- #irpp!IRPipe@."ir_msg";
        LET mshrId <- #irpp!IRPipe@."ir_mshr_id";
        LET rsRel <- #irpp!IRPipe@."ir_is_rs_rel";
        Assert !#rsRel;
        LET pir <- #lr!LRPipe@."lr_ir";
        LET pinfo <- #pir!InfoRead@."info";
        Call mshr <- getMSHR(#mshrId);
        ostVars <- compile_info_to_ostVars pinfo;
        :compile_rule_msg_from (hrule_msg_from hr) mf;
        :compile_rule_prec
           msgIn mshr ostVars (hrule_precond hr (hvar_of var));
        :compile_rule_trs_ord msgIn mshrId mshr pir ostVars (hrule_trs hr);
        Retv)%kami_action.

      Definition execRsRel: ActionT var Void :=
        (Call lr <- deqLR2EX();
        LET irpp <- #lr!LRPipe@."lr_ir_pp";
        LET mf <- #irpp!IRPipe@."ir_msg_from";
        LET msgIn <- #irpp!IRPipe@."ir_msg";
        LET mshrId <- #irpp!IRPipe@."ir_mshr_id";
        LET rsRel <- #irpp!IRPipe@."ir_is_rs_rel";
        Assert #rsRel;
        LET pir <- #lr!LRPipe@."lr_ir";
        LET pinfo <- #pir!InfoRead@."info";
        Call mshr <- getMSHR(#mshrId);
        ostVars <- compile_info_to_ostVars pinfo;
        :compile_rule_msg_from (hrule_msg_from hr) mf;
        :compile_rule_prec
           msgIn mshr ostVars (hrule_precond hr (hvar_of var));
        :compile_rule_trs_ord msgIn mshrId mshr pir ostVars (hrule_trs hr);
        Retv)%kami_action.

      Definition execInvRq: ActionT var Void :=
        (Call victim <- getVictim();
        LET paddr <- #victim!Victim@."victim_addr";
        LET pinfo <- #victim!Victim@."victim_info";
        LET pvalue <- #victim!Victim@."victim_value";
        LET msg <- STRUCT { "id" ::= $$Default;
                            "type" ::= $$MRq;
                            "addr" ::= #paddr;
                            "value" ::= $$Default };
        Call mid <- getULImm(#msg);
        Call setVictimRq(STRUCT { "victim_addr" ::= #paddr; "victim_req" ::= #mid });
        LET mshr <- STRUCT { "m_status" ::= mshrValid;
                             "m_next" ::= $$Default;
                             "m_is_ul" ::= $$true;
                             "m_msg" ::= #msg;
                             "m_qidx" ::= $$Default;
                             "m_rsb" ::= $$false;
                             "m_dl_rss_from" ::= $$Default;
                             "m_dl_rss_recv" ::= $$Default;
                             "m_dl_rss" ::= $$Default };
        ostVars <- compile_info_to_ostVars pinfo;
        let nostVars := compile_value_read_to_ostVars _ ostVars pvalue in
        :compile_rule_prec
           msg mshr nostVars (hrule_precond hr (hvar_of var));
        :compile_rule_trs_nowrite msg mid mshr nostVars (hrule_trs hr);
        Retv)%kami_action.

    End ExecStage.

  End Pipeline.

  Context `{CompExtExp} `{CompLineRW}.

  Section WithObj.
    Variable (oidx: IdxT).
    Variables (deqInputN enqIR2LRN deqIR2LRN enqLR2EXN deqLR2EXN: string).

    Definition compile_rules_ir: list (Attribute (Action Void)) :=
      {| attrName := "rule_ir_prq_" ++ idx_to_string oidx;
         attrType := fun var => irPRq oidx deqInputN enqIR2LRN |}
        :: {| attrName := "rule_ir_prs_" ++ idx_to_string oidx;
              attrType := fun var => irPRs oidx deqInputN enqIR2LRN |}
        :: {| attrName := "rule_ir_crq_" ++ idx_to_string oidx;
              attrType := fun var => irCRq oidx deqInputN enqIR2LRN |}
        :: {| attrName := "rule_ir_crs_" ++ idx_to_string oidx;
              attrType := fun var => irCRs oidx deqInputN |}
        :: {| attrName := "rule_ir_retry_" ++ idx_to_string oidx;
              attrType := fun var => irRetry oidx enqIR2LRN |}
        :: {| attrName := "rule_ir_invrs_" ++ idx_to_string oidx;
              attrType := fun var => irInvRs oidx deqInputN |}
        :: {| attrName := "rule_ir_rsrel_" ++ idx_to_string oidx;
              attrType := fun var => irRsRel oidx enqIR2LRN |}
        :: nil.

    Definition compile_rules_lr: list (Attribute (Action Void)) :=
      {| attrName := "rule_lr_" ++ idx_to_string oidx;
         attrType := fun var => lrRule oidx deqIR2LRN enqLR2EXN |}
        :: nil.

    Definition execRuleNameBase: string := "rule_exec".
    Definition execRuleNameI (ridx: IdxT) :=
      (execRuleNameBase
         ++ "_" ++ idx_to_string oidx
         ++ "_" ++ idx_to_string ridx)%string.

    Definition compile_execPP
               (rule: {sr: Hemiola.Syntax.Rule & HRule sr}): Attribute (Action Void) :=
      let r := projT1 rule in
      {| attrName := execRuleNameI (rule_idx r);
         attrType := fun _ => execPP oidx deqLR2EXN rule |}.

    Definition compile_execRsRel
               (rule: {sr: Hemiola.Syntax.Rule & HRule sr}): Attribute (Action Void) :=
      let r := projT1 rule in
      {| attrName := execRuleNameI (rule_idx r);
         attrType := fun _ => execRsRel oidx deqLR2EXN rule |}.

    Definition compile_execInvRq
               (rule: {sr: Hemiola.Syntax.Rule & HRule sr}): Attribute (Action Void) :=
      let r := projT1 rule in
      {| attrName := execRuleNameI (rule_idx r);
         attrType := fun _ => execInvRq oidx rule |}.

    Definition compile_rule_exec
               (rule: {sr: Hemiola.Syntax.Rule & HRule sr}): Attribute (Action Void) :=
      let hr := projT2 rule in
      let isRq := check_rule_rq_prec (hrule_precond hr _) in
      let mfNil := check_rule_msg_from_nil (hrule_msg_from hr) in
      if mfNil
      then (if isRq then compile_execInvRq rule else compile_execRsRel rule)
      else (compile_execPP rule).

    Definition compile_rules_exec (rules: list {sr: Hemiola.Syntax.Rule & HRule sr}):
      list (Attribute (Action Void)) :=
      map compile_rule_exec rules.

    Definition compile_rules_pipeline (rules: list {sr: Hemiola.Syntax.Rule & HRule sr}):
      list (Attribute (Action Void)) :=
      compile_rules_ir ++ compile_rules_lr ++ compile_rules_exec rules.

  End WithObj.

  Definition compile_OState_init (oidx: IdxT): list RegInitT := nil.

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

  Section Inputs.
    Variable oidx: IdxT.

    Definition ppCRqInputFifoN: string := ("fifoCRqInput" ++ idx_to_string oidx).
    Definition enqCRqInputN := ppCRqInputFifoN -- enqN.
    Definition deqCRqInputN := ppCRqInputFifoN -- deqN.

    Definition ppCRsInputFifoN: string := ("fifoCRsInput" ++ idx_to_string oidx).
    Definition enqCRsInputN := ppCRsInputFifoN -- enqN.
    Definition deqCRsInputN := ppCRsInputFifoN -- deqN.

    Definition ppInputFifoN: string := ("fifoInput" ++ idx_to_string oidx).
    Definition enqInputN := ppInputFifoN -- enqN.
    Definition deqInputN := ppInputFifoN -- deqN.

    Definition build_inputs_l1: Modules :=
      inputAcceptor2 oidx enqInputN.

    Definition build_inputs_li_4: Modules :=
      ((cRqAcceptor4 oidx enqCRqInputN (oidx~>0) (oidx~>1) (oidx~>2) (oidx~>3))
         ++ (cRsAcceptor4 oidx enqCRsInputN (oidx~>0) (oidx~>1) (oidx~>2) (oidx~>3))
         ++ (inputAcceptor3 oidx deqCRqInputN deqCRsInputN enqInputN))%kami.

  End Inputs.

  Section Outputs.
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

    Definition build_outputs_l1_async: Modules :=
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

    Definition build_outputs_l1: Modules :=
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

    Definition build_outputs_li_async: Modules :=
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

    Definition build_outputs_li: Modules :=
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

    Definition build_outputs_mem: Modules :=
      MODULE {
        Method (makeEnqFn oidx)(e: MakeEnqK): Void :=
          LET msg <- #e!MakeEnq@."enq_msg";
          Call (enqTo (downTo (oidx~>0)))(#msg);
          Retv
      }.

  End Outputs.

  Let ppIR2LRN (oidx: IdxT): string := ("fifoIL" ++ idx_to_string oidx).
  Let enqIR2LRN (oidx: IdxT) := (ppIR2LRN oidx) -- enqN.
  Let deqIR2LRN (oidx: IdxT) := (ppIR2LRN oidx) -- deqN.

  Let ppLR2EXN (oidx: IdxT): string := ("fifoIL" ++ idx_to_string oidx).
  Let enqLR2EXN (oidx: IdxT) := (ppLR2EXN oidx) -- enqN.
  Let deqLR2EXN (oidx: IdxT) := (ppLR2EXN oidx) -- deqN.

  Definition build_pipeline (obj: {sobj: Hemiola.Syntax.Object & HObject sobj}): Modules :=
    let oidx := obj_idx (projT1 obj) in
    let cregs := compile_OState_init oidx in
    let crules := compile_rules_pipeline
                    oidx (deqInputN oidx) (enqIR2LRN oidx)
                    (deqIR2LRN oidx) (enqLR2EXN oidx) (deqLR2EXN oidx)
                    (hobj_rules (projT2 obj)) in
    Mod cregs crules nil.

  Definition build_controller_l1
             (obj: {sobj: Hemiola.Syntax.Object & HObject sobj}): Modules :=
    let oidx := obj_idx (projT1 obj) in
    ((build_inputs_l1 oidx ++ build_pipeline obj ++ build_outputs_l1 oidx)
       ++ build_int_fifos oidx ++ build_ext_fifos oidx)%kami.

  Definition build_controller_li_4
             (obj: {sobj: Hemiola.Syntax.Object & HObject sobj}): Modules :=
    let oidx := obj_idx (projT1 obj) in
    ((build_inputs_li_4 oidx ++ build_pipeline obj ++ build_outputs_li oidx)
       ++ build_int_fifos oidx)%kami.

  Definition build_controller_mem
             (obj: {sobj: Hemiola.Syntax.Object & HObject sobj}): Modules :=
    let oidx := obj_idx (projT1 obj) in
    (build_pipeline obj ++ build_outputs_mem oidx)%kami.

End Compile.
