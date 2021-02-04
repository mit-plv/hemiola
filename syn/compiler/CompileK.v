Require Import Numbers.DecimalString.

Require Import Hemiola.Common Hemiola.Index Hemiola.Syntax.
Require Import Hemiola.Ex.TopoTemplate.

Require Import Compiler.HemiolaDeep. (* source *)
Require Import Kami.Lib.Struct Kami Kami.Ex.Fifo Kami.PrimFifo Kami.PrimBram. (* target *)
Require Export Compiler.Components.

Set Implicit Arguments.

Import MonadNotations.

Definition nfifo (fifoName: string) (dType: Kind) (sz: nat) :=
  fifo primNormalFifoName fifoName dType sz.
Definition ppfifo (fifoName: string) (dType: Kind) :=
  fifo primPipelineFifoName fifoName dType 0.

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

  (** Victims *)
  Variable predNumVictims: nat.
  Let victimIdxSz := S (Nat.log2 predNumVictims).
  Let MviK := Maybe (Bit victimIdxSz).

  Definition kind_of_hbtype (hbt: hbtype): Kind :=
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

  Section PipelineStages.
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

    Definition Input :=
      STRUCT { "in_msg" :: Struct KMsg; "in_msg_from" :: KQIdx }.
    Let InputK := Struct Input.

    Variables enqCRqN enqCRsN: string.

    Definition cRqAcceptor2 (cidx0 cidx1: IdxT): Modules :=
      acceptor2
        ("cRq2_" ++ idx_to_string oidx) (eltT:= InputK)
        (fun _ msg => STRUCT { "in_msg" ::= #msg; "in_msg_from" ::= {$rqUpIdx, $0} })%kami_expr
        (fun _ msg => STRUCT { "in_msg" ::= #msg; "in_msg_from" ::= {$rqUpIdx, $1} })%kami_expr
        (deqFn (rqUpFrom cidx0)) (deqFn (rqUpFrom cidx1)) enqCRqN.

    Definition cRsAcceptor2 (cidx0 cidx1: IdxT): Modules :=
      acceptor2
        ("cRs2_" ++ idx_to_string oidx) (eltT:= InputK)
        (fun _ msg => STRUCT { "in_msg" ::= #msg; "in_msg_from" ::= {$rsUpIdx, $0} })%kami_expr
        (fun _ msg => STRUCT { "in_msg" ::= #msg; "in_msg_from" ::= {$rsUpIdx, $1} })%kami_expr
        (deqFn (rsUpFrom cidx0)) (deqFn (rsUpFrom cidx1)) enqCRsN.

    Definition cRqAcceptor4 (cidx0 cidx1 cidx2 cidx3: IdxT): Modules :=
      acceptor4
        ("cRq4_" ++ idx_to_string oidx) (eltT:= InputK)
        (fun _ msg => STRUCT { "in_msg" ::= #msg; "in_msg_from" ::= {$rqUpIdx, $0} })%kami_expr
        (fun _ msg => STRUCT { "in_msg" ::= #msg; "in_msg_from" ::= {$rqUpIdx, $1} })%kami_expr
        (fun _ msg => STRUCT { "in_msg" ::= #msg; "in_msg_from" ::= {$rqUpIdx, $2} })%kami_expr
        (fun _ msg => STRUCT { "in_msg" ::= #msg; "in_msg_from" ::= {$rqUpIdx, $3} })%kami_expr
        (deqFn (rqUpFrom cidx0)) (deqFn (rqUpFrom cidx1))
        (deqFn (rqUpFrom cidx2)) (deqFn (rqUpFrom cidx3)) enqCRqN.

    Definition cRsAcceptor4 (cidx0 cidx1 cidx2 cidx3: IdxT): Modules :=
      acceptor4
        ("cRs4_" ++ idx_to_string oidx) (eltT:= InputK)
        (fun _ msg => STRUCT { "in_msg" ::= #msg; "in_msg_from" ::= {$rsUpIdx, $0} })%kami_expr
        (fun _ msg => STRUCT { "in_msg" ::= #msg; "in_msg_from" ::= {$rsUpIdx, $1} })%kami_expr
        (fun _ msg => STRUCT { "in_msg" ::= #msg; "in_msg_from" ::= {$rsUpIdx, $2} })%kami_expr
        (fun _ msg => STRUCT { "in_msg" ::= #msg; "in_msg_from" ::= {$rsUpIdx, $3} })%kami_expr
        (deqFn (rsUpFrom cidx0)) (deqFn (rsUpFrom cidx1))
        (deqFn (rsUpFrom cidx2)) (deqFn (rsUpFrom cidx3)) enqCRsN.

    (*! Pipeline Stages *)

    Variables deqInputN enqIN2IRN: string.

    Definition IRElt :=
      STRUCT { "ir_is_rs_rel" :: Bool;
               "ir_msg" :: Struct KMsg;
               "ir_msg_from" :: KQIdx;
               "ir_mshr_id" :: MshrId;
               "ir_by_victim" :: MviK }.
    Let IREltK := Struct IRElt.

    Section InputStage.
      Definition deqInput := MethodSig deqInputN(): InputK.
      Definition enqIN2IR := MethodSig enqIN2IRN(IREltK): Void.

      Local Notation findVictim := (findVictim oidx hcfg_addr_sz predNumVictims).
      Local Notation releaseVictim := (releaseVictim oidx hcfg_addr_sz).
      Local Notation hasVictim := (hasVictim oidx).

      Local Notation getPRqSlot := (getPRqSlot oidx mshrNumPRqs mshrNumCRqs).
      Local Notation getCRqSlot := (getCRqSlot oidx mshrNumPRqs mshrNumCRqs).
      Local Notation GetSlot := (GetSlot mshrNumPRqs mshrNumCRqs).
      Let GetSlotK := Struct GetSlot.
      Local Notation addRs := (addRs oidx).
      Local Notation getULReady := (getULReady oidx mshrNumPRqs mshrNumCRqs).
      Local Notation DLReady := (DLReady mshrNumPRqs mshrNumCRqs).
      Let DLReadyK := Struct DLReady.
      Local Notation getDLReady := (getDLReady oidx mshrNumPRqs mshrNumCRqs).
      Local Notation startRelease := (startRelease oidx mshrNumPRqs mshrNumCRqs).
      Local Notation releaseMSHR := (releaseMSHR oidx mshrNumPRqs mshrNumCRqs).
      Local Notation getWait := (getWait oidx mshrNumPRqs mshrNumCRqs).
      Local Notation PreMSHR := (PreMSHR mshrNumPRqs mshrNumCRqs).
      Let PreMSHRK := Struct PreMSHR.

      Definition inputPRq: ActionT var Void :=
        (Call pelt <- deqInput();
        LET mf <- #pelt!Input@."in_msg_from";
        Assert (#mf == {$downIdx, compile_oidx_to_cidx oidx});
        LET msg <- #pelt!Input@."in_msg";
        Assert !(#msg!KMsg@."type");
        Call gs <- getPRqSlot(STRUCT { "r_id" ::= $$Default;
                                       "r_msg" ::= #msg;
                                       "r_msg_from" ::= #pelt!Input@."in_msg_from" });
        Assert (#gs!GetSlot@."s_has_slot");
        If !(#gs!GetSlot@."s_conflict")
         then (Call mv <- findVictim(#msg!KMsg@."addr");
              LET nelt <- STRUCT { "ir_is_rs_rel" ::= $$false;
                                   "ir_msg" ::= #pelt!Input@."in_msg";
                                   "ir_msg_from" ::= #mf;
                                   "ir_mshr_id" ::= #gs!GetSlot@."s_id";
                                   "ir_by_victim" ::= #mv };
              Call enqIN2IR(#nelt);
              Retv);
         Retv)%kami_action.

      Definition inputPRs: ActionT var Void :=
        (Call pelt <- deqInput();
        LET mf <- #pelt!Input@."in_msg_from";
        Assert (#mf == {$downIdx, compile_oidx_to_cidx oidx});
        LET msg <- #pelt!Input@."in_msg";
        Assert (#msg!KMsg@."type" && #msg!KMsg@."id" != $$invRsId);
        Call mid <- getULReady(#msg!KMsg@."addr");
        Call startRelease(#mid);
        Call mv <- findVictim(#msg!KMsg@."addr");
        LET nelt <- STRUCT { "ir_is_rs_rel" ::= $$false;
                             "ir_msg" ::= #pelt!Input@."in_msg";
                             "ir_msg_from" ::= #mf;
                             "ir_mshr_id" ::= #mid;
                             "ir_by_victim" ::= #mv };
        Call enqIN2IR(#nelt);
        Retv)%kami_action.

      Definition inputCRq: ActionT var Void :=
        (Call pelt <- deqInput();
        LET mf <- #pelt!Input@."in_msg_from";
        Assert (_truncLsb_ #mf == $rqUpIdx);
        LET msg <- #pelt!Input@."in_msg";
        Assert !(#msg!KMsg@."type");
        (** NOTE: the [hasVictim] check is necessary to avoid deadlocks between
         * victim lines and uplocks. It is tricky to have the assertion in this MSHRRq
         * transition, but [HUpdUpLock] is the only and exact transition that
         * requires this check. *)
        Call hasVictim <- hasVictim();
        Assert !#hasVictim;
        Call gs <- getCRqSlot(STRUCT { "r_id" ::= $$Default;
                                       "r_msg" ::= #msg;
                                       "r_msg_from" ::= #mf });
        Assert (#gs!GetSlot@."s_has_slot");
        If !(#gs!GetSlot@."s_conflict")
         then (Call mv <- findVictim(#msg!KMsg@."addr");
              LET nelt <- STRUCT { "ir_is_rs_rel" ::= $$false;
                                   "ir_msg" ::= #pelt!Input@."in_msg";
                                   "ir_msg_from" ::= #mf;
                                   "ir_mshr_id" ::= #gs!GetSlot@."s_id";
                                   "ir_by_victim" ::= #mv };
              Call enqIN2IR(#nelt);
              Retv);
         Retv)%kami_action.

      Definition inputCRs: ActionT var Void :=
        (Call pelt <- deqInput();
        LET mf <- #pelt!Input@."in_msg_from";
        Assert (_truncLsb_ #mf == $rsUpIdx);
        LET msg <- #pelt!Input@."in_msg";
        Assert (#msg!KMsg@."type");
        Call addRs(STRUCT { "r_midx" ::= _truncate_ #mf; "r_msg" ::= #msg });
        Retv)%kami_action.

      Definition inputRetry: ActionT var Void :=
        (Call pmshr <- getWait();
        LET msg <- #pmshr!PreMSHR@."r_msg";
        Call mv <- findVictim(#msg!KMsg@."addr");
        LET nelt <- STRUCT { "ir_is_rs_rel" ::= $$false;
                             "ir_msg" ::= #msg;
                             "ir_msg_from" ::= #pmshr!PreMSHR@."r_msg_from";
                             "ir_mshr_id" ::= #pmshr!PreMSHR@."r_id";
                             "ir_by_victim" ::= #mv };
        Call enqIN2IR(#nelt);
        Retv)%kami_action.

      Definition inputInvRs: ActionT var Void :=
        (Call pelt <- deqInput();
        LET mf <- #pelt!Input@."in_msg_from";
        Assert (#mf == {$downIdx, compile_oidx_to_cidx oidx});
        LET msg <- #pelt!Input@."in_msg";
        Assert (#msg!KMsg@."type" && #msg!KMsg@."id" == $$invRsId);
        Call vmid <- getULReady(#msg!KMsg@."addr");
        Call releaseVictim(#msg!KMsg@."addr");
        Call releaseMSHR(#vmid);
        Retv)%kami_action.

      Definition inputRsRel: ActionT var Void :=
        (Call rsr <- getDLReady();
        Call startRelease(#rsr!DLReady@."r_id");
        LET msg: Struct KMsg <- STRUCT { "id" ::= $$Default;
                                         "type" ::= $$Default;
                                         "addr" ::= #rsr!DLReady@."r_addr";
                                         "value" ::= $$Default };
        LET nelt <- STRUCT { "ir_is_rs_rel" ::= $$true;
                             "ir_msg" ::= #msg;
                             "ir_msg_from" ::= $$Default;
                             "ir_mshr_id" ::= #rsr!DLReady@."r_id";
                             "ir_by_victim" ::= MaybeNone };
        Call enqIN2IR(#nelt);
        Retv)%kami_action.

    End InputStage.

    Variables deqIN2IRN enqIR2LRN: string.

    Section InfoReadStage.

      Definition deqIN2IR := MethodSig deqIN2IRN(): IREltK.
      Definition enqIR2LR := MethodSig enqIR2LRN(IREltK): Void.

      Local Notation infoRq := (infoRq oidx hcfg_addr_sz).

      Definition irCache: ActionT var Void :=
        (Call pelt <- deqIN2IR();
        Assert !(#pelt!IRElt@."ir_by_victim"!(MaybeStr (Bit victimIdxSz))@."valid");
        LET msg <- #pelt!IRElt@."ir_msg";
        Call infoRq(#msg!KMsg@."addr");
        Call enqIR2LR(#pelt);
        Retv)%kami_action.

      Definition irVictims: ActionT var Void :=
        (Call pelt <- deqIN2IR();
        Assert (#pelt!IRElt@."ir_by_victim"!(MaybeStr (Bit victimIdxSz))@."valid");
        Call enqIR2LR(#pelt);
        Retv)%kami_action.

    End InfoReadStage.

    Variables deqIR2LRN enqLR2EXN: string.
    Local Notation InfoRead := (InfoRead infoK indexSz hcfg_addr_sz lgWay edirLgWay).

    Section LineReadStage.

      Definition LRElt :=
        STRUCT { "lr_ir_pp" :: IREltK;
                 "lr_ir" :: Struct InfoRead;
                 "lr_value" :: KValue
               }.
      Definition LREltK := Struct LRElt.

      Definition deqIR2LR := MethodSig deqIR2LRN(): IREltK.
      Definition enqLR2EX := MethodSig enqLR2EXN(LREltK): Void.
      Local Notation infoRsValueRq :=
        (infoRsValueRq oidx infoK indexSz hcfg_addr_sz lgWay edirLgWay).
      Local Notation getVictim :=
        (getVictim oidx hcfg_addr_sz predNumVictims infoK KValue).
      Local Notation Victim := (Victim hcfg_addr_sz infoK KValue).

      Definition lrCache: ActionT var Void :=
        (Call ir <- deqIR2LR();
        Assert !(#ir!IRElt@."ir_by_victim"!(MaybeStr (Bit victimIdxSz))@."valid");
        Call rinfo <- infoRsValueRq(#ir!IRElt@."ir_msg"!KMsg@."addr");
        LET lr <- STRUCT { "lr_ir_pp" ::= #ir;
                           "lr_ir" ::= #rinfo;
                           "lr_value" ::= $$Default };
        Call enqLR2EX(#lr);
        Retv)%kami_action.

      Definition lrVictims: ActionT var Void :=
        (Call ir <- deqIR2LR();
        Assert (#ir!IRElt@."ir_by_victim"!(MaybeStr (Bit victimIdxSz))@."valid");
        LET vidx <- #ir!IRElt@."ir_by_victim"!(MaybeStr (Bit victimIdxSz))@."data";
        Call victim <- getVictim(#vidx);
        LET rinfo <- STRUCT { "info_index" ::= $$Default;
                              "info_hit" ::= $$Default;
                              "info_way" ::= $$Default;
                              "edir_hit" ::= $$Default;
                              "edir_way" ::= $$Default;
                              "edir_slot" ::= $$Default;
                              "info" ::= #victim!Victim@."victim_info";
                              "may_victim" ::= $$Default;
                              "reps" ::= $$Default };
        LET lr <- STRUCT { "lr_ir_pp" ::= #ir;
                           "lr_ir" ::= #rinfo;
                           "lr_value" ::= #victim!Victim@."victim_value" };
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
                (mshrId: var MshrId) (mshr: var (Struct MSHR))
                (rq frs: var (Struct KMsg)).

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
             (Assert (#mshr!MSHR@."m_rsb");
             Assert (#rq!KMsg@."type" == Const _ (ConstBool mty));
             Assert (#rq!KMsg@."id" == $$%mid%:hcfg_msg_id_sz);
             cont)
           | HUpLockMsg => (Assert (#mshr!MSHR@."m_rsb"); cont)
           | HUpLockIdxBack => (Assert (#mshr!MSHR@."m_rsb"); cont)
           | HUpLockBackNone => (Assert (!(#mshr!MSHR@."m_rsb")); cont)
           | HDownLockMsgId mty mid =>
             (Assert (#mshr!MSHR@."m_rsb");
             Assert (#rq!KMsg@."type" == Const _ (ConstBool mty));
             Assert (#rq!KMsg@."id" == $$%mid%:hcfg_msg_id_sz);
             cont)
           | HDownLockMsg => (Assert (#mshr!MSHR@."m_rsb"); cont)
           | HDownLockIdxBack => (Assert (#mshr!MSHR@."m_rsb"); cont)
           | HMsgIdFrom msgId => (Assert (#msgIn!KMsg@."id" == $$%msgId%:hcfg_msg_id_sz); cont)
           | HRssFull _ =>
             (** The below assertion is already checked in [inputRsRel] *)
             (* Assert (#mshr!MSHR@."dl_rss_recv" == #mshr!MSHR@."dl_rss_from");  *)
             cont
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
           | HGetUpLockMsg => #rq
           | HGetDownLockMsg => #rq
           | HGetUpLockIdxBack => {$downIdx, _truncate_ (#mshr!MSHR@."m_qidx")}
           | HGetDownLockIdxBack => (#mshr!MSHR@."m_qidx")
           | HGetDownLockFirstRs =>
             (let fs := bvFirstSet (#mshr!MSHR@."m_dl_rss_from") in
              STRUCT { "cidx" ::= {$rsUpIdx, fs}; "msg" ::= #frs })
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
        Local Notation setVictim :=
          (setVictim oidx predNumVictims infoK KValue).

        Definition compile_OState_request_write
                   (host: HOState (hvar_of var)) (pline: var (LineWriteK infoK))
                   (mvi: var MviK) (victimVal: var KValue)
                   (cont: var KValue -> ActionT var Void): ActionT var Void :=
          match host with
          | HOStateI _ =>
            (If (#mvi!(MaybeStr (Bit victimIdxSz))@."valid") then (Ret #victimVal)
             else (Call val <- valueRsLineRq($$Default); Ret #val)
              as nvalue; cont nvalue)
          | _ =>
            compile_OState_write_fix
              host pline
              (fun nline =>
                 (If (#mvi!(MaybeStr (Bit victimIdxSz))@."valid")
                  then (Call setVictim
                             (STRUCT { "victim_idx" ::= #mvi!(MaybeStr (Bit victimIdxSz))@."data";
                                       "victim_info" ::= #nline!(LineWrite infoK)@."info";
                                       "victim_value" ::=
                                         (** [valueRsLineRq] checks whether to update the value
                                          * by [value_write], but [setVictim] always tries to write
                                          * with [victim_value]. Thus we need to check here whether
                                          * to update the value or not. *)
                                         (IF (#nline!(LineWrite infoK)@."value_write")
                                          then #nline!(LineWrite infoK)@."value"
                                          else #victimVal) });
                       Ret #victimVal)
                  else (Call val <- valueRsLineRq(#nline); Ret #val)
                   as nvalue; cont nvalue))
          end%kami_action.

      End OstVarsNoValue.

      Section OstVarsWithValue.
        Variable ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty).
        Local Notation compile_exp := (compile_exp ostVars).

        Local Notation registerUL := (registerUL oidx mshrNumPRqs mshrNumCRqs).
        Local Notation registerDL := (registerDL oidx mshrNumPRqs mshrNumCRqs).
        Local Notation releaseMSHR := (releaseMSHR oidx mshrNumPRqs mshrNumCRqs).
        Local Notation transferUpDown := (transferUpDown oidx mshrNumPRqs mshrNumCRqs).

        Definition compile_ORq_trs (horq: HORq (hvar_of var))
                   (cont: ActionT var Void): ActionT var Void :=
          (match horq with
           | HORqI _ => cont
           | HUpdUpLock rq _ rsb =>
             (Call registerUL(STRUCT { "r_id" ::= #mshrId;
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
             (** Already handled by the previous pipeline stage; see the [inputRsAcc] rule. *)
             cont
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
                 (mvi: var MviK) (victimVal: var KValue)
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
                                                   "value" ::= $$Default;
                                                   "may_victim" ::= #pir!InfoRead@."may_victim";
                                                   "reps" ::= #pir!InfoRead@."reps" };
        compile_OState_request_write
          ostVars host pline
          mvi victimVal
          (fun rvalue: var KValue =>
             let nostVars := compile_value_read_to_ostVars _ ostVars rvalue in
             compile_ORq_trs nostVars horq (compile_MsgsOut_trs nostVars hmsgs cont)))%kami_action.

      Definition compile_MonadT_ret_invrq
                 (ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
                 (hmsgs: HMsgsOut (hvar_of var))
                 (cont: ActionT var Void): ActionT var Void :=
        (compile_MsgsOut_trs ostVars hmsgs cont)%kami_action.

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
                 (mvi: var MviK) (victimVal: var KValue)
                 (trs: HOTrs) (cont: ActionT var Void): ActionT var Void :=
        compile_rule_trs ostVars trs (compile_MonadT_ret_ord ostVars mvi victimVal cont).

      Definition compile_rule_trs_invrq
                 (ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
                 (trs: HOTrs) (cont: ActionT var Void): ActionT var Void :=
        compile_rule_trs
          ostVars trs
          (fun _ horq hmsgs => compile_MonadT_ret_invrq ostVars hmsgs cont).

    End CompileExec.

    Variables deqLR2EXN: string.

    Section ExecStage.
      Definition hvarU: htype -> Type := fun _ => unit.

      Definition check_rule_rq_prec_rqrs (rrp: HOPrecR): bool :=
        match rrp with
        | HRqAccepting => true
        | _ => false
        end.
      Fixpoint check_rule_rq_prec (rp: HOPrecT hvarU): bool :=
        match rp with
        | HOPrecAnd prec1 prec2 => check_rule_rq_prec prec1 || check_rule_rq_prec prec2
        | HOPrecRqRs _ rrprec => check_rule_rq_prec_rqrs rrprec
        | HOPrecProp _ => false
        end.

      Definition check_rule_rs_prec_rqrs (rrp: HOPrecR): bool :=
        match rrp with
        | HRsAccepting => true
        | _ => false
        end.
      Fixpoint check_rule_rs_prec (rp: HOPrecT hvarU): bool :=
        match rp with
        | HOPrecAnd prec1 prec2 => check_rule_rs_prec prec1 || check_rule_rs_prec prec2
        | HOPrecRqRs _ rrprec => check_rule_rs_prec_rqrs rrprec
        | HOPrecProp _ => false
        end.

      Definition check_rule_rssfull_prec_rqrs (rrp: HOPrecR): bool :=
        match rrp with
        | HRssFull _ => true
        | _ => false
        end.
      Fixpoint check_rule_rssfull_prec (rp: HOPrecT hvarU): bool :=
        match rp with
        | HOPrecAnd prec1 prec2 => check_rule_rssfull_prec prec1 || check_rule_rssfull_prec prec2
        | HOPrecRqRs _ rrprec => check_rule_rssfull_prec_rqrs rrprec
        | HOPrecProp _ => false
        end.

      Definition check_rule_msg_from_nil (mf: HMsgFrom): bool :=
        match mf with
        | HMsgFromNil => true
        | _ => false
        end.

      Definition check_rule_msg_from_child (mf: HMsgFrom): bool :=
        match mf with
        | HMsgFromChild _ => true
        | HMsgFromDownLock _ => true
        | _ => false
        end.

      Definition check_rule_orq_intact_orq (horq: HORq hvarU): bool :=
        match horq with
        | HORqI _ => true
        | _ => false
        end.

      Fixpoint check_rule_orq_intact_monad (hm: HMonadT hvarU): bool :=
        match hm with
        | HBind _ mcont => check_rule_orq_intact_monad (mcont tt)
        | HRet _ horq _ => check_rule_orq_intact_orq horq
        end.

      Definition check_rule_orq_intact (htrs: HOTrs): bool :=
        match htrs with
        | HTrsMTrs (HMTrs mn) => check_rule_orq_intact_monad (mn hvarU)
        end.

      Definition check_rule_msgs_out_nil_out (hmsgs: HMsgsOut hvarU): bool :=
        match hmsgs with
        | HMsgOutNil _ => true
        | _ => false
        end.

      Fixpoint check_rule_msgs_out_nil_monad (hm: HMonadT hvarU): bool :=
        match hm with
        | HBind _ mcont => check_rule_msgs_out_nil_monad (mcont tt)
        | HRet _ _ hmsgs => check_rule_msgs_out_nil_out hmsgs
        end.

      Definition check_rule_msgs_out_nil (htrs: HOTrs): bool :=
        match htrs with
        | HTrsMTrs (HMTrs mn) => check_rule_msgs_out_nil_monad (mn hvarU)
        end.

      Definition deqLR2EX := MethodSig deqLR2EXN(): LREltK.

      Local Notation valueRsLineRq :=
        (valueRsLineRq oidx infoK KValue hcfg_addr_sz lgWay edirLgWay).
      Local Notation getMSHR := (getMSHR oidx mshrNumPRqs mshrNumCRqs).
      Local Notation getMSHRRq := (getMSHRRq oidx mshrNumPRqs mshrNumCRqs).
      Local Notation getMSHRFirstRs := (getMSHRFirstRs oidx mshrNumPRqs mshrNumCRqs).
      Local Notation releaseMSHR := (releaseMSHR oidx mshrNumPRqs mshrNumCRqs).
      Local Notation Victim := (Victim hcfg_addr_sz infoK KValue).
      Local Notation getFirstVictim := (getFirstVictim oidx hcfg_addr_sz infoK KValue).
      Local Notation setVictimRq := (setVictimRq oidx hcfg_addr_sz).
      Local Notation releaseVictim := (releaseVictim oidx hcfg_addr_sz).
      Local Notation canImm := (canImm oidx).
      Local Notation setULImm := (setULImm oidx).

      Variables (rule: {sr: Hemiola.Syntax.Rule & HRule sr}).
      Let hr := projT2 rule.

      Local Notation "v <- f ; cont" :=
        (f (fun v => cont)) (at level 12, right associativity, only parsing): kami_action_scope.
      Local Notation ": f ; cont" :=
        (f cont) (at level 12, right associativity, only parsing): kami_action_scope.

      Definition execPP (isImm: bool): ActionT var Void :=
        (Call lr <- deqLR2EX();
        LET irpp <- #lr!LRElt@."lr_ir_pp";
        LET mf <- #irpp!IRElt@."ir_msg_from";
        LET msgIn <- #irpp!IRElt@."ir_msg";
        LET mshrId <- #irpp!IRElt@."ir_mshr_id";
        LET rsRel <- #irpp!IRElt@."ir_is_rs_rel";
        Assert !#rsRel;
        LET pir <- #lr!LRElt@."lr_ir";
        LET pinfo <- #pir!InfoRead@."info";
        LET mvi <- #irpp!IRElt@."ir_by_victim";
        LET victimVal <- #lr!LRElt@."lr_value";
        Call mshr <- getMSHR(#mshrId);
        Call rq <- getMSHRRq(#mshrId);
        (* [execPP] should not use any response messages during the execution *)
        LET frs <- $$Default;
        ostVars <- compile_info_to_ostVars pinfo;
        :compile_rule_msg_from (hrule_msg_from hr) mf;
        :compile_rule_prec
           msgIn mshr rq ostVars (hrule_precond hr (hvar_of var));
        :compile_rule_trs_ord msgIn mshrId mshr rq frs pir ostVars mvi victimVal (hrule_trs hr);
        (if isImm then (Call releaseMSHR(#mshrId); Retv) else Retv))%kami_action.

      Definition execRsRel: ActionT var Void :=
        (Call lr <- deqLR2EX();
        LET irpp <- #lr!LRElt@."lr_ir_pp";
        LET mf <- #irpp!IRElt@."ir_msg_from";
        LET msgIn <- #irpp!IRElt@."ir_msg";
        LET mshrId <- #irpp!IRElt@."ir_mshr_id";
        LET rsRel <- #irpp!IRElt@."ir_is_rs_rel";
        Assert #rsRel;
        LET pir <- #lr!LRElt@."lr_ir";
        LET pinfo <- #pir!InfoRead@."info";
        LET mvi <- #irpp!IRElt@."ir_by_victim";
        LET victimVal <- #lr!LRElt@."lr_value";
        Call mshr <- getMSHR(#mshrId);
        Call rq <- getMSHRRq(#mshrId);
        Call frs <- getMSHRFirstRs(#mshrId);
        ostVars <- compile_info_to_ostVars pinfo;
        :compile_rule_msg_from (hrule_msg_from hr) mf;
        :compile_rule_prec
           msgIn mshr rq ostVars (hrule_precond hr (hvar_of var));
        :compile_rule_trs_ord msgIn mshrId mshr rq frs pir ostVars mvi victimVal (hrule_trs hr);
        Retv)%kami_action.

      Definition execInvRq (isImm: bool): ActionT var Void :=
        (Call victim <- getFirstVictim();
        LET paddr <- #victim!Victim@."victim_addr";
        LET pinfo <- #victim!Victim@."victim_info";
        LET pvalue <- #victim!Victim@."victim_value";
        LET msg <- STRUCT { "id" ::= $$Default;
                            "type" ::= $$MRq;
                            "addr" ::= #paddr;
                            "value" ::= $$Default };
        LET mshr <- STRUCT { "m_is_ul" ::= $$true;
                             "m_qidx" ::= $$Default;
                             "m_rsb" ::= $$false;
                             "m_dl_rss_from" ::= $$Default;
                             "m_dl_rss_recv" ::= $$Default };
        LET rq <- $$Default;
        LET frs <- $$Default;
        ostVars <- compile_info_to_ostVars pinfo;
        let nostVars := compile_value_read_to_ostVars _ ostVars pvalue in
        :compile_rule_prec
           msg mshr rq nostVars (hrule_precond hr (hvar_of var));
        :compile_rule_trs_invrq msg mshr rq frs nostVars (hrule_trs hr);
        (if isImm
         then (Call canImm(#paddr); Call releaseVictim(#paddr); Retv)
         else (Call setULImm(#msg); Call setVictimRq(#paddr); Retv)))%kami_action.

    End ExecStage.

  End PipelineStages.

  Context `{CompExtExp} `{CompLineRW}.

  Section Pipeline.
    Variables (oidx: IdxT).
    Variables (deqPInputN deqCRqInputN deqCRsInputN
                          enqIN2IRN deqIN2IRN
                          enqIR2LRN deqIR2LRN
                          enqLR2EXN deqLR2EXN: string).

    Let ppIdxN := idx_to_string oidx.

    Definition compile_rules_in_parent: list (Attribute (Action Void)) :=
      {| attrName := "rule_in_prq_" ++ ppIdxN;
         attrType := fun var => inputPRq oidx deqPInputN enqIN2IRN |}
        :: {| attrName := "rule_in_prs_" ++ ppIdxN;
              attrType := fun var => inputPRs oidx deqPInputN enqIN2IRN |}
        :: {| attrName := "rule_in_retry_" ++ ppIdxN;
              attrType := fun var => inputRetry oidx enqIN2IRN |}
        :: {| attrName := "rule_in_invrs_" ++ ppIdxN;
              attrType := fun var => inputInvRs oidx deqPInputN |}
        :: nil.

    Definition compile_rules_in_child_rq: list (Attribute (Action Void)) :=
      {| attrName := "rule_in_crq_" ++ ppIdxN;
         attrType := fun var => inputCRq oidx deqCRqInputN enqIN2IRN |}
        :: nil.

    Definition compile_rules_in_child_rs: list (Attribute (Action Void)) :=
      {| attrName := "rule_in_crs_" ++ ppIdxN;
         attrType := fun var => inputCRs oidx deqCRsInputN |}
        :: {| attrName := "rule_in_rsrel_" ++ ppIdxN;
              attrType := fun var => inputRsRel oidx enqIN2IRN |}
        :: nil.

    Definition compile_rules_ir: list (Attribute (Action Void)) :=
      {| attrName := "rule_ir_cache_" ++ ppIdxN;
         attrType := fun var => irCache oidx deqIN2IRN enqIR2LRN |}
        :: {| attrName := "rule_ir_victims_" ++ ppIdxN;
              attrType := fun var => irVictims deqIN2IRN enqIR2LRN |}
        :: nil.

    Definition compile_rules_lr: list (Attribute (Action Void)) :=
      {| attrName := "rule_lr_cache_" ++ ppIdxN;
         attrType := fun var => lrCache oidx deqIR2LRN enqLR2EXN |}
        :: {| attrName := "rule_lr_victims_" ++ ppIdxN;
              attrType := fun var => lrVictims oidx deqIR2LRN enqLR2EXN |}
        :: nil.

    Definition execRuleNameBase: string := "rule_exec".
    Definition execRuleNameI (ridx: IdxT) :=
      (execRuleNameBase
         ++ "_" ++ idx_to_string oidx
         ++ "_" ++ idx_to_string ridx)%string.

    Definition compile_execPP (isImm: bool)
               (rule: {sr: Hemiola.Syntax.Rule & HRule sr}): Attribute (Action Void) :=
      let r := projT1 rule in
      {| attrName := execRuleNameI (rule_idx r);
         attrType := fun _ => execPP oidx deqLR2EXN rule isImm |}.

    Definition compile_execRsRel
               (rule: {sr: Hemiola.Syntax.Rule & HRule sr}): Attribute (Action Void) :=
      let r := projT1 rule in
      {| attrName := execRuleNameI (rule_idx r);
         attrType := fun _ => execRsRel oidx deqLR2EXN rule |}.

    Definition compile_execInvRq (isImm: bool)
               (rule: {sr: Hemiola.Syntax.Rule & HRule sr}): Attribute (Action Void) :=
      let r := projT1 rule in
      {| attrName := execRuleNameI (rule_idx r);
         attrType := fun _ => execInvRq oidx rule isImm |}.

    Definition compile_rule_exec (rule: {sr: Hemiola.Syntax.Rule & HRule sr}):
      option (Attribute (Action Void)) :=
      let hr := projT2 rule in
      let isRs := check_rule_rs_prec (hrule_precond hr _) in
      let rssFull := check_rule_rssfull_prec (hrule_precond hr _) in
      let mfNil := check_rule_msg_from_nil (hrule_msg_from hr) in
      let mfChild := check_rule_msg_from_child (hrule_msg_from hr) in
      let mtNil := check_rule_msgs_out_nil (hrule_trs hr) in
      let isImm := check_rule_orq_intact (hrule_trs hr) in
      if rssFull then Some (compile_execRsRel rule)
      else if mfNil then Some (compile_execInvRq isImm rule)
           else if (isRs && mfChild)
                then None (* Child-response rules are already defined in [inputRsAcc] *)
                else if (isRs && mtNil)
                     then None (* Invalidation-response rules are already defined in [inputInvRs]. *)
                     else Some (compile_execPP isImm rule).

    Definition compile_rules_exec (rules: list {sr: Hemiola.Syntax.Rule & HRule sr}):
      list (Attribute (Action Void)) :=
      ListSupport.oll (map compile_rule_exec rules).

    Definition compile_rules_pipeline_li: list (Attribute (Action Void)) :=
      compile_rules_in_parent
        ++ compile_rules_in_child_rq
        ++ compile_rules_in_child_rs
        ++ compile_rules_ir
        ++ compile_rules_lr.

    Definition compile_rules_pipeline_l1: list (Attribute (Action Void)) :=
      compile_rules_in_parent
        ++ compile_rules_in_child_rq
        ++ compile_rules_ir
        ++ compile_rules_lr.

  End Pipeline.

  Definition compile_OState_init (oidx: IdxT): list RegInitT := nil.

  Section DebugFifos.
    Let cntSz := 18.

    Definition msgDisps {ty} (msg: Expr ty (SyntaxKind (Struct KMsg))): list (Disp ty) :=
      (DispBit (0, Hex) (msg!KMsg@."id")%kami_expr)
        :: (DispBool (0, Binary) (msg!KMsg@."type")%kami_expr)
        :: (DispBit (0, Hex) (msg!KMsg@."addr")%kami_expr)
        :: nil.

    Definition dMsgFifo (fifoName: string) :=
      debugFifoN (dType:= Struct KMsg) fifoName 1 cntSz
                 ("-- MSG " ++ fifoName ++ ":")%string
                 (fun _ elt => msgDisps (#elt)%kami_expr).

    Definition dInputFifo (fifoName: string) :=
      debugFifoN (dType:= Struct Input) fifoName 2 cntSz
                 ("-- INPUT " ++ fifoName ++ ":")%string
                 (fun _ elt =>
                    (DispBit (0, Hex) (#elt!Input@."in_msg_from")%kami_expr)
                      :: (msgDisps (#elt!Input@."in_msg")%kami_expr)).

    Definition irDisps {ty} (elt: Expr ty (SyntaxKind (Struct IRElt))): list (Disp ty) :=
      (DispBool (0, Binary) (elt!IRElt@."ir_is_rs_rel")%kami_expr)
        :: (msgDisps (elt!IRElt@."ir_msg")%kami_expr)
        ++ (DispBit (0, Hex) (elt!IRElt@."ir_msg_from")%kami_expr)
        :: (DispBit (0, Hex) (elt!IRElt@."ir_mshr_id")%kami_expr)
        :: (DispBool (0, Binary)
                     (elt!IRElt@."ir_by_victim"
                                   !(MaybeStr (Bit victimIdxSz))@."valid")%kami_expr)
        :: (DispBit (0, Hex)
                    (elt!IRElt@."ir_by_victim"
                                  !(MaybeStr (Bit victimIdxSz))@."data")%kami_expr)
        :: nil.

    Definition dIRFifo (fifoName: string) :=
      debugFifo (dType:= Struct IRElt) fifoName cntSz
                ("-- IR " ++ fifoName ++ ":")%string
                (fun _ elt => irDisps (#elt)%kami_expr).

    Local Notation InfoRead :=
      (InfoRead infoK indexSz hcfg_addr_sz lgWay edirLgWay).
    Definition infoReadDisps {ty}
               (ir: Expr ty (SyntaxKind (Struct InfoRead))): list (Disp ty) :=
      (DispBit (0, Hex) (ir!InfoRead@."info_index")%kami_expr)
        :: (DispBool (0, Binary) (ir!InfoRead@."info_hit")%kami_expr)
        :: (DispBit (0, Hex) (ir!InfoRead@."info_way")%kami_expr)
        :: (DispBool (0, Binary) (ir!InfoRead@."edir_hit")%kami_expr)
        :: (DispBit (0, Hex) (ir!InfoRead@."edir_way")%kami_expr)
        :: (DispBool (0, Binary)
                     (ir!InfoRead@."edir_slot"
                                     !(MaybeStr (Bit edirLgWay))@."valid")%kami_expr)
        :: (DispBit (0, Hex)
                    (ir!InfoRead@."edir_slot"
                                    !(MaybeStr (Bit edirLgWay))@."data")%kami_expr)
        :: nil.

    Definition dLRFifo (fifoName: string) :=
      debugFifo (dType:= Struct LRElt) fifoName cntSz
                ("-- LR " ++ fifoName ++ ":")%string
                (fun _ elt =>
                   (irDisps (#elt!LRElt@."lr_ir_pp")%kami_expr)
                     ++ (infoReadDisps (#elt!LRElt@."lr_ir")%kami_expr)).

  End DebugFifos.

  (* Let msgFifo (fifoName: string) := dMsgFifo fifoName. *)
  Let msgFifo (fifoName: string) := nfifo fifoName (Struct KMsg) 1.

  Definition build_int_fifos (oidx: IdxT): Modules :=
    ((msgFifo (fifoBaseName ++ idx_to_string (rqUpFrom oidx)))
       ++ (msgFifo (fifoBaseName ++ idx_to_string (rsUpFrom oidx)))
       ++ (msgFifo (fifoBaseName ++ idx_to_string (downTo oidx)))
    )%kami.

  Definition build_ext_fifos (oidx: IdxT): Modules :=
    ((msgFifo (fifoBaseName ++ idx_to_string (rqUpFrom (l1ExtOf oidx))))
       ++ (msgFifo (fifoBaseName ++ idx_to_string (downTo (l1ExtOf oidx))))
    )%kami.

  Section Inputs.
    Variable oidx: IdxT.

    Definition ppPInputFifoN: string := ("fifoPInput_" ++ idx_to_string oidx).
    Definition enqPInputN := ppPInputFifoN -- enqN.
    Definition deqPInputN := ppPInputFifoN -- deqN.

    Let deqPMsgN := (fifoBaseName ++ idx_to_string (downTo oidx)) -- deqN.
    Definition pInputConverter: Modules :=
      MODULE {
        Rule ("parent_convert_" ++ idx_to_string oidx) :=
          Call msg <- (MethodSig deqPMsgN(): Struct KMsg)();
          LET input <- STRUCT { "in_msg" ::= #msg;
                                "in_msg_from" ::= {$downIdx, compile_oidx_to_cidx oidx} };
          Call (MethodSig enqPInputN(Struct Input): Void)(#input);
          Retv
        }.

    (* Let pInputFifo := dInputFifo ppPInputFifoN. *)
    Let pInputFifo := nfifo ppPInputFifoN (Struct Input) 2.

    Definition build_parent_inputs: Modules :=
      (pInputConverter ++ pInputFifo)%kami.

    Definition ppCRqInputFifoN: string := ("fifoCRqInput_" ++ idx_to_string oidx).
    Definition enqCRqInputN := ppCRqInputFifoN -- enqN.
    Definition deqCRqInputN := ppCRqInputFifoN -- deqN.

    Definition ppCRsInputFifoN: string := ("fifoCRsInput_" ++ idx_to_string oidx).
    Definition enqCRsInputN := ppCRsInputFifoN -- enqN.
    Definition deqCRsInputN := ppCRsInputFifoN -- deqN.

    Let deqCRqN := deqFn (rqUpFrom (l1ExtOf oidx)).
    Definition cInputConverter: Modules :=
      MODULE {
        Rule ("child_convert_" ++ idx_to_string oidx) :=
          Call msg <- (MethodSig deqCRqN(): Struct KMsg)();
          LET input <- STRUCT { "in_msg" ::= #msg;
                                "in_msg_from" ::= {$rqUpIdx, compile_oidx_to_cidx (l1ExtOf oidx)} };
          Call (MethodSig enqCRqInputN(Struct Input): Void)(#input);
          Retv
      }.

    (* Let cRqInputFifo := dInputFifo ppCRqInputFifoN. *)
    (* Let cRsInputFifo := dInputFifo ppCRsInputFifoN. *)
    Let cRqInputFifo := nfifo ppCRqInputFifoN (Struct Input) 2.
    Let cRsInputFifo := nfifo ppCRsInputFifoN (Struct Input) 2.

    Definition build_child_inputs_l1: Modules :=
      (cInputConverter ++ cRqInputFifo)%kami.

    Definition build_child_inputs_li_2: Modules :=
      ((cRqAcceptor2 oidx enqCRqInputN (oidx~>0) (oidx~>1))
         ++ cRqInputFifo
         ++ (cRsAcceptor2 oidx enqCRsInputN (oidx~>0) (oidx~>1))
         ++ cRsInputFifo)%kami.

    Definition build_child_inputs_li_4: Modules :=
      ((cRqAcceptor4 oidx enqCRqInputN (oidx~>0) (oidx~>1) (oidx~>2) (oidx~>3))
         ++ cRqInputFifo
         ++ (cRsAcceptor4 oidx enqCRsInputN (oidx~>0) (oidx~>1) (oidx~>2) (oidx~>3))
         ++ cRsInputFifo)%kami.

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

  Let ppIN2IRN (ppName: string): string := ("fifoN2I_" ++ ppName).
  Let enqIN2IRN (ppName: string) := (ppIN2IRN ppName) -- enqN.
  Let deqIN2IRN (ppName: string) := (ppIN2IRN ppName) -- deqN.

  Let parentN (oidx: IdxT): string := ("parent_" ++ idx_to_string oidx).
  Let childN (oidx: IdxT): string := ("child_" ++ idx_to_string oidx).

  Let ppIR2LRN (ppName: string): string := ("fifoI2L_" ++ ppName).
  Let enqIR2LRN (ppName: string) := (ppIR2LRN ppName) -- enqN.
  Let deqIR2LRN (ppName: string) := (ppIR2LRN ppName) -- deqN.

  Let ppLR2EXN (ppName: string): string := ("fifoL2E_" ++ ppName).
  Let enqLR2EXN (ppName: string) := (ppLR2EXN ppName) -- enqN.
  Let deqLR2EXN (ppName: string) := (ppLR2EXN ppName) -- deqN.

  Definition build_pipeline_l1
             (obj: {sobj: Hemiola.Syntax.Object & HObject sobj}): Modules :=
    let oidx := obj_idx (projT1 obj) in
    let cregs := compile_OState_init oidx in
    let pp := compile_rules_pipeline_l1
                oidx (deqPInputN oidx) (deqCRqInputN oidx)
                (enqIN2IRN (idx_to_string oidx)) (deqIN2IRN (idx_to_string oidx))
                (enqIR2LRN (idx_to_string oidx)) (deqIR2LRN (idx_to_string oidx))
                (enqLR2EXN (idx_to_string oidx)) in
    let execRules := compile_rules_exec
                       oidx (deqLR2EXN (idx_to_string oidx)) (hobj_rules (projT2 obj)) in
    Mod cregs (pp ++ execRules) nil.

  Definition build_pipeline_li
             (obj: {sobj: Hemiola.Syntax.Object & HObject sobj}): Modules :=
    let oidx := obj_idx (projT1 obj) in
    let cregs := compile_OState_init oidx in
    let pp := compile_rules_pipeline_li
                oidx (deqPInputN oidx) (deqCRqInputN oidx) (deqCRsInputN oidx)
                (enqIN2IRN (idx_to_string oidx)) (deqIN2IRN (idx_to_string oidx))
                (enqIR2LRN (idx_to_string oidx)) (deqIR2LRN (idx_to_string oidx))
                (enqLR2EXN (idx_to_string oidx)) in
    let execRules := compile_rules_exec
                       oidx (deqLR2EXN (idx_to_string oidx)) (hobj_rules (projT2 obj)) in
    Mod cregs (pp ++ execRules) nil.

  (* Let n2iFifo (oidx: IdxT) := dIRFifo (ppIN2IRN (idx_to_string oidx)). *)
  (* Let i2lFifo (oidx: IdxT) := dIRFifo (ppIR2LRN (idx_to_string oidx)). *)
  (* Let l2eFifo (oidx: IdxT) := dLRFifo (ppLR2EXN (idx_to_string oidx)). *)

  Let n2iFifo (oidx: IdxT) := ppfifo (ppIN2IRN (idx_to_string oidx)) (Struct IRElt).
  Let i2lFifo (oidx: IdxT) := ppfifo (ppIR2LRN (idx_to_string oidx)) (Struct IRElt).
  Let l2eFifo (oidx: IdxT) := ppfifo (ppLR2EXN (idx_to_string oidx)) (Struct LRElt).

  Definition build_controller_l1
             (obj: {sobj: Hemiola.Syntax.Object & HObject sobj}): Modules :=
    let oidx := obj_idx (projT1 obj) in
    ((build_child_inputs_l1 oidx)
       ++ (build_parent_inputs oidx)
       ++ (build_pipeline_l1 obj)
       ++ (n2iFifo oidx)
       ++ (i2lFifo oidx)
       ++ (l2eFifo oidx)
       ++ build_outputs_l1 oidx
       ++ build_int_fifos oidx
       ++ build_ext_fifos oidx)%kami.

  Definition build_controller_li_2_no_ints
             (obj: {sobj: Hemiola.Syntax.Object & HObject sobj}): Modules :=
    let oidx := obj_idx (projT1 obj) in
    ((build_child_inputs_li_2 oidx)
       ++ (build_parent_inputs oidx)
       ++ (build_pipeline_li obj)
       ++ (n2iFifo oidx)
       ++ (i2lFifo oidx)
       ++ (l2eFifo oidx)
       ++ build_outputs_li oidx)%kami.

  Definition build_controller_li_4_no_ints
             (obj: {sobj: Hemiola.Syntax.Object & HObject sobj}): Modules :=
    let oidx := obj_idx (projT1 obj) in
    ((build_child_inputs_li_4 oidx)
       ++ (build_parent_inputs oidx)
       ++ (build_pipeline_li obj)
       ++ (n2iFifo oidx)
       ++ (i2lFifo oidx)
       ++ (l2eFifo oidx)
       ++ build_outputs_li oidx)%kami.

  Definition build_controller_li_2
             (obj: {sobj: Hemiola.Syntax.Object & HObject sobj}): Modules :=
    let oidx := obj_idx (projT1 obj) in
    (build_controller_li_2_no_ints obj ++ build_int_fifos oidx)%kami.

  Definition build_controller_li_4
             (obj: {sobj: Hemiola.Syntax.Object & HObject sobj}): Modules :=
    let oidx := obj_idx (projT1 obj) in
    (build_controller_li_4_no_ints obj ++ build_int_fifos oidx)%kami.

End Compile.
