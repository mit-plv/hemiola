Require Import Numbers.DecimalString.

Require Import Hemiola.Common Hemiola.Index Hemiola.Syntax.
Require Import Hemiola.Ex.TopoTemplate.

Require Import Compiler.HemiolaDeep. (* source *)
Require Import Kami.Lib.Struct Kami Kami.PrimFifo Kami.PrimBram. (* target *)
Require Export Compiler.Components.

Set Implicit Arguments.

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

      Definition compile_midx_to_cidx (midx: IdxT): Expr var (SyntaxKind KCIdx) :=
        Const _ (compile_midx_to_cidx_const midx).

      Definition compile_midx_to_qidx (midx: IdxT): Expr var (SyntaxKind KQIdx) :=
        Const _ (compile_midx_to_qidx_const midx).

      Definition compile_oidx_to_cidx (oidx: IdxT): Expr var (SyntaxKind KCIdx) :=
        Const _ (compile_oidx_to_cidx_const oidx).

      (** * Step 1: compile the message-accepting rule:
       * it makes the read request to the info cache as well. *)

      Class CompLineRW :=
        { (* line read/write-related *)
          lineK: Kind;
          get_line_addr:
            forall (var: Kind -> Type),
              var lineK -> Expr var (SyntaxKind KAddr);
          compile_line_to_ostVars:
            forall (var: Kind -> Type),
              var lineK ->
              (HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty) ->
               ActionT var Void) ->
              ActionT var Void;
          compile_line_update:
            forall (var: Kind -> Type),
              var lineK ->
              forall ht (i: Fin.t ost_sz),
                hostf_ty[@i] = ht ->
                Expr var (SyntaxKind (kind_of ht)) ->
                Expr var (SyntaxKind lineK);
        }.
      Context `{CompLineRW}.

      (* A readlock:
       * - rl_valid: true if the lock being held
       * - rl_cmidx: a child-queue index where the message comes from
       * - rl_msg: the message that required the lock
       * - rl_line_valid: true if [rl_line] is valid
       * - rl_line: holds the information (owned, status, dir, etc.) from the cache.
       *)
      Definition RL :=
        STRUCT { "rl_valid" :: Bool;
                 "rl_cmidx" :: KCIdx;
                 (** NOTE: the message contains a line address as well *)
                 "rl_msg" :: Struct KMsg;
                 "rl_line_valid" :: Bool;
                 "rl_line" :: lineK }.

      (* Used to have ["wl_msgs_out" :: Struct KMsgsOut], feat. [KMsgsOut] *)
      Definition WL :=
        STRUCT { "wl_valid" :: Bool;
                 "wl_write_rq" :: Bool }.

      Variables
        (prln: string) (prl: var (Struct RL))
        (crqrln: string) (crqrl: var (Struct RL))
        (crsrln: string) (crsrl: var (Struct RL))
        (erln: string) (erl: var Bool)
        (* rlc: a two-bit flag saying which readlock is being used;
         * p(10), crq(00), crs(01) *)
        (rlcn: string)
        (wln: string) (wl: var (Struct WL))
        (* rr: also a two-bit flag for round-robin *)
        (rrn: string).

      Definition compile_rule_readlock_parent
                 (cont: var (Struct RL) -> ActionT var Void): ActionT var Void :=
        (Read prl: Struct RL <- prln; cont prl)%kami_action.

      Definition compile_rule_readlock_child_rq
                 (cont: var (Struct RL) -> ActionT var Void): ActionT var Void :=
        (Read crqrl: Struct RL <- crqrln; cont crqrl)%kami_action.

      Definition compile_rule_readlock_child_rs
                 (cont: var (Struct RL) -> ActionT var Void): ActionT var Void :=
        (Read crsrl: Struct RL <- crsrln; cont crsrl)%kami_action.

      Definition compile_rule_readlock_evict
                 (cont: var Bool -> ActionT var Void): ActionT var Void :=
        (Read erl: Bool <- erln; cont erl)%kami_action.

      Definition detect_input_msg_rqrs_r (rrp: HOPrecR): bool :=
        match rrp with
        | HRsAccepting => true
        | HRssFull => true
        | _ => false
        end.

      Fixpoint detect_input_msg_rqrs (rp: HOPrecT (hvar_of var)): bool :=
        match rp with
        | HOPrecAnd prec1 prec2 =>
          (detect_input_msg_rqrs prec1) || (detect_input_msg_rqrs prec2)
        | HOPrecRqRs _ rrprec => detect_input_msg_rqrs_r rrprec
        | HOPrecProp _ => false
        end.

      (* [Some None] if from the parent, [Some (Some cmidx)] if from a child,
       * and [None] if no input message. *)
      Definition detect_input_msg_from (mf: HMsgFrom): option (option IdxT) :=
        match mf with
        | HMsgFromNil => None
        | HMsgFromParent pmidx => Some None
        | HMsgFromChild cmidx => Some (Some cmidx)
        | HMsgFromExt emidx => Some (Some emidx)
        | HMsgFromUpLock => Some None
        | HMsgFromDownLock cidx => Some (Some cidx)
        end.

      Record InputMsgType :=
        { imt_rqrs: bool; imt_from: option (option IdxT) }.

      Definition compile_rule_rr_step: ActionT var Void :=
        (Read rr: Bit 2 <- rrn;
        Write rrn <- #rr + $1;
        Retv)%kami_action.

      (** NOTE: this round robin still has a lot of chances to be optimized. *)
      Definition compile_rule_rr_check (imt: InputMsgType)
                 (cont: ActionT var Void): ActionT var Void :=
        (match imt.(imt_from) with
         | None =>
           match imt.(imt_rqrs) with
           | true => (Read rr: Bit 2 <- rrn; Assert #rr == $2; cont)
           | false =>
             (* for eviction requests *)
             (Read rr: Bit 2 <- rrn; Assert #rr == $3; cont)
           end
         | Some None => (Read rr: Bit 2 <- rrn; Assert #rr == $0; cont)
         | Some (Some _) =>
           match imt.(imt_rqrs) with
           | true => (Read rr: Bit 2 <- rrn; Assert #rr == $2; cont)
           | false => (Read rr: Bit 2 <- rrn; Assert #rr == $1; cont)
           end
         end)%kami_action.

      Definition compile_rule_readlock_available (imt: InputMsgType)
                 (cont: ActionT var Void): ActionT var Void :=
        (match imt.(imt_from) with
         | None =>
           match imt.(imt_rqrs) with
           | true => (Assert !(#crsrl!RL@."rl_valid"); cont)
           | false => (Assert !#erl; cont)
           end
         | Some None => (Assert !(#prl!RL@."rl_valid"); cont)
         | Some (Some _) =>
           match imt.(imt_rqrs) with
           | true => (Assert !(#crsrl!RL@."rl_valid"); cont)
           | false => (Assert !(#crqrl!RL@."rl_valid"); cont)
           end
         end)%kami_action.

      Definition compile_rule_request_read
                 (addr: Expr var (SyntaxKind (Bit hcfg_addr_sz)))
                 (cont: ActionT var Void): ActionT var Void :=
        (Call (readRq oidx hcfg_addr_sz) (addr); cont)%kami_action.

      (* OPT: no need to make an info request if no read *)
      Definition compile_rule_accept_message_and_request_read (imt: InputMsgType)
                 (cont: ActionT var Void): ActionT var Void :=
        (match imt.(imt_from) with
         | None =>
           match imt.(imt_rqrs) with
           | true =>
             (** TODO: [downLockRssFull] is called twice in the first- and
              * the second-phase rule, which is a bit inefficient. *)
             (Call odl <- (downLockRssFull oidx) ();
             Assert #odl!(MaybeStr (Struct DL))@."valid";
             (* Here setting the original request message to [rl_msg] is
              * just to use the "addr" field in [KMsg] *)
             LET msg <- #odl!(MaybeStr (Struct DL))@."data"!DL@."dl_msg";
             Write crsrln: Struct RL <- STRUCT { "rl_valid" ::= $$true;
                                                 "rl_cmidx" ::= $$Default;
                                                 "rl_msg" ::= #msg;
                                                 "rl_line_valid" ::= $$false;
                                                 "rl_line" ::= $$Default };
             Write rlcn: Bit 2 <- $1;
             compile_rule_request_read (#msg!KMsg@."addr")%kami_expr cont)
           | false => cont (* nothing to do in case of eviction *)
           end
         | Some (Some cmidx) =>
           match imt.(imt_rqrs) with
           | true => (Call msgIn <- (deqFromChild cmidx)();
                     Write crsrln: Struct RL <- STRUCT { "rl_valid" ::= $$true;
                                                         "rl_cmidx" ::= compile_midx_to_cidx cmidx;
                                                         "rl_msg" ::= #msgIn;
                                                         "rl_line_valid" ::= $$false;
                                                         "rl_line" ::= $$Default };
                     Write rlcn: Bit 2 <- $1;
                     compile_rule_request_read (#msgIn!KMsg@."addr")%kami_expr cont)
           | false => (Call msgIn <- (deqFromChild cmidx)();
                      Write crqrln: Struct RL <- STRUCT { "rl_valid" ::= $$true;
                                                          "rl_cmidx" ::= compile_midx_to_cidx cmidx;
                                                          "rl_msg" ::= #msgIn;
                                                          "rl_line_valid" ::= $$false;
                                                          "rl_line" ::= $$Default };
                      Write rlcn: Bit 2 <- $0;
                      compile_rule_request_read (#msgIn!KMsg@."addr")%kami_expr cont)
           end
         | Some None => (Call msgIn <- (deqFromParent (downTo oidx))();
                        Write prln: Struct RL <- STRUCT { "rl_valid" ::= $$true;
                                                          "rl_cmidx" ::= $$Default;
                                                          "rl_msg" ::= #msgIn;
                                                          "rl_line_valid" ::= $$false;
                                                          "rl_line" ::= $$Default };
                        Write rlcn: Bit 2 <- $2;
                        compile_rule_request_read (#msgIn!KMsg@."addr")%kami_expr cont)
         end)%kami_action.

      (** * Step 2: take a read response, save it in a proper readlock. *)

      (* NOTE: [lineK] should match with [CacheLineK ..] in [Components.cache]. *)
      Definition readRs := MethodSig (readRsN oidx) (): lineK.
      Definition compile_rule_take_info_resp (cont: ActionT var Void): ActionT var Void :=
        (Call od <- readRs ();
        Read rlc: Bit 2 <- rlcn;
        If (#rlc == $0) (* crq *)
        then (Write crqrln: Struct RL <- STRUCT { "rl_valid" ::= #crqrl!RL@."rl_valid";
                                                  "rl_cmidx" ::= #crqrl!RL@."rl_cmidx";
                                                  "rl_msg" ::= #crqrl!RL@."rl_msg";
                                                  "rl_line_valid" ::= $$true;
                                                  "rl_line" ::= #od }; Retv)
        else (If (#rlc == $1)
              then (Write crsrln: Struct RL <- STRUCT { "rl_valid" ::= #crsrl!RL@."rl_valid";
                                                        "rl_cmidx" ::= #crsrl!RL@."rl_cmidx";
                                                        "rl_msg" ::= #crsrl!RL@."rl_msg";
                                                        "rl_line_valid" ::= $$true;
                                                        "rl_line" ::= #od }; Retv)
              else (Write prln: Struct RL <- STRUCT { "rl_valid" ::= #prl!RL@."rl_valid";
                                                      "rl_cmidx" ::= #prl!RL@."rl_cmidx";
                                                      "rl_msg" ::= #prl!RL@."rl_msg";
                                                      "rl_line_valid" ::= $$true;
                                                      "rl_line" ::= #od }; Retv);
              Retv); cont)%kami_action.

      (** * Step 3: compile rules for checking preconditions & requesting transitions:
       * it takes a info-read response, checks its precondition, and makes
       * the write request to the info/value caches. *)

      Variables
        (pline: var lineK)
        (ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
        (msgIn: var (Struct KMsg))
        (ul: var (Struct UL)) (dl: var (Struct DL)).

      (** 3-1: check there is already a proper readlock and the information is ready. *)

      (* NOTE: [lineK] should match with [CacheLineK ..] in [Components.cache]. *)
      Definition getVictim := MethodSig (getVictimN oidx) (): lineK.

      (* NOTE: should be safe to extract "data" directly from "rl_line",
       *       since the info cache returns the default value in case of miss. *)
      Definition compile_rule_readlocked_and_info_ready
                 (imt: InputMsgType)
                 (cont: var lineK -> ActionT var Void): ActionT var Void :=
        (match imt.(imt_from) with
         | None =>
           match imt.(imt_rqrs) with
           | true => (Assert (#crsrl!RL@."rl_valid" && #crsrl!RL@."rl_line_valid");
                     LET i <- #crsrl!RL@."rl_line"; cont i)
           | false => (Assert #erl; Call i <- getVictim (); cont i)
           end
         | Some (Some cmidx) =>
           match imt.(imt_rqrs) with
           | true => (Assert (#crsrl!RL@."rl_valid" && #crsrl!RL@."rl_line_valid");
                     Assert (#crsrl!RL@."rl_cmidx" == compile_midx_to_cidx cmidx);
                     LET i <- #crsrl!RL@."rl_line"; cont i)
           | false => (Assert (#crqrl!RL@."rl_valid" && #crqrl!RL@."rl_line_valid");
                      Assert (#crqrl!RL@."rl_cmidx" == compile_midx_to_cidx cmidx);
                      LET i <- #crqrl!RL@."rl_line"; cont i)
           end
         | Some None => (Assert (#prl!RL@."rl_valid" && #prl!RL@."rl_line_valid");
                        LET i <- #prl!RL@."rl_line"; cont i)
         end)%kami_action.

      Definition compile_rule_get_readlock_msg
                 (imt: InputMsgType)
                 (cont: var (Struct KMsg) -> ActionT var Void): ActionT var Void :=
        (match imt.(imt_from) with
         | None =>
           match imt.(imt_rqrs) with
           | true => (LET msgIn <- #crsrl!RL@."rl_msg"; cont msgIn)
           | false => (LET msgIn <- $$Default; cont msgIn)
           end
         | Some (Some _) =>
           match imt.(imt_rqrs) with
           | true => (LET msgIn <- #crsrl!RL@."rl_msg"; cont msgIn)
           | false => (LET msgIn <- #crqrl!RL@."rl_msg"; cont msgIn)
           end
         | Some None => (LET msgIn <- #prl!RL@."rl_msg"; cont msgIn)
         end)%kami_action.

      (** 3-2: check the precondition using the input message and the information *)

      Fixpoint compile_bexp {hbt} (he: hbexp (hbvar_of var) hbt)
        : Expr var (SyntaxKind (kind_of_hbtype hbt)) :=
        (match he with
         | HBConst _ c => Const _ (compile_const c)
         | HVar _ _ v => Var _ (SyntaxKind _) v
         | HIdmId pe => ((compile_bexp pe)!KCIdm@."cidx")
         | HIdmMsg pe => ((compile_bexp pe)!KCIdm@."msg")
         | HObjIdxOf midx => (_truncate_ (compile_bexp midx))
         | HAddrB _ => $0 (* Used only when making an eviction request with a nondet. addr *)
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
         (* The expressions below are used only when dealing with responses. *)
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
         | HExtP _ ep => compile_eoprec _ ul dl ostVars ep
         | HNativeP _ _ => $$true
         end)%kami_expr.

      Definition compile_rule_rqrs_prec (rrp: HOPrecR)
                 (cont: ActionT var Void): ActionT var Void :=
        (match rrp with
         | HRqAccepting => (Assert (!(#msgIn!KMsg@."type")); cont)
         | HRsAccepting => (Assert (#msgIn!KMsg@."type"); cont)
         | HUpLockFree =>
           (Call canUl <- (upLockable oidx) (#msgIn!KMsg@."addr"); Assert #canUl; cont)
         | HDownLockFree =>
           (Call canDl <- (downLockable oidx) (#msgIn!KMsg@."addr"); Assert #canDl; cont)
         | HUpLockMsgId mty mid =>
           (Assert (#ul!UL@."ul_valid");
           Assert (#ul!UL@."ul_rsb");
           Assert (#ul!UL@."ul_msg"!KMsg@."type" == Const _ (ConstBool mty));
           Assert (#ul!UL@."ul_msg"!KMsg@."id" == $$%mid%:hcfg_msg_id_sz);
           cont)
         | HUpLockMsg =>
           (Assert (#ul!UL@."ul_valid"); Assert (#ul!UL@."ul_rsb"); cont)
         | HUpLockIdxBack =>
           (Assert (#ul!UL@."ul_valid"); Assert (#ul!UL@."ul_rsb"); cont)
         | HUpLockBackNone =>
           (Assert (#ul!UL@."ul_valid"); Assert (!(#ul!UL@."ul_rsb")); cont)
         | HDownLockMsgId mty mid =>
           (Assert (#dl!DL@."dl_valid");
           Assert (#dl!DL@."dl_rsb");
           Assert (#dl!DL@."dl_msg"!KMsg@."type" == Const _ (ConstBool mty));
           Assert (#dl!DL@."dl_msg"!KMsg@."id" == $$%mid%:hcfg_msg_id_sz);
           cont)
         | HDownLockMsg =>
           (Assert (#dl!DL@."dl_valid"); Assert (#dl!DL@."dl_rsb"); cont)
         | HDownLockIdxBack =>
           (Assert (#dl!DL@."dl_valid"); Assert (#dl!DL@."dl_rsb"); cont)
         | HMsgIdFrom msgId => (Assert (#msgIn!KMsg@."id" == $$%msgId%:hcfg_msg_id_sz); cont)
         | HRssFull => (Assert (#dl!DL@."dl_rss_recv" == #dl!DL@."dl_rss_from"); cont)
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

      (** 3-3: make the rule transition (write requests):
       * 1) [HOState]: (maybe) make a write request to the cache,
       *    with the new info/line value.
       * 2) [HORq]: change the MSHR status.
       * 3) [HMsgsOut]: since the current info/line already being read,
       *    the output messages can be generated. *)

      Definition compile_rule_readlock_release
                 (imt: InputMsgType) (cont: ActionT var Void): ActionT var Void :=
        (match imt.(imt_from) with
         | None =>
           match imt.(imt_rqrs) with
           | true => (Write crsrln: Struct RL <- $$Default; cont)
           | false => (Write erln: Bool <- $$false; cont)
           end
         | Some (Some _) =>
           match imt.(imt_rqrs) with
           | true => (Write crsrln: Struct RL <- $$Default; cont)
           | false => (Write crqrln: Struct RL <- $$Default; cont)
           end
         | Some None => (Write prln: Struct RL <- $$Default; cont)
         end)%kami_action.

      Definition compile_rule_writelock
                 (cont: var (Struct WL) -> ActionT var Void): ActionT var Void :=
        (Read wl: Struct WL <- wln; cont wl)%kami_action.

      Definition compile_rule_writelock_available
                 (cont: ActionT var Void): ActionT var Void :=
        (Assert !(#wl!WL@."wl_valid"); cont)%kami_action.

      Definition compile_rule_writelock_acquire
                 (wrq: Expr var (SyntaxKind Bool))
                 (cont: ActionT var Void): ActionT var Void :=
        (Write wln: Struct WL <- STRUCT { "wl_valid" ::= $$true;
                                          "wl_write_rq" ::= wrq };
        cont)%kami_action.

      Definition compile_rule_get_uplock (imt: InputMsgType)
                 (cont: var (Struct UL) -> ActionT var Void): ActionT var Void :=
        (match imt.(imt_rqrs), imt.(imt_from) with
         | true, Some None =>
           (* A response from the parent *)
           (Call oul <- (upLockGet oidx) (#msgIn!KMsg@."addr");
           Assert #oul!(MaybeStr (Struct UL))@."valid";
           LET ul <- #oul!(MaybeStr (Struct UL))@."data";
           cont ul)
         | _, _ => (LET ul <- $$Default; cont ul)
         end)%kami_action.

      Definition compile_rule_get_downlock (imt: InputMsgType)
                 (cont: var (Struct DL) -> ActionT var Void): ActionT var Void :=
        (match imt.(imt_rqrs), imt.(imt_from) with
         | true, Some (Some _) =>
           (* A response from a child *)
           (Call odl <- (downLockGet oidx) (#msgIn!KMsg@."addr");
           Assert #odl!(MaybeStr (Struct DL))@."valid";
           LET dl <- #odl!(MaybeStr (Struct DL))@."data";
           cont dl)
         | true, None =>
           (* When [RssFull]: see the definition of [detect_input_msg_rqrs_r] *)
           (Call odl <- (downLockRssFull oidx) ();
           Assert #odl!(MaybeStr (Struct DL))@."valid";
           LET dl <- #odl!(MaybeStr (Struct DL))@."data";
           cont dl)
         | _, _ => (LET dl <- $$Default; cont dl)
         end)%kami_action.

      Definition compile_rule_writelocked_silent (cont: ActionT var Void): ActionT var Void :=
        (Assert (#wl!WL@."wl_valid" && !(#wl!WL@."wl_write_rq")); cont)%kami_action.

      Definition compile_rule_writelocked_rs (cont: ActionT var Void): ActionT var Void :=
        (Assert (#wl!WL@."wl_valid" && #wl!WL@."wl_write_rq"); cont)%kami_action.

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

      (* NOTE: [lineK] should match with [CacheLineK ..] in [Components.cache]. *)
      Definition writeRq := MethodSig (writeRqN oidx) (lineK): Void.

      Fixpoint compile_OState_write_fix
               (host: HOState (hvar_of var))
               (rinfo: var lineK)
               (cont: var lineK -> ActionT var Void): ActionT var Void :=
        (match host with
         | HOStateI _ => cont rinfo
         | @HOstUpdate _ _ _ _ _ _ _ _ i ht Heq he host' =>
           (LET ninfo <- compile_line_update rinfo _ Heq (compile_exp he);
           compile_OState_write_fix host' ninfo cont)
         end)%kami_action.

      Definition bypass_write_rl (rln: string) (nline: var lineK)
                 (cont: ActionT var Void): ActionT var Void :=
        (Read rl: Struct RL <- rln;
        If ((#rl!RL@."rl_valid") && (#rl!RL@."rl_line_valid") &&
            (#rl!RL@."rl_msg"!KMsg@."addr" == #msgIn!KMsg@."addr"))
         then (Write rln: Struct RL <- STRUCT { "rl_valid" ::= $$true;
                                                "rl_cmidx" ::= #rl!RL@."rl_cmidx";
                                                "rl_msg" ::= #rl!RL@."rl_msg";
                                                "rl_line_valid" ::= $$true;
                                                "rl_line" ::= #nline };
              Retv);
         cont)%kami_action.

      Definition compile_rule_bypass_write_rl
                 (ninfo: var lineK) (imt: InputMsgType)
                 (cont: ActionT var Void): ActionT var Void :=
        (match imt.(imt_from) with
         | None =>
           match imt.(imt_rqrs) with
           | true => (bypass_write_rl prln ninfo (bypass_write_rl crqrln ninfo cont))
           | false => cont (* NOTE: the victim line gets up-to-date inside the cache module *)
           end
         | Some (Some _) =>
           match imt.(imt_rqrs) with
           | true => (bypass_write_rl prln ninfo (bypass_write_rl crqrln ninfo cont))
           | false => (bypass_write_rl prln ninfo (bypass_write_rl crsrln ninfo cont))
           end
         | Some None =>
           (bypass_write_rl crqrln ninfo (bypass_write_rl crsrln ninfo cont))
         end)%kami_action.

      Definition compile_request_write
                 (line: Expr var (SyntaxKind lineK))
                 (cont: ActionT var Void): ActionT var Void :=
        (Call writeRq (line); cont)%kami_action.

      Definition compile_OState_request_write
                 (host: HOState (hvar_of var)) (imt: InputMsgType)
                 (cont: Expr var (SyntaxKind Bool) -> ActionT var Void): ActionT var Void :=
        (match host with
         | HOStateI _ => cont ($$false)%kami_expr
         | _ =>
           compile_OState_write_fix
             host pline
             (fun nline =>
                compile_request_write
                  (#nline)%kami_expr
                  (compile_rule_bypass_write_rl nline imt (cont ($$true)%kami_expr)))
         end)%kami_action.

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
                           "r_ul_msg" ::= STRUCT { "id" ::= $$Default;
                                                   "type" ::= $$false; (* request *)
                                                   "addr" ::= get_line_addr _ pline;
                                                   "value" ::= $$Default };
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
           (** NOTE: silent down-requests;
            * not used in non-inclusive cache-coherence protocols *)
           (Call (registerDL oidx)
                 (STRUCT { "r_dl_rsb" ::= $$false;
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
         | HMsgOutNil _ =>
           (* NOTE: assume no output messages as the eviction responses *)
           (Call (removeVictim oidx)(); cont)
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

      Fixpoint compile_MonadT_trs (hm: HMonadT (hvar_of var)) (imt: InputMsgType)
               (cont: Expr var (SyntaxKind Bool) -> ActionT var Void): ActionT var Void :=
        (match hm with
         | HBind hv mcont =>
           Let_ (compile_bval hv)
                (fun x: var (kind_of_hbtype _) => compile_MonadT_trs (mcont x) imt cont)
         | HRet host horq hmsgs =>
           compile_OState_request_write
             host imt (fun we => compile_ORq_trs horq (compile_MsgsOut_trs hmsgs (cont we)))
         end)%kami_action.

      Definition compile_rule_trs (trs: HOTrs) (imt: InputMsgType)
                 (cont: Expr var (SyntaxKind Bool) -> ActionT var Void)
        : ActionT var Void :=
        match trs with
        | HTrsMTrs (HMTrs mn) => compile_MonadT_trs (mn (hvar_of var)) imt cont
        end.

      (** * Step 4: compile rules for handling the write response with possible eviction *)

      Definition compile_rule_writelock_release
                 (cont: ActionT var Void): ActionT var Void :=
        (Write wln: Struct WL <- $$Default; cont)%kami_action.

      Definition writeRs := MethodSig (writeRsN oidx) (): Void.
      Definition compile_rule_take_write_response
                 (cont: ActionT var Void): ActionT var Void :=
        (Call writeRs (); cont)%kami_action.

    End Phoas.

  End ExtComp.

  Context `{ee: @ExtExp dv oifc het} `{cet: CompExtType}
          `{@CompExtExp ee cet} `{@CompLineRW cet}.

  Section WithObj.
    Variables (oidx: IdxT)
              (rrn prln crqrln crsrln erln rlcn wln: string).

    Definition ruleNameBase: string := "rule".
    Definition ruleNameI (ridx: IdxT) :=
      (ruleNameBase
         ++ "_" ++ idx_to_string oidx
         ++ "_" ++ idx_to_string ridx)%string.

    Local Notation "v <- f ; cont" :=
      (f (fun v => cont)) (at level 60, right associativity, only parsing).
    Local Notation "f ;; cont" :=
      (f cont) (at level 60, right associativity, only parsing).

    Definition compile_rule_0 (ridx: IdxT) (imt: InputMsgType):
      Attribute (Action Void) :=
      {| attrName := ruleNameI ridx;
         attrType :=
           fun var =>
             (prl <- compile_rule_readlock_parent prln;
             crqrl <- compile_rule_readlock_child_rq crqrln;
             crsrl <- compile_rule_readlock_child_rs crsrln;
             erl <- compile_rule_readlock_evict erln;
             compile_rule_readlock_available prl crqrl crsrl erl imt;;
             compile_rule_accept_message_and_request_read
               oidx prln crqrln crsrln rlcn imt;;
             Retv)%kami_action |}.

    Definition readlockIdx: IdxT := 1~>2~>3.
    Definition infoIdx: IdxT := 4~>5~>6.
    Definition writelockIdx: IdxT := 7~>8~>9.

    Definition compile_rule_rr :=
      {| attrName := "rr_" ++ idx_to_string oidx;
         attrType := fun var => @compile_rule_rr_step var rrn |}.

    Definition compile_rule_0_parent :=
      compile_rule_0 (readlockIdx~>0) {| imt_rqrs := false; (* don't care *)
                                         imt_from := Some None |}.

    Definition compile_rule_0_child_rq (cmidx: IdxT) :=
      compile_rule_0 (readlockIdx~>1~~cmidx)
                     {| imt_rqrs := false; imt_from := Some (Some cmidx) |}.
    Definition compile_rule_0_children_rq (dtr: Topology.DTree) :=
      map (fun cidx => compile_rule_0_child_rq (rqUpFrom cidx))
          (Topology.subtreeChildrenIndsOf dtr oidx).

    Definition compile_rule_0_child_rs (cmidx: IdxT) :=
      compile_rule_0 (readlockIdx~>2~~cmidx)
                     {| imt_rqrs := true; imt_from := Some (Some cmidx) |}.
    Definition compile_rule_0_children_rs (dtr: Topology.DTree) :=
      map (fun cidx => compile_rule_0_child_rs (rsUpFrom cidx))
          (Topology.subtreeChildrenIndsOf dtr oidx).

    Definition compile_rule_0_release_rs :=
      compile_rule_0 (readlockIdx~>3)
                     {| imt_rqrs := true; imt_from := None |}.

    Definition compile_rule_1: Attribute (Action Void) :=
      {| attrName := ruleNameI infoIdx;
         attrType :=
           fun var =>
             (prl <- compile_rule_readlock_parent prln;
             crqrl <- compile_rule_readlock_child_rq crqrln;
             crsrl <- compile_rule_readlock_child_rs crsrln;
             compile_rule_take_info_resp
               oidx prln prl crqrln crqrl crsrln crsrl rlcn Retv)%kami_action |}.

    Definition compile_rule_2 (rule: {sr: Hemiola.Syntax.Rule & HRule sr}):
      Attribute (Action Void) :=
      let hr := projT2 rule in
      {| attrName := ruleNameI (rule_idx (projT1 rule));
         attrType :=
           fun var =>
             let imt := {| imt_rqrs := detect_input_msg_rqrs (hrule_precond hr (hvar_of var));
                           imt_from := detect_input_msg_from (hrule_msg_from hr) |} in
             (compile_rule_rr_check rrn imt;;
              (* Check the readlock and see if the information is read *)
              prl <- compile_rule_readlock_parent prln;
             crqrl <- compile_rule_readlock_child_rq crqrln;
             crsrl <- compile_rule_readlock_child_rs crsrln;
             erl <- compile_rule_readlock_evict erln;
             pline <- compile_rule_readlocked_and_info_ready oidx prl crqrl crsrl erl imt;
             (* NOTE: [compile_line_to_ostVars] only covers info slots;
              *       we know the value will not be read in this rule. *)
             ostVars <- compile_line_to_ostVars pline;
             msgIn <- compile_rule_get_readlock_msg prl crqrl crsrl imt;
             (* Check the precondition *)
             ul <- compile_rule_get_uplock oidx msgIn imt;
             dl <- compile_rule_get_downlock oidx msgIn imt;
             compile_rule_prec
               oidx ostVars msgIn ul dl (hrule_precond hr (hvar_of var));;
             (* Release the readlock *)
             compile_rule_readlock_release prln crqrln crsrln erln imt;;
             (* Request to read/write a value/status appropriately *)
             wrq <- compile_rule_trs
                      oidx prln crqrln crsrln
                      pline ostVars msgIn ul dl (hrule_trs hr) imt;
             (** OPT: no need to acquire a writelock if [wrq == $$false] *)
             (* Check if a writelock is available *)
             wl <- compile_rule_writelock wln;
             compile_rule_writelock_available wl;;
             (* Acquire the writelock; save the log about what are requested *)
             compile_rule_writelock_acquire wln wrq;;
             Retv)%kami_action |}.

    Definition compile_rule_3_silent: Attribute (Action Void) :=
      {| attrName := ruleNameI (writelockIdx~>0);
         attrType :=
           fun var =>
             (wl <- compile_rule_writelock wln;
             compile_rule_writelocked_silent wl;;
             compile_rule_writelock_release wln;;
             Retv)%kami_action |}.

    Definition compile_rule_3_rs: Attribute (Action Void) :=
      {| attrName := ruleNameI (writelockIdx~>1);
         attrType :=
           fun var =>
             (wl <- compile_rule_writelock wln;
             compile_rule_writelocked_rs wl;;
             compile_rule_take_write_response oidx;;
             compile_rule_writelock_release wln;;
             Retv)%kami_action |}.

    Definition compile_rules (dtr: Topology.DTree)
               (rules: list {sr: Hemiola.Syntax.Rule & HRule sr}):
      list (Attribute (Action Void)) :=
      compile_rule_rr
        :: compile_rule_0_parent
        :: compile_rule_0_release_rs
        :: (compile_rule_0_children_rq dtr)
        ++ (compile_rule_0_children_rs dtr)
        ++ [compile_rule_1]
        ++ (map compile_rule_2 rules)
        ++ [compile_rule_3_silent; compile_rule_3_rs].

  End WithObj.

  Definition rrReg (oidx: IdxT): string := "rr" ++ idx_to_string oidx.
  Definition prlReg (oidx: IdxT): string := "prl" ++ idx_to_string oidx.
  Definition crqrlReg (oidx: IdxT): string := "crqrl" ++ idx_to_string oidx.
  Definition crsrlReg (oidx: IdxT): string := "crsrl" ++ idx_to_string oidx.
  Definition erlReg (oidx: IdxT): string := "erl" ++ idx_to_string oidx.
  Definition rlcReg (oidx: IdxT): string := "rlc" ++ idx_to_string oidx.
  Definition wlReg (oidx: IdxT): string := "wl" ++ idx_to_string oidx.

  Definition compile_OState_init (oidx: IdxT): list RegInitT :=
    {| attrName := rrReg oidx; attrType := RegInitDefault (SyntaxKind (Bit 2)) |}
      :: {| attrName := prlReg oidx; attrType := RegInitDefault (SyntaxKind (Struct RL)) |}
      :: {| attrName := crqrlReg oidx; attrType := RegInitDefault (SyntaxKind (Struct RL)) |}
      :: {| attrName := crsrlReg oidx; attrType := RegInitDefault (SyntaxKind (Struct RL)) |}
      :: {| attrName := erlReg oidx; attrType := RegInitDefault (SyntaxKind Bool) |}
      :: {| attrName := rlcReg oidx; attrType := RegInitDefault (SyntaxKind (Bit 2)) |}
      :: {| attrName := wlReg oidx; attrType := RegInitDefault (SyntaxKind (Struct WL)) |}
      :: nil.

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

  Definition compile_Object (dtr: Topology.DTree)
             (obj: {sobj: Hemiola.Syntax.Object & HObject sobj})
    : Modules :=
    let oidx := obj_idx (projT1 obj) in
    let cregs := compile_OState_init oidx in
    let crules := compile_rules oidx
                                (rrReg oidx) (prlReg oidx) (crqrlReg oidx) (crsrlReg oidx)
                                (erlReg oidx) (rlcReg oidx) (wlReg oidx)
                                dtr (hobj_rules (projT2 obj)) in
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
