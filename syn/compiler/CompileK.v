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

      Definition compile_midx_to_cidx (midx: IdxT): Expr var (SyntaxKind KCIdx) :=
        Const _ (compile_midx_to_cidx_const midx).

      Definition compile_midx_to_qidx (midx: IdxT): Expr var (SyntaxKind KQIdx) :=
        Const _ (compile_midx_to_qidx_const midx).

      Definition compile_oidx_to_cidx (oidx: IdxT): Expr var (SyntaxKind KCIdx) :=
        Const _ (compile_oidx_to_cidx_const oidx).

      Fixpoint compile_rule_ost_vars_fix (n: nat) {sz} (htys: Vector.t htype sz)
               (cont: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) htys) ->
                      ActionT var Void) {struct htys}: ActionT var Void :=
        match htys in Vector.t _ sz
              return (HVector.hvec (Vector.map (fun hty => var (kind_of hty)) htys) ->
                      ActionT var Void) -> ActionT var Void with
        | Vector.nil _ => fun cont => cont tt
        | Vector.cons _ hty _ htys =>
          fun cont =>
            (Read ov: (kind_of hty) <- (ostValNameN n);
            compile_rule_ost_vars_fix
              (S n) htys (fun vars => cont (HVector.hvcons ov vars)))%kami_action
        end cont.

      Definition compile_rule_ost_vars :=
        compile_rule_ost_vars_fix O hostf_ty.

      (** * Step 1: compile the message-accepting rule *)

      (* a local lock *)
      Definition LL :=
        STRUCT { "ll_valid" :: Bool;
                 "ll_cmidx" :: KCIdx;
                 (* The message contains a line address as well *)
                 "ll_msg" :: Struct KMsg }.

      Variables (prln: string) (prl: var (Struct LL))
                (crqrln: string) (crqrl: var (Struct LL))
                (crsrln: string) (crsrl: var (Struct LL))
                (wln: string) (wl: var (Struct LL))
                (rrn: string).

      Definition compile_rule_readlock_parent
                 (cont: var (Struct LL) -> ActionT var Void): ActionT var Void :=
        (Read prl: Struct LL <- prln; cont prl)%kami_action.

      Definition compile_rule_readlock_child_rq
                 (cont: var (Struct LL) -> ActionT var Void): ActionT var Void :=
        (Read crqrl: Struct LL <- crqrln; cont crqrl)%kami_action.

      Definition compile_rule_readlock_child_rs
                 (cont: var (Struct LL) -> ActionT var Void): ActionT var Void :=
        (Read crsrl: Struct LL <- crsrln; cont crsrl)%kami_action.

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
        Write rrn <- (IF #rr == $2 then $0 else #rr + $1);
        Retv)%kami_action.

      (** NOTE: this round robin still has a lot of chances to be optimized. *)
      Definition compile_rule_rr_check (imt: InputMsgType)
                 (cont: ActionT var Void): ActionT var Void :=
        (match imt.(imt_from) with
         | None =>
           match imt.(imt_rqrs) with
           | true => (Read rr: Bit 2 <- rrn; Assert #rr == $2; cont)
           | false => (Assert $$false; cont) (** FIXME: block volunteer-eviction rules for now *)
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
           | true => (Assert !(#crsrl!LL@."ll_valid"); cont)
           | false => (Assert $$false; cont) (** FIXME: block volunteer-eviction rules for now *)
           end
         | Some None => (Assert !(#prl!LL@."ll_valid"); cont)
         | Some (Some _) =>
           match imt.(imt_rqrs) with
           | true => (Assert !(#crsrl!LL@."ll_valid"); cont)
           | false => (Assert !(#crqrl!LL@."ll_valid"); cont)
           end
         end)%kami_action.

      Definition compile_rule_accept_message (imt: InputMsgType)
                 (cont: ActionT var Void): ActionT var Void :=
        (match imt.(imt_from) with
         | None =>
           match imt.(imt_rqrs) with
           | true =>
             (** TODO: [downLockRssFull] is called twice in the first- and
              * the second-phase rule, which is a bit inefficient. *)
             (Call odl <- (downLockRssFull oidx) ();
             Assert #odl!(MaybeStr (Struct DL))@."valid";
             (* Here setting the original request message to [ll_msg] is
              * just to use the "addr" field in [KMsg] *)
             LET msg <- #odl!(MaybeStr (Struct DL))@."data"!DL@."dl_msg";
             Write crsrln: Struct LL <- STRUCT { "ll_valid" ::= $$true;
                                                 "ll_cmidx" ::= $$Default;
                                                 "ll_msg" ::= #msg };
             cont)
           | false => cont (** FIXME *)
           end
         | Some (Some cmidx) =>
           match imt.(imt_rqrs) with
           | true => (Call msgIn <- (deqFromChild cmidx)();
                     Write crsrln: Struct LL <- STRUCT { "ll_valid" ::= $$true;
                                                         "ll_cmidx" ::= compile_midx_to_cidx cmidx;
                                                         "ll_msg" ::= #msgIn };
                     cont)
           | false => (Call msgIn <- (deqFromChild cmidx)();
                      Write crqrln: Struct LL <- STRUCT { "ll_valid" ::= $$true;
                                                          "ll_cmidx" ::= compile_midx_to_cidx cmidx;
                                                          "ll_msg" ::= #msgIn };
                      cont)
           end
         | Some None => (Call msgIn <- (deqFromParent (downTo oidx))();
                        Write prln: Struct LL <- STRUCT { "ll_valid" ::= $$true;
                                                          "ll_cmidx" ::= $$Default;
                                                          "ll_msg" ::= #msgIn };
                        cont)
         end)%kami_action.

      (** * Step 2: compile rules for checking preconditions & requesting transitions *)

      Variables (ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
                (msgIn: var (Struct KMsg))
                (ul: var (Struct UL)) (dl: var (Struct DL)).

      Definition compile_rule_readlocked
                 (imt: InputMsgType) (cont: ActionT var Void): ActionT var Void :=
        (match imt.(imt_from) with
         | None =>
           match imt.(imt_rqrs) with
           | true => (Assert #crsrl!LL@."ll_valid"; cont)
           | false => (Assert $$false; cont) (** FIXME: block volunteer-eviction rules for now *)
           end
         | Some (Some cmidx) =>
           match imt.(imt_rqrs) with
           | true => (Assert #crsrl!LL@."ll_valid";
                     Assert (#crsrl!LL@."ll_cmidx" == compile_midx_to_cidx cmidx);
                     cont)
           | false => (Assert #crqrl!LL@."ll_valid";
                      Assert (#crqrl!LL@."ll_cmidx" == compile_midx_to_cidx cmidx);
                      cont)
           end
         | Some None => (Assert #prl!LL@."ll_valid"; cont)
         end)%kami_action.

      Definition compile_rule_get_readlock_msg
                 (imt: InputMsgType)
                 (cont: var (Struct KMsg) -> ActionT var Void): ActionT var Void :=
        (match imt.(imt_from) with
         | None =>
           match imt.(imt_rqrs) with
           | true => (LET msgIn <- #crsrl!LL@."ll_msg"; cont msgIn)
           | false => (LET msgIn <- $$Default; cont msgIn) (** FIXME *)
           end
         | Some (Some _) =>
           match imt.(imt_rqrs) with
           | true => (LET msgIn <- #crsrl!LL@."ll_msg"; cont msgIn)
           | false => (LET msgIn <- #crqrl!LL@."ll_msg"; cont msgIn)
           end
         | Some None => (LET msgIn <- #prl!LL@."ll_msg"; cont msgIn)
         end)%kami_action.

      Definition compile_rule_writelock
                 (cont: var (Struct LL) -> ActionT var Void): ActionT var Void :=
        (Read wl: Struct LL <- wln; cont wl)%kami_action.

      Definition compile_rule_writelock_available
                 (cont: ActionT var Void): ActionT var Void :=
        (Assert !(#wl!LL@."ll_valid"); cont)%kami_action.

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

      Definition compile_rule_readlock_release
                 (imt: InputMsgType) (cont: ActionT var Void): ActionT var Void :=
        (match imt.(imt_from) with
         | None =>
           match imt.(imt_rqrs) with
           | true => (Write crsrln: Struct LL <- $$Default; cont)
           | false => cont
           end
         | Some (Some _) =>
           match imt.(imt_rqrs) with
           | true => (Write crsrln: Struct LL <- $$Default; cont)
           | false => (Write crqrln: Struct LL <- $$Default; cont)
           end
         | Some None => (Write prln: Struct LL <- $$Default; cont)
         end)%kami_action.

      Definition compile_rule_writelock_acquire
                 (cont: ActionT var Void): ActionT var Void :=
        (Write wln: Struct LL <- STRUCT { "ll_valid" ::= $$true;
                                          "ll_cmidx" ::= $$Default;
                                          "ll_msg" ::= #msgIn };
        cont)%kami_action.

      (** * Step 3: compile rules for state transitions and output messages *)

      Definition compile_rule_writelocked (cont: ActionT var Void): ActionT var Void :=
        (Assert #wl!LL@."ll_valid"; cont)%kami_action.

      Definition compile_rule_get_writelock_msg
                 (cont: var (Struct KMsg) -> ActionT var Void): ActionT var Void :=
        (LET msgIn <- #wl!LL@."ll_msg"; cont msgIn)%kami_action.

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
                           (** FIXME: [msg] should contain the address when eviction-requested *)
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
                           (** FIXME: [msg] should contain the address when eviction-requested *)
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

      Definition compile_rule_trs (rtrs: HOTrs): ActionT var Void :=
        match rtrs with
        | HTrsMTrs mtrs => compile_state_trs mtrs
        end.

      Definition compile_rule_writelock_release
                 (cont: ActionT var Void): ActionT var Void :=
        (Write wln: Struct LL <- $$Default; cont)%kami_action.

    End Phoas.

  End ExtComp.

  Context `{CompExtExp}.

  Section WithObj.
    Variables (oidx: IdxT)
              (rrn prln crqrln crsrln wln: string)
              (ostin: string).

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
             compile_rule_readlock_available prl crqrl crsrl imt;;
             (* NOTE: [compile_rule_accept_message] does acquire a proper readlock. *)
             compile_rule_accept_message oidx prln crqrln crsrln imt;;
             Retv)%kami_action |}.

    Definition readlockIdx: IdxT := 1~>2~>3~>4.
    Definition writelockIdx: IdxT := 5~>6~>7~>8.

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

    Definition compile_rule_1 (rule: {sr: Hemiola.Syntax.Rule & HRule sr}):
      Attribute (Action Void) :=
      let hr := projT2 rule in
      {| attrName := ruleNameI (rule_idx (projT1 rule));
         attrType :=
           fun var =>
             let imt := {| imt_rqrs := detect_input_msg_rqrs (hrule_precond hr (hvar_of var));
                           imt_from := detect_input_msg_from (hrule_msg_from hr) |} in
             (compile_rule_rr_check rrn imt;;
              prl <- compile_rule_readlock_parent prln;
             crqrl <- compile_rule_readlock_child_rq crqrln;
             crsrl <- compile_rule_readlock_child_rs crsrln;
             compile_rule_readlocked prl crqrl crsrl imt;;
             msgIn <- compile_rule_get_readlock_msg prl crqrl crsrl imt;
             wl <- compile_rule_writelock wln;
             compile_rule_writelock_available wl;;
             (** FIXME: should use values from the status-read response *)
             ostVars <- compile_rule_ost_vars ostin;
             ul <- compile_rule_get_uplock oidx msgIn imt;
             dl <- compile_rule_get_downlock oidx msgIn imt;
             compile_rule_prec
               oidx ostVars msgIn ul dl (hrule_precond hr (hvar_of var));;
             compile_rule_readlock_release prln crqrln crsrln imt;;
             compile_rule_writelock_acquire wln msgIn;;
             (** FIXME: no need to acquire a writelock if no state transition *)
             (** FIXME: should make a transition request, not the actual transition *)
             compile_rule_trs
               oidx ostin ostVars msgIn ul dl (hrule_trs hr))%kami_action |}.

    Definition compile_rule_2: Attribute (Action Void) :=
      {| attrName := ruleNameI writelockIdx;
         attrType :=
           fun var =>
             (wl <- compile_rule_writelock wln;
             compile_rule_writelocked wl;;
             (** FIXME: should deal with a transition response *)
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
        ++ (map compile_rule_1 rules)
        ++ [compile_rule_2].

  End WithObj.

  Definition rrReg (oidx: IdxT): string := "rr" ++ idx_to_string oidx.
  Definition prlReg (oidx: IdxT): string := "prl" ++ idx_to_string oidx.
  Definition crqrlReg (oidx: IdxT): string := "crqrl" ++ idx_to_string oidx.
  Definition crsrlReg (oidx: IdxT): string := "crsrl" ++ idx_to_string oidx.
  Definition wlReg (oidx: IdxT): string := "wl" ++ idx_to_string oidx.
  Definition ostInReg (oidx: IdxT): string := "ost" ++ idx_to_string oidx.

  Fixpoint compile_inits (oidx: IdxT) (n: nat) (hts: list htype): list RegInitT :=
    match hts with
    | nil => nil
    | ht :: hts' =>
      {| attrName := ostValNameN (ostInReg oidx) n;
         attrType := RegInitDefault (SyntaxKind (kind_of ht)) |}
        :: compile_inits oidx (S n) hts'
    end.

  Definition compile_OState_init (oidx: IdxT): list RegInitT :=
    {| attrName := rrReg oidx; attrType := RegInitDefault (SyntaxKind (Bit 2)) |}
      :: {| attrName := prlReg oidx; attrType := RegInitDefault (SyntaxKind (Struct LL)) |}
      :: {| attrName := crqrlReg oidx; attrType := RegInitDefault (SyntaxKind (Struct LL)) |}
      :: {| attrName := crsrlReg oidx; attrType := RegInitDefault (SyntaxKind (Struct LL)) |}
      :: {| attrName := wlReg oidx; attrType := RegInitDefault (SyntaxKind (Struct LL)) |}
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

  Definition compile_Object (dtr: Topology.DTree)
             (obj: {sobj: Hemiola.Syntax.Object & HObject sobj})
    : Modules :=
    let oidx := obj_idx (projT1 obj) in
    let cregs := compile_OState_init oidx in
    let crules := compile_rules oidx
                                (rrReg oidx) (prlReg oidx) (crqrlReg oidx) (crsrlReg oidx)
                                (wlReg oidx) (ostInReg oidx)
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
