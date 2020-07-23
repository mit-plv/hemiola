Require Import Numbers.DecimalString.

Require Import Hemiola.Common Hemiola.Index Hemiola.Ex.TopoTemplate.
Require Import Compiler.HemiolaDeep. (* source *)
Require Import Kami.Lib.Struct Kami Kami.PrimFifo Kami.PrimBram. (* target *)

Set Implicit Arguments.

(** TODO: move to Kami *)
Notation "v '#[' idx <- val ] " := (UpdateArray v idx val) (at level 10) : kami_expr_scope.

Notation "∘ sz" := (snd sz * fst sz) (at level 0).

Definition nat_to_string (n: nat): string :=
  NilEmpty.string_of_uint (Nat.to_uint n).

Fixpoint idx_to_word_fix (deg width: nat) (idx: IdxT): word (width * deg) :=
  match width with
  | O => WO
  | S w =>
    match idx with
    | nil => wzero _
    | n :: i => combine (natToWord deg n) (idx_to_word_fix deg w i)
    end
  end.

Definition idx_to_word (sz: nat * nat) (idx: IdxT): word ∘sz :=
  idx_to_word_fix (fst sz) (snd sz) idx.

Notation "% i %: sz" := (idx_to_word sz i) (at level 5): kami_expr_scope.

Fixpoint idx_to_string (idx: IdxT): string :=
  match idx with
  | nil => ""
  | i :: idx' => idx_to_string idx' ++ nat_to_string i
  end.
(* Eval compute in (idx_to_string (0~>1~>2)). *)

Definition MaybeStr (k: Kind) :=
  STRUCT { "valid" :: Bool; "data" :: k }.
Definition Maybe (k: Kind) := Struct (MaybeStr k).
Definition MaybeNone {var k}: Expr var (SyntaxKind (Maybe k)) :=
  (STRUCT { "valid" ::= $$false; "data" ::= $$Default })%kami_expr.
Definition MaybeSome {var k} (v: Expr var (SyntaxKind k)): Expr var (SyntaxKind (Maybe k)) :=
  (STRUCT { "valid" ::= $$true; "data" ::= v })%kami_expr.

Section Acceptor4.
  Variable oidx: IdxT.
  Variables (dataT: Kind).
  Variables (forwardN acceptN0 acceptN1 acceptN2 acceptN3: string).

  Local Notation "s '+o'" := (s ++ "_" ++ idx_to_string oidx)%string (at level 60).
  Local Notation "s1 _++ s2" := (s1 ++ "_" ++ s2)%string (at level 60).

  Local Notation acceptF0 := (MethodSig acceptN0(): dataT).
  Local Notation acceptF1 := (MethodSig acceptN1(): dataT).
  Local Notation acceptF2 := (MethodSig acceptN2(): dataT).
  Local Notation acceptF3 := (MethodSig acceptN3(): dataT).
  Local Notation forward := (MethodSig forwardN(dataT): Void).

  Let rrSz := 2.

  Definition acceptor: Kami.Syntax.Modules :=
    MODULE {
        Register ("rr"+o): Bit rrSz <- Default
        with Rule "inc_rr"+o :=
          Read rr: Bit rrSz <- "rr"+o;
          Write "rr"+o <- #rr + $1;
          Retv
        with Rule "accept0"+o :=
          Read rr: Bit rrSz <- "rr"+o; Assert (#rr == $0);
          Call val <- acceptF0(); Call forward(#val); Retv
        with Rule "accept1"+o :=
          Read rr: Bit rrSz <- "rr"+o; Assert (#rr == $1);
          Call val <- acceptF1(); Call forward(#val); Retv
        with Rule "accept2"+o :=
          Read rr: Bit rrSz <- "rr"+o; Assert (#rr == $2);
          Call val <- acceptF2(); Call forward(#val); Retv
        with Rule "accept3"+o :=
          Read rr: Bit rrSz <- "rr"+o; Assert (#rr == $3);
          Call val <- acceptF3(); Call forward(#val); Retv
      }.

End Acceptor4.

Section Bitvector.
  Variable sz: nat.
  Local Notation sz_lg := (Nat.log2 sz).

  Context {var: Kind -> Type}.

  Definition bvSet (bv: (Bit sz) @ var) (i: (Bit sz_lg) @ var): (Bit sz) @ var :=
    (bv ~| ($1 << i))%kami_expr.

  Definition bvUnset (bv: (Bit sz) @ var) (i: (Bit sz_lg) @ var): (Bit sz) @ var :=
    (bv ~& UniBit (Inv _) ($1 << i))%kami_expr.

  Definition bvTest (bv: (Bit sz) @ var) (i: (Bit sz_lg) @ var): Bool @ var :=
    ((bv ~| ($1 << i)) == bv)%kami_expr.

  Definition bvAll (bv: (Bit sz) @ var): Bool @ var :=
    (bv == $$(wones _))%kami_expr.

  Fixpoint bvFirstSetFix {n} (bv: (Bit n) @ var) {m}: (Bit m) @ var :=
    (match n return (((Bit n) @ var) -> forall m, (Bit m) @ var)
     with
     | O => fun _ _ => $$Default
     | S n' =>
       fun bv _ =>
         (IF (UniBit (Trunc 1 _) bv == $$(WO~1))
          then $0
          else $1 + bvFirstSetFix (UniBit (TruncLsb 1 _) bv))
     end bv m)%kami_expr.

  Definition bvFirstSet (bv: (Bit sz) @ var): (Bit sz_lg) @ var :=
    bvFirstSetFix bv.

  Definition bvSingleton (i: (Bit sz_lg) @ var): (Bit sz) @ var :=
    ($1 << i)%kami_expr.

  Definition bvIsSingleton (bv: (Bit sz) @ var) (i: (Bit sz_lg) @ var): Bool @ var :=
    (bv == ($1 << i))%kami_expr.

  Fixpoint bvCountFix {n} (bv: (Bit n) @ var) {m}: (Bit m) @ var :=
    (match n return (((Bit n) @ var) -> forall m, (Bit m) @ var)
     with
     | O => fun _ _ => $$Default
     | S n' =>
       fun bv _ =>
         ((IF (UniBit (Trunc 1 _) bv == $$(WO~1)) then $1 else $0)
          + bvCountFix (UniBit (TruncLsb 1 _) bv))
     end bv m)%kami_expr.

  Definition bvCount (bv: (Bit sz) @ var): (Bit (S sz_lg)) @ var :=
    bvCountFix bv.

End Bitvector.

Class TopoConfig :=
  { hcfg_value_sz: nat;
    hcfg_line_values_lg: nat;
    hcfg_children_max_pred: nat }.
Definition hcfg_children_max `{TopoConfig} := S hcfg_children_max_pred.
Definition hcfg_children_max_lg `{TopoConfig} := Nat.log2 hcfg_children_max.

Section Kinds.
  Context `{ReifyConfig} `{TopoConfig}.

  Definition KCIdx := Bit hcfg_children_max_lg.
  Definition KQIdx := Bit (hcfg_children_max_lg + 2).
  Definition KCBv := Bit hcfg_children_max. (* as a bitvector *)
  Definition KIdxM := Bit ∘hcfg_msg_id_sz.
  Definition KAddr := Bit hcfg_addr_sz.
  Definition KValue := Vector (Bit hcfg_value_sz) hcfg_line_values_lg.

  Definition KMsg :=
    STRUCT { "id" :: KIdxM;
             "type" :: Bool;
             "addr" :: KAddr;
             "value" :: KValue }.

End Kinds.

Section MSHR.
  Context `{ReifyConfig} `{TopoConfig}.
  Variable oidx: IdxT.

  Definition MSHR :=
    STRUCT { "m_valid" :: Bool;
             "m_is_ul" :: Bool;
             "m_msg" :: Struct KMsg;
             "m_rsb" :: Bool;
             "m_rsbTo" :: KQIdx; (* Use as it is for downlocks; truncate for uplocks *)
             "m_dl_rss_from" :: KCBv;
             "m_dl_rss_recv" :: KCBv;
             "m_dl_rss" :: Array (Struct KMsg) hcfg_children_max }.

  Local Notation "s '+o'" := (s ++ "_" ++ idx_to_string oidx)%string (at level 60).
  Local Notation "s1 _++ s2" := (s1 ++ "_" ++ s2)%string (at level 60).

  Variable numPRqs numCRqs: nat.
  Let predNumSlots := numPRqs + numCRqs - 1.
  Let numSlots := S predNumSlots.
  Let slotSz := S (Nat.log2 predNumSlots).
  Let MshrId := Bit slotSz.

  Definition getPRqSlot: Attribute SignatureT := MethodSig ("getPRqSlot"+o)(): Maybe MshrId.
  Definition getCRqSlot: Attribute SignatureT := MethodSig ("getCRqSlot"+o)(): Maybe MshrId.
  Definition canRegUL: Attribute SignatureT := MethodSig ("canRegUL"+o)(KAddr): Bool.
  Definition canRegDL: Attribute SignatureT := MethodSig ("canRegDL"+o)(KAddr): Bool.

  Definition RegUL :=
    STRUCT { "r_id" :: MshrId;
             "r_ul_msg" :: Struct KMsg; (* contains a line address *)
             "r_ul_rsb" :: Bool;
             "r_ul_rsbTo" :: KCIdx }.
  Definition registerUL: Attribute SignatureT :=
    MethodSig ("registerUL"+o)(Struct RegUL): Void.

  Definition RegDL :=
    STRUCT { "r_id" :: MshrId;
             "r_dl_msg" :: Struct KMsg;
             "r_dl_rss_from" :: KCBv;
             "r_dl_rsb" :: Bool;
             "r_dl_rsbTo" :: KQIdx }.
  Definition registerDL: Attribute SignatureT :=
    MethodSig ("registerDL"+o)(Struct RegDL): Void.

  Definition TrsfUpDown :=
    STRUCT { "r_id" :: MshrId; "r_dl_rss_from" :: KCBv }.
  Definition transferUpDown: Attribute SignatureT :=
    MethodSig ("transferUpDown"+o)(Struct TrsfUpDown): Void.

  Definition release: Attribute SignatureT := MethodSig ("release"+o)(MshrId): Void.

  Definition AddRs :=
    STRUCT { "r_dl_midx" :: KCIdx; "r_dl_msg" :: Struct KMsg }.
  Definition addRs: Attribute SignatureT := MethodSig ("addRs"+o)(Struct AddRs): Void.

  Fixpoint rqFix {var k}
           (lc: Expr var (SyntaxKind k))
           (tc: nat -> Expr var (SyntaxKind (Struct MSHR)) -> Expr var (SyntaxKind k))
           (cond: Expr var (SyntaxKind (Struct MSHR)) -> Expr var (SyntaxKind Bool))
           (rqs: Expr var (SyntaxKind (Array (Struct MSHR) numSlots)))
           (n: nat): Expr var (SyntaxKind k) :=
    (match n with
     | O => lc
     | S n' =>
       let ul := rqs#[$$(natToWord slotSz (numSlots - n))] in
       (IF (cond ul) then tc (numSlots - n)%nat ul else rqFix lc tc cond rqs n')
     end)%kami_expr.

  Definition rqIter {var k}
             (lc: Expr var (SyntaxKind k))
             (tc: nat -> Expr var (SyntaxKind (Struct MSHR)) -> Expr var (SyntaxKind k))
             (cond: Expr var (SyntaxKind (Struct MSHR)) -> Expr var (SyntaxKind Bool))
             (rqs: Expr var (SyntaxKind (Array (Struct MSHR) numSlots))) :=
    rqFix lc tc cond rqs numSlots.

  Fixpoint prqFix {var k}
           (lc: Expr var (SyntaxKind k))
           (tc: nat -> Expr var (SyntaxKind (Struct MSHR)) -> Expr var (SyntaxKind k))
           (cond: Expr var (SyntaxKind (Struct MSHR)) -> Expr var (SyntaxKind Bool))
           (rqs: Expr var (SyntaxKind (Array (Struct MSHR) numSlots)))
           (n: nat): Expr var (SyntaxKind k) :=
    (match n with
     | O => lc
     | S n' =>
       let ul := rqs#[$$(natToWord slotSz (numPRqs - n))] in
       (IF (cond ul) then tc (numPRqs - n)%nat ul else prqFix lc tc cond rqs n')
     end)%kami_expr.

  Definition prqIter {var k}
             (lc: Expr var (SyntaxKind k))
             (tc: nat -> Expr var (SyntaxKind (Struct MSHR)) -> Expr var (SyntaxKind k))
             (cond: Expr var (SyntaxKind (Struct MSHR)) -> Expr var (SyntaxKind Bool))
             (rqs: Expr var (SyntaxKind (Array (Struct MSHR) numSlots))) :=
    prqFix lc tc cond rqs numPRqs.

  Fixpoint crqFix {var k}
           (lc: Expr var (SyntaxKind k))
           (tc: nat -> Expr var (SyntaxKind (Struct MSHR)) -> Expr var (SyntaxKind k))
           (cond: Expr var (SyntaxKind (Struct MSHR)) -> Expr var (SyntaxKind Bool))
           (rqs: Expr var (SyntaxKind (Array (Struct MSHR) numSlots)))
           (n: nat): Expr var (SyntaxKind k) :=
    (match n with
     | O => lc
     | S n' =>
       let ul := rqs#[$$(natToWord slotSz (numCRqs - n + numPRqs))] in
       (IF (cond ul) then tc (numCRqs - n + numPRqs)%nat ul else crqFix lc tc cond rqs n')
     end)%kami_expr.

  Definition crqIter {var k}
             (lc: Expr var (SyntaxKind k))
             (tc: nat -> Expr var (SyntaxKind (Struct MSHR)) -> Expr var (SyntaxKind k))
             (cond: Expr var (SyntaxKind (Struct MSHR)) -> Expr var (SyntaxKind Bool))
             (rqs: Expr var (SyntaxKind (Array (Struct MSHR) numSlots))) :=
    crqFix lc tc cond rqs numCRqs.

  Definition mshrs: Kami.Syntax.Modules :=
    MODULE {
        Register ("rqs"+o): Array (Struct MSHR) numSlots <- Default

        with Method ("getPRqSlot"+o)(): Maybe MshrId :=
          Read rqs <- "rqs"+o;
          LET ret <- (prqIter MaybeNone
                              (fun n _ => MaybeSome $n)
                              (fun m => !(m!MSHR@."m_valid"))
                              #rqs);
          Ret #ret
        with Method ("getCRqSlot"+o)(): Maybe MshrId :=
          Read rqs <- "rqs"+o;
          LET ret <- (crqIter MaybeNone
                              (fun n _ => MaybeSome $(n + numPRqs))
                              (fun m => !(m!MSHR@."m_valid"))
                              #rqs);
          Ret #ret

        with Method ("canRegUL"+o)(addr: KAddr): Bool :=
          Read rqs <- "rqs"+o;
          (* PRq cannot make any uplocks *)
          LET ret <- (crqIter $$true
                              (fun _ _ => $$false)
                              (fun m =>
                                 m!MSHR@."m_is_ul" && m!MSHR@."m_msg"!KMsg@."addr" == #addr)
                              #rqs);
          Ret #ret
        with Method ("canRegDL"+o)(addr: KAddr): Bool :=
          Read rqs <- "rqs"+o;
          LET ret <- (rqIter $$true
                             (fun _ _ => $$false)
                             (fun m =>
                                (!(m!MSHR@."m_is_ul")) && m!MSHR@."m_msg"!KMsg@."addr" == #addr)
                             #rqs);
          Ret #ret

        with Method ("registerUL"+o)(ul: Struct RegUL): Void :=
          LET mid <- #ul!RegUL@."r_id";
          LET mshr: Struct MSHR <- STRUCT { "m_valid" ::= $$true;
                                            "m_is_ul" ::= $$true;
                                            "m_msg" ::= #ul!RegUL@."r_ul_msg";
                                            "m_rsb" ::= #ul!RegUL@."r_ul_rsb";
                                            "m_rsbTo" ::= _zeroExtend_ (#ul!RegUL@."r_ul_rsbTo");
                                            "m_dl_rss_from" ::= $$Default;
                                            "m_dl_rss_recv" ::= $$Default;
                                            "m_dl_rss" ::= $$Default };
          Read rqs: Array (Struct MSHR) numSlots <- "rqs"+o;
          Write "rqs"+o <- #rqs#[#mid <- #mshr];
          Retv
        with Method ("registerDL"+o)(dl: Struct RegDL): Void :=
          LET mid <- #dl!RegDL@."r_id";
          LET mshr: Struct MSHR <- STRUCT { "m_valid" ::= $$true;
                                            "m_is_ul" ::= $$false;
                                            "m_msg" ::= #dl!RegDL@."r_dl_msg";
                                            "m_rsb" ::= #dl!RegDL@."r_dl_rsb";
                                            "m_rsbTo" ::= #dl!RegDL@."r_dl_rsbTo";
                                            "m_dl_rss_from" ::= #dl!RegDL@."r_dl_rss_from";
                                            "m_dl_rss_recv" ::= $$Default;
                                            "m_dl_rss" ::= $$Default };
          Read rqs: Array (Struct MSHR) numSlots <- "rqs"+o;
          Write "rqs"+o <- #rqs#[#mid <- #mshr];
          Retv

        with Method ("transferUpDown"+o)(trsf: Struct TrsfUpDown): Void :=
          Read rqs: Array (Struct MSHR) numSlots <- "rqs"+o;
          LET mid <- #trsf!TrsfUpDown@."r_id";
          LET pmshr <- #rqs#[#mid];
          LET nmshr: Struct MSHR <- STRUCT { "m_valid" ::= $$true;
                                             "m_is_ul" ::= $$false;
                                             "m_msg" ::= #pmshr!MSHR@."m_msg";
                                             "m_rsb" ::= #pmshr!MSHR@."m_rsb";
                                             "m_rsbTo" ::= #pmshr!MSHR@."m_rsbTo";
                                             "m_dl_rss_from" ::= #trsf!TrsfUpDown@."r_dl_rss_from";
                                             "m_dl_rss_recv" ::= $$Default;
                                             "m_dl_rss" ::= $$Default };
          Write "rqs"+o <- #rqs#[#mid <- #nmshr];
          Retv

        with Method ("release"+o)(mid: MshrId): Void :=
          Read rqs: Array (Struct MSHR) numSlots <- "rqs"+o;
          Write "rqs"+o <- #rqs#[#mid <- $$Default];
          Retv

        with Method ("addRs"+o)(a: Struct AddRs): Void :=
          Read rqs: Array (Struct MSHR) numSlots <- "rqs"+o;
          LET addr <- #a!AddRs@."r_msg"!KMsg@."addr";
          LET mid: MshrId <- (rqIter $$Default
                                     (fun n _ => $n)
                                     (fun m =>
                                        (!(m!MSHR@."m_is_ul")) &&
                                        m!MSHR@."m_msg"!KMsg@."addr" == #addr)
                                     #rqs);
          LET pmshr <- #rqs#[#mid];
          LET nmshr: Struct MSHR <- STRUCT { "m_valid" ::= #pmshr!MSHR@."m_valid";
                                             "m_is_ul" ::= #pmshr!MSHR@."m_is_ul";
                                             "m_msg" ::= #pmshr!MSHR@."m_msg";
                                             "m_rsb" ::= #pmshr!MSHR@."m_rsb";
                                             "m_rsbTo" ::= #pmshr!MSHR@."m_rsbTo";
                                             "m_dl_rss_from" ::= #pmshr!MSHR@."m_dl_rss_from";
                                             "m_dl_rss_recv" ::=
                                                bvSet (#pmshr!MSHR@."m_dl_rss_recv")
                                                      (#a!AddRs@."r_dl_midx");
                                             "m_dl_rss" ::=
                                               (#pmshr!MSHR@."m_dl_rss")
                                                 #[#a!AddRs@."r_dl_midx" <- #a!AddRs@."r_dl_msg"] };
          Write "rqs"+o <- #rqs#[#mid <- #nmshr];
          Retv
      }.

End MSHR.

Section NCID.
  Variables (oidx: IdxT)
            (* Common *)
            (infoK edirK dataK: Kind)
            (* D$ + info cache + "Traditional" directory *)
            (tagSz indexSz offsetSz addrSz lgWay: nat)
            (* "Extended" directory *)
            (edirLgWay: nat)
            (* Victim lines *)
            (predNumVictim: nat).

  Local Notation "s '+o'" := (s ++ "__" ++ idx_to_string oidx)%string (at level 60).
  Local Notation "s1 _++ s2" := (s1 ++ "__" ++ s2)%string (at level 60).

  Let numVictim := S predNumVictim.
  Let victimIdxSz := Nat.log2 predNumVictim.

  (*! Private cache interfaces *)

  Local Notation "'NCall' v <- f ; cont" :=
    (f (fun v => cont%kami_action))
      (at level 12, right associativity, v at level 15, f at level 15, only parsing): kami_action_scope.
  Local Notation "'NCall' f ; cont" :=
    (f cont%kami_action)
      (at level 12, right associativity, f at level 15, only parsing): kami_action_scope.

  Definition TagValue (valueK: Kind) :=
    STRUCT { "tag" :: Bit tagSz; "value" :: valueK }.

  (** Information cache *)

  Let TagInfo := TagValue infoK.
  Let TagInfoK := Struct TagInfo.

  Definition infoRamN (way: nat): string := "infoRam"+o _++ nat_to_string way.
  Definition infoRam (way: nat) := bram2 (infoRamN way) indexSz TagInfoK.
  Definition infoRdReq (way: nat) :=
    MethodSig ((infoRamN way) -- "rdReq")(Bit indexSz): Void.
  Definition infoRdResp (way: nat) :=
    MethodSig ((infoRamN way) -- "rdResp")(): TagInfoK.
  Definition infoWrReq (way: nat) :=
    MethodSig ((infoRamN way) -- "wrReq")(Struct (BramWriteReq indexSz TagInfoK)): Void.

  Fixpoint makeInfoRdReqsFix (var: Kind -> Type)
           (index: var (Bit indexSz))
           (n: nat) {retK} (cont: ActionT var retK): ActionT var retK :=
    (match n with
     | O => cont
     | S n' => makeInfoRdReqsFix index n' (Call (infoRdReq n')(#index); cont)
     end)%kami_action.
  Definition makeInfoRdReqs (var: Kind -> Type)
             (index: var (Bit indexSz))
             {retK} (cont: ActionT var retK): ActionT var retK :=
    makeInfoRdReqsFix index (Nat.pow 2 lgWay) cont.

  Fixpoint makeInfoRdRespsFix (var: Kind -> Type)
           (tis: var (Vector TagInfoK lgWay))
           (n: nat) {retK} (cont: var (Vector TagInfoK lgWay) -> ActionT var retK)
    : ActionT var retK :=
    (match n with
     | O => cont tis
     | S n' => (NCall ptis <- makeInfoRdRespsFix tis n';
               Call ti <- (infoRdResp n')();
               LET ntis <- #ptis@[$n' <- #ti];
               (cont ntis))
     end)%kami_action.
  Definition makeInfoRdResps (var: Kind -> Type)
             (tis: var (Vector TagInfoK lgWay))
             {retK} (cont: var (Vector TagInfoK lgWay) -> ActionT var retK) :=
    makeInfoRdRespsFix tis (Nat.pow 2 lgWay) cont.

  (** Extended directory *)

  Let TagEDir := TagValue edirK.
  Let TagEDirK := Struct TagEDir.

  Definition edirRamN (way: nat): string := "edirRam"+o _++ nat_to_string way.
  Definition edirRam (way: nat) := bram2 (edirRamN way) indexSz TagEDirK.
  Definition edirRdReq (way: nat) :=
    MethodSig ((edirRamN way) -- "rdReq")(Bit indexSz): Void.
  Definition edirRdResp (way: nat) :=
    MethodSig ((edirRamN way) -- "rdResp")(): TagEDirK.
  Definition edirWrReq (way: nat) :=
    MethodSig ((edirRamN way) -- "wrReq")(Struct (BramWriteReq indexSz TagEDirK)): Void.

  Fixpoint makeEDirRdReqsFix (var: Kind -> Type)
           (index: var (Bit indexSz))
           (n: nat) {retK} (cont: ActionT var retK): ActionT var retK :=
    (match n with
     | O => cont
     | S n' => makeEDirRdReqsFix index n' (Call (edirRdReq n')(#index); cont)
     end)%kami_action.
  Definition makeEDirRdReqs (var: Kind -> Type)
             (index: var (Bit indexSz))
             {retK} (cont: ActionT var retK): ActionT var retK :=
    makeEDirRdReqsFix index (Nat.pow 2 edirLgWay) cont.

  Fixpoint makeEDirRdRespsFix (var: Kind -> Type)
           (tis: var (Vector TagEDirK edirLgWay))
           (n: nat) {retK} (cont: var (Vector TagEDirK edirLgWay) -> ActionT var retK)
    : ActionT var retK :=
    (match n with
     | O => cont tis
     | S n' => (NCall ptis <- makeEDirRdRespsFix tis n';
               Call ti <- (edirRdResp n')();
               LET ntis <- #ptis@[$n' <- #ti];
               (cont ntis))
     end)%kami_action.
  Definition makeEDirRdResps (var: Kind -> Type)
             (tis: var (Vector TagEDirK edirLgWay))
             {retK} (cont: var (Vector TagEDirK edirLgWay) -> ActionT var retK) :=
    makeEDirRdRespsFix tis (Nat.pow 2 edirLgWay) cont.

  (** Data cache *)

  Definition dataIndexSz := indexSz + lgWay.
  Definition dataRamN: string := "dataRam"+o.
  Definition dataRam := bram2 dataRamN dataIndexSz dataK.
  Definition dataRdReq := MethodSig (dataRamN -- "rdReq") (Bit dataIndexSz): Void.
  Definition dataRdResp := MethodSig (dataRamN -- "rdResp") (): dataK.
  Definition dataWrReq :=
    MethodSig (dataRamN -- "wrReq") (Struct (BramWriteReq dataIndexSz dataK)): Void.

  (** Replacement cache *)

  Definition AccType := Bit 2.
  Definition accValid {var}: Expr var (SyntaxKind AccType) := ($0)%kami_expr.
  Definition accInvalid {var}: Expr var (SyntaxKind AccType) := ($1)%kami_expr.
  Definition accTouch {var}: Expr var (SyntaxKind AccType) := ($2)%kami_expr.
  Definition accReset {var}: Expr var (SyntaxKind AccType) := ($3)%kami_expr.

  Definition AccessRec :=
    STRUCT { "acc_type" :: AccType; "acc_index" :: Bit indexSz; "way" :: Bit lgWay }.
  Let AccessRecK := Struct AccessRec.

  Definition repAccess := MethodSig ("repAccess"+o)(AccessRecK): Void.
  Definition repGet := MethodSig ("repGet"+o)(Bit indexSz): Bit lgWay.

  (*! Public interface for the info/value caches *)

  Definition InfoRead :=
    STRUCT { "info_hit" :: Bool;
             "info_way" :: Bit lgWay; (* a replaceable way, if miss *)
             "edir_hit" :: Bool;
             "edir_way" :: Bit edirLgWay;
             "info" :: infoK
           }.
  Let InfoReadK := Struct InfoRead.

  Definition cacheN: string := "cache"+o.

  (** Stage 1: request to read information *)
  Definition infoReadRqN: string := cacheN _++ "infoReadRq".
  Definition infoReadRq := MethodSig infoReadRqN (Bit addrSz): Void.

  (** Stage 2: get the information response, and
   * - on cache hit: request to read the value.
   * - on cache miss: hold the victim information and request to read the victim value. *)
  Definition infoReadRsN: string := cacheN _++ "infoReadRs".
  Definition infoReadRs := MethodSig infoReadRsN (): InfoReadK.

  Definition IdxWay :=
    STRUCT { "index" :: Bit indexSz; "way" :: Bit lgWay }.
  Let IdxWayK := Struct IdxWay.
  Definition valueReadRqN: string := cacheN _++ "valueReadRq".
  Definition valueReadRq := MethodSig valueReadRqN (IdxWayK): Void.
  Definition victimValueRqN: string := cacheN _++ "victimValueRq".
  Definition victimValueRq := MethodSig victimValueRqN (): Void.

  (** Stage 3: get the value response and request to write information/value. *)
  Definition valueReadRsN: string := cacheN _++ "valueReadRs".
  Definition valueReadRs := MethodSig valueReadRsN (): dataK.
  Definition victimValueRsN: string := cacheN _++ "victimValueRs".
  Definition victimValueRs := MethodSig victimValueRsN (): Void.

  Definition LineWrite :=
    STRUCT { "addr" :: Bit addrSz;
             "info_write" :: Bool;
             "info_way" :: Bit lgWay;
             "info" :: infoK;
             "edir_write" :: Bool;
             "edir_way" :: Bit edirLgWay;
             "value_write" :: Bool;
             "value" :: dataK
           }.
  Let LineWriteK := Struct LineWrite.

  Definition writeRqN: string := cacheN _++ "writeRq".
  Definition writeRq := MethodSig writeRqN (LineWriteK): Void.

  (* Definition getVictimN: string := cacheN _++ "getVictim". *)
  (* Definition getVictim := MethodSig getVictimN (): VictimK. *)
  (* Definition removeVictimN: string := cacheN _++ "removeVictim". *)
  (* Definition removeVictim := MethodSig removeVictimN (Bit addrSz): Void. *)

  (*! -- public interface ends here *)

  Variables (getIndex: forall ty, fullType ty (SyntaxKind (Bit addrSz)) ->
                                  Expr ty (SyntaxKind (Bit indexSz)))
            (getTag: forall ty, fullType ty (SyntaxKind (Bit addrSz)) ->
                                Expr ty (SyntaxKind (Bit tagSz)))
            (buildAddr: forall ty, fullType ty (SyntaxKind (Bit tagSz)) ->
                                   fullType ty (SyntaxKind (Bit indexSz)) ->
                                   Expr ty (SyntaxKind (Bit addrSz)))
            (edirToInfo: forall ty, fullType ty (SyntaxKind edirK) ->
                                    Expr ty (SyntaxKind infoK))
            (evictF: forall ty, Expr ty (SyntaxKind infoK) ->
                                Expr ty (SyntaxKind Bool)).

  Definition TagMatch (valueK: Kind) (lw: nat) :=
    STRUCT { "tm_hit" :: Bool;
             "tm_way" :: Bit lw;
             "tm_value" :: valueK }.

  Fixpoint doTagMatch (var: Kind -> Type)
           (tag: var (Bit tagSz))
           {valueK lw} (tags: var (Vector (Struct (TagValue valueK)) lw))
           (n: nat): Expr var (SyntaxKind (Struct (TagMatch valueK lw))) :=
    (match n with
     | O => $$Default
     | S n' =>
       (IF (#tags@[$(Nat.pow 2 lw - n)]!(TagValue valueK)@."tag" == #tag)
        then (STRUCT { "tm_hit" ::= $$true;
                       "tm_way" ::= $(Nat.pow 2 lw - n);
                       "tm_value" ::= #tags@[$(Nat.pow 2 lw - n)]!(TagValue valueK)@."value" })
        else (doTagMatch _ tag tags n'))
     end)%kami_expr.

  (* Fixpoint findLineWrite (var: Kind -> Type) *)
  (*          (tags: var (Vector (Struct (TagValue infoK)) lgWay)) *)
  (*          (n: nat): Expr var (SyntaxKind (Bit lgWay)) := *)
  (*   (match n with *)
  (*    | O => $$Default (* cannot happen *) *)
  (*    | S n' => *)
  (*      (IF (evictF (#tags@[$(Nat.pow 2 lgWay - n)]!(TagValue infoK)@."value")) *)
  (*       then $(Nat.pow 2 lgWay - n) *)
  (*       else (findLineWrite _ tags n')) *)
  (*    end)%kami_expr. *)

  (* Fixpoint infoPutRqWFix (var: Kind -> Type) *)
  (*          (way: var (Bit lgWay)) *)
  (*          (rq: var (Struct (BramRq indexSz TagInfoK))) *)
  (*          (n: nat) (cont: ActionT var Void): ActionT var Void := *)
  (*   match n with *)
  (*   | O => cont *)
  (*   | S n' => *)
  (*     (If (#way == $(Nat.pow 2 lgWay - n)) *)
  (*      then (Call (infoPutRq (Nat.pow 2 lgWay - n))(#rq); Retv); *)
  (*      infoPutRqWFix way rq n' cont)%kami_action *)
  (*   end. *)

  (* Definition infoPutRqW (var: Kind -> Type) *)
  (*            (way: var (Bit lgWay)) *)
  (*            (rq: var (Struct (BramRq indexSz TagInfoK))) *)
  (*            (cont: ActionT var Void): ActionT var Void := *)
  (*   infoPutRqWFix way rq (Nat.pow 2 lgWay) cont. *)

  (* Fixpoint infoGetRsWFix (var: Kind -> Type) *)
  (*          (way: var (Bit lgWay)) *)
  (*          (ti: var TagInfoK) *)
  (*          (n: nat) (cont: var TagInfoK -> ActionT var Void): ActionT var Void := *)
  (*   match n with *)
  (*   | O => cont ti *)
  (*   | S n' => *)
  (*     (If (#way == $(Nat.pow 2 lgWay - n)) *)
  (*      then (Call nti <- (infoGetRs (Nat.pow 2 lgWay - n))(); Ret #nti) *)
  (*      else (Ret $$Default) *)
  (*       as mti; *)
  (*     infoGetRsWFix way mti n' cont)%kami_action *)
  (*   end. *)

  (* Definition infoGetRsW (var: Kind -> Type) *)
  (*            (way: var (Bit lgWay)) *)
  (*            (cont: var TagInfoK -> ActionT var Void): ActionT var Void := *)
  (*   (LET tid <- $$Default; *)
  (*   infoGetRsWFix way tid (Nat.pow 2 lgWay) cont)%kami_action. *)

  (** Victim lines *)

  Definition MayVictim :=
    STRUCT { "mv_index" :: Bit indexSz;
             "mv_way" :: Bit lgWay;
             "mv_info" :: infoK;
             "mv_value" :: dataK }.
  Let MayVictimK := Struct MayVictim.

  Definition Victim :=
    STRUCT { "victim_valid" :: Bool;
             "victim_addr" :: Bit addrSz;
             "victim_info" :: infoK;
             "victim_value" :: dataK }.
  Let VictimK := Struct Victim.

  Local Notation "$v$ n" :=
    (Const _ (natToWord victimIdxSz n)) (at level 5): kami_expr_scope.

  Fixpoint victimIterAFix (var: Kind -> Type)
           (victims: Expr var (SyntaxKind (Array VictimK numVictim)))
           (addr: Expr var (SyntaxKind (Bit addrSz)))
           (readF: nat -> Expr var (SyntaxKind VictimK) -> ActionT var Void)
           (cont: ActionT var Void) (n: nat): ActionT var Void :=
    match n with
    | O => cont
    | S n' =>
      (LET victim: VictimK <- victims#[$v$(Nat.pow 2 lgWay - n)];
      If ((#victim!Victim@."victim_valid")
          && #victim!Victim@."victim_addr" == addr)
       then (readF (Nat.pow 2 lgWay - n) (#victim)%kami_expr)
       else (victimIterAFix victims addr readF cont n'); Retv)%kami_action
    end.

  Definition victimIterA (var: Kind -> Type)
             (victims: Expr var (SyntaxKind (Array VictimK numVictim)))
             (addr: Expr var (SyntaxKind (Bit addrSz)))
             (readF: nat -> Expr var (SyntaxKind VictimK) -> ActionT var Void)
             (cont: ActionT var Void): ActionT var Void :=
    victimIterAFix victims addr readF cont numVictim.

  (* Fixpoint hasVictimSlotFix (var: Kind -> Type) *)
  (*          (victims: Expr var (SyntaxKind (Array VictimK numVictim))) *)
  (*          (n: nat): Expr var (SyntaxKind Bool) := *)
  (*   (match n with *)
  (*    | O => !(victims#[$v$0]!Victim@."victim_valid") *)
  (*    | S n' => *)
  (*      ((!(victims#[$v$n]!Victim@."victim_valid")) || hasVictimSlotFix victims n') *)
  (*    end)%kami_expr. *)

  (* Fixpoint hasVictimSlotF (var: Kind -> Type) *)
  (*          (victims: Expr var (SyntaxKind (Array VictimK numVictim))) *)
  (*   : Expr var (SyntaxKind Bool) := *)
  (*   hasVictimSlotFix victims (numVictim - 1). *)

  (* Fixpoint hasVictimFix (var: Kind -> Type) *)
  (*          (victims: Expr var (SyntaxKind (Array VictimK numVictim))) *)
  (*          (n: nat): Expr var (SyntaxKind Bool) := *)
  (*   (match n with *)
  (*    | O => (victims#[$v$0]!Victim@."victim_valid") *)
  (*    | S n' => *)
  (*      ((victims#[$v$n]!Victim@."victim_valid") || hasVictimFix victims n') *)
  (*    end)%kami_expr. *)

  (* Fixpoint hasVictimF (var: Kind -> Type) *)
  (*          (victims: Expr var (SyntaxKind (Array VictimK numVictim))) *)
  (*   : Expr var (SyntaxKind Bool) := *)
  (*   hasVictimFix victims (numVictim - 1). *)

  (* Fixpoint getVictimSlotFix (var: Kind -> Type) *)
  (*          (victims: Expr var (SyntaxKind (Array VictimK numVictim))) *)
  (*          (n: nat): Expr var (SyntaxKind (Bit victimIdxSz)) := *)
  (*   (match n with *)
  (*    | O => $0 *)
  (*    | S n' => *)
  (*      (IF (victims#[$v$n]!Victim@."victim_valid") *)
  (*       then getVictimSlotFix victims n' *)
  (*       else $n) *)
  (*    end)%kami_expr. *)

  (* Fixpoint getVictimSlotF (var: Kind -> Type) *)
  (*          (victims: Expr var (SyntaxKind (Array VictimK numVictim))) *)
  (*   : Expr var (SyntaxKind (Bit victimIdxSz)) := *)
  (*   getVictimSlotFix victims (numVictim - 1). *)

  (* Fixpoint getVictimFix (var: Kind -> Type) *)
  (*          (victims: Expr var (SyntaxKind (Array VictimK numVictim))) *)
  (*          (n: nat): Expr var (SyntaxKind LineWriteK) := *)
  (*   (match n with *)
  (*    | O => (victims#[$v$0]!Victim@."victim_line") *)
  (*    | S n' => *)
  (*      (IF (victims#[$v$n]!Victim@."victim_valid") *)
  (*       then victims#[$v$n]!Victim@."victim_line" *)
  (*       else getVictimFix victims n') *)
  (*    end)%kami_expr. *)

  (* Fixpoint getVictimF (var: Kind -> Type) *)
  (*          (victims: Expr var (SyntaxKind (Array VictimK numVictim))) *)
  (*   : Expr var (SyntaxKind LineWriteK) := *)
  (*   getVictimFix victims (numVictim - 1). *)

  (*!-- NEW DESIGN BELOW --*)

  (** Registers *)
  Definition irStageN: string := "irStage"+o.
  Definition irAddrN: string := "irAddr"+o.
  Definition irInfoN: string := "irLineWrite"+o.
  (* Definition writeStageN: string := "writeStage"+o. *)
  (* Definition writeLineWriteN: string := "writeLineWrite"+o. *)
  Definition mayVictimN: string := "mayVictim"+o.
  Definition victimsN: string := "victims"+o.
  Definition victimLineWriteN: string := "victimLineWrite"+o.
  Definition victimWayN: string := "victimWay"+o.

  (** Stages *)
  Definition InfoReadStage := Bit 2.
  Definition irNone {var}: Expr var (SyntaxKind InfoReadStage) := ($0)%kami_expr.
  Definition irRequested {var}: Expr var (SyntaxKind InfoReadStage) := ($1)%kami_expr.
  Definition irReady {var}: Expr var (SyntaxKind InfoReadStage) := ($2)%kami_expr.

  (* Definition WriteStage := Bit 3. *)
  (* Definition wsNone {var}: Expr var (SyntaxKind WriteStage) := ($0)%kami_expr. *)
  (* Definition wsRqAcc {var}: Expr var (SyntaxKind WriteStage) := ($1)%kami_expr. *)
  (* Definition wsRepRq {var}: Expr var (SyntaxKind WriteStage) := ($2)%kami_expr. *)
  (* Definition wsVictimRq {var}: Expr var (SyntaxKind WriteStage) := ($3)%kami_expr. *)
  (* Definition wsRsReady {var}: Expr var (SyntaxKind WriteStage) := ($7)%kami_expr. *)

  Definition ncid :=
    MODULE {
      Register irStageN: InfoReadStage <- Default
      with Register irAddrN: Bit addrSz <- Default
      with Register irInfoN: InfoReadK <- Default
      with Register mayVictimN: MayVictimK <- Default
      with Register victimsN: Array VictimK numVictim <- Default

      with Method infoReadRqN (addr: Bit addrSz): Void :=
        Read victims <- victimsN;
        victimIterA
          (#victims)%kami_expr (#addr)%kami_expr
          (fun _ victim =>
             (Write irStageN: InfoReadStage <- irReady;
             LET vline <- victim!Victim@."victim_line";
             Write irInfoN: InfoReadK <- STRUCT { "info_hit" ::= $$true;
                                                  (* [info_way] has no meaning for victim lines *)
                                                  "info_way" ::= $$Default;
                                                  "edir_hit" ::= $$false;
                                                  "edir_way" ::= $$Default;
                                                  "info" ::= victim!Victim@."victim_info"
                                                };
             Retv))
          (Write irStageN: InfoReadStage <- irRequested;
          Write irAddrN <- #addr;
          LET index <- getIndex _ addr;
          NCall makeInfoRdReqs index;
          NCall makeEDirRdReqs index;
          Retv)

      with Method infoReadRsN (): InfoReadK :=
        Read readStage: InfoReadStage <- irStageN;
        Assert (#readStage == irReady || #readStage == irRequested);
        Write irStageN: InfoReadStage <- irNone;
        If (#readStage == irReady)
        then (Read linfo: InfoReadK <- irInfoN; Ret #linfo)
        else (Read addr: Bit addrSz <- irAddrN;
             LET tag <- getTag _ addr;
             LET index <- getIndex _ addr;
             LET tis: Vector TagInfoK lgWay <- $$Default;
             NCall ntis <- makeInfoRdResps tis;
             LET itm <- doTagMatch _ tag ntis (Nat.pow 2 lgWay);

             If (#itm!(TagMatch infoK lgWay)@."tm_hit")
             then (* cache hit *)
               (LET linfo: InfoReadK <-
                           STRUCT { "info_hit" ::= #itm!(TagMatch infoK lgWay)@."tm_hit";
                                    "info_way" ::= #itm!(TagMatch infoK lgWay)@."tm_way";
                                    "edir_hit" ::= $$false;
                                    "edir_way" ::= $$Default;
                                    "info" ::= #itm!(TagMatch infoK lgWay)@."tm_value" };
               Ret #linfo)
             else (* cache miss *)
               (Call repWay <- repGet(#index);
               LET repTagInfo <- #ntis@[#repWay];
               LET repInfo <- #repTagInfo!(TagValue infoK)@."value";
               Write mayVictimN: MayVictimK <- STRUCT { "mv_index" ::= #index;
                                                        "mv_way" ::= #repWay;
                                                        "mv_info" ::= #repInfo;
                                                        (** will be updated in the next cycle *)
                                                        "mv_value" ::= $$Default };
               LET tes: Vector TagEDirK edirLgWay <- $$Default;
               NCall ntes <- makeEDirRdResps tes;
               LET etm <- doTagMatch _ tag ntes (Nat.pow 2 edirLgWay);
               LET edirV <- #etm!(TagMatch edirK edirLgWay)@."tm_value";
               LET linfo: InfoReadK <-
                          STRUCT { "info_hit" ::= $$false;
                                   (** On cache miss, provide a replacement candidate way *)
                                   "info_way" ::= #repWay;
                                   "edir_hit" ::= #etm!(TagMatch edirK edirLgWay)@."tm_hit";
                                   "edir_way" ::= #etm!(TagMatch edirK edirLgWay)@."tm_way";
                                   "info" ::= edirToInfo _ edirV };
               Ret #linfo)
             as linfo; Ret #linfo)
        as linfo; Ret #linfo

      with Method valueReadRqN (iw: IdxWayK): Void :=
        LET index <- #iw!IdxWay@."index";
        LET way <- #iw!IdxWay@."way";
        Call dataRdReq({#way, #index});
        Retv
      with Method valueReadRsN (): dataK :=
        Call value <- dataRdResp();
        Ret #value

      with Method victimValueRqN (): Void :=
        Read mayVictim: MayVictimK <- mayVictimN;
        LET vindex <- #mayVictim!MayVictim@."mv_index";
        LET vway <- #mayVictim!MayVictim@."mv_way";
        Call dataRdReq({#vway, #vindex});
        Retv
      with Method victimValueRsN (): Void :=
        Call value <- dataRdResp();
        Read mayVictim: MayVictimK <- mayVictimN;
        Write mayVictimN <- STRUCT { "mv_index" ::= #mayVictim!MayVictim@."mv_index";
                                     "mv_way" ::= #mayVictim!MayVictim@."mv_way";
                                     "mv_info" ::= #mayVictim!MayVictim@."mv_info";
                                     "mv_value" ::= #value };
        Retv
    }.

  (*!-- OLD STUFF BELOW --*)

  Definition cacheIfc :=
    MODULE {
      Register readStageN: ReadStage <- Default
      with Register readAddrN: Bit addrSz <- Default
      with Register readLineWriteN: LineWriteK <- Default
      with Register writeStageN: WriteStage <- Default
      with Register writeLineWriteN: LineWriteK <- Default
      with Register victimsN: Vector VictimK lgNumVictim <- Default
      with Register victimLineWriteN: LineWriteK <- Default
      with Register victimWayN: Bit lgWay <- Default

      with Method readRqN (addr: Bit addrSz): Void :=
        (** Do not allow reads when a write is in progress *)
        Read writeStage: WriteStage <- writeStageN;
        Assert (#writeStage == wsNone);
        Read readStage: ReadStage <- readStageN;
        Assert (#readStage == irNone);

        Read victims <- victimsN;
        victimIterA
          (#victims)%kami_expr (#addr)%kami_expr
          (fun _ victim => (Write readStageN: ReadStage <- rsRsReady;
                           Write readLineWriteN <- victim!Victim@."victim_line";
                           Retv))%kami_action
          (Write readStageN: ReadStage <- irRequested;
          Write readAddrN <- #addr;
          LET index <- getIndex _ addr;
          LET infoRq: Struct (BramRq indexSz TagInfoK) <- STRUCT { "write" ::= $$false;
                                                                   "addr" ::= #index;
                                                                   "datain" ::= $$Default };
          NCall callInfoReadRqs infoRq (Nat.pow 2 lgWay);
          Retv)%kami_action

      with Method readRsN (): LineWriteK :=
        Read readStage: ReadStage <- readStageN;
        Assert (#readStage == rsRsReady);
        Write readStageN: ReadStage <- irNone;
        Read line: Struct LineWrite <- readLineWriteN;
        Ret #line

      with Method writeRqN (line: LineWriteK): Void :=
        (** Do not allow writes when a read is in progress *)
        Read readStage: ReadStage <- readStageN;
        Assert (#readStage == irNone);
        Read writeStage: WriteStage <- writeStageN;
        Assert (#writeStage == wsNone);

        (* When writing to a victim which is not evicted yet, need to check
         * if the new victim is still evictable (by checking [evictF]).
         * If so, it's fine to overwrite the victim with the new value.
         * Otherwise, remove the victim (consider it released) and perform an
         * ordinary write. *)
        Read victims <- victimsN;
        LET evictable <- evictF (#line!LineWrite@."info");
        victimIterA
          (#victims)%kami_expr (#line!LineWrite@."addr")%kami_expr
          (fun vidx victim =>
             (LET mline <- updStruct (ls:= LineWrite) (#line)
                                     (LineWrite !! "info_hit") ($$false);
             Write writeStageN <- (IF #evictable then wsRsReady else wsRqAcc);
             Write writeLineWriteN <- #mline; (* meaningless when evictable *)
             Write victimsN <-
             #victims@[vidx <- STRUCT { "victim_valid" ::= #evictable;
                                        "victim_idx" ::= vidx;
                                        "victim_line" ::=
                                          #mline (* meaningless when not evictable *) }];
             Retv))%kami_action
          (Write writeStageN <- wsRqAcc;
          Write writeLineWriteN <- #line;
          Retv)%kami_action

      with Method writeRsN (): LineWriteK :=
        Read writeStage: WriteStage <- writeStageN;
        Assert (#writeStage == wsRsReady);
        Write writeStageN <- wsNone;
        Read nline: LineWriteK <- writeLineWriteN;
        Ret #nline

      with Method hasVictimN (): Bool :=
        Read victims <- victimsN;
        LET hasV <- hasVictimF #victims;
        Ret #hasV

      with Method getVictimN (): LineWriteK :=
        Read victims <- victimsN;
        Assert (hasVictimF #victims);
        LET victim <- getVictimF #victims;
        Ret #victim

      with Method removeVictimN (addr: Bit addrSz): Void :=
        Read victims: Vector VictimK lgNumVictim <- victimsN;
        victimIterA
          (#victims)%kami_expr (#addr)%kami_expr
          (fun vidx _ => (Write victimsN <- #victims@[vidx <- $$Default]; Retv))
          Retv

      with Rule "read_tagmatch"+o :=
        Read readStage: ReadStage <- readStageN;
        Assert (#readStage == irRequested);
        Read addr: Bit addrSz <- readAddrN;
        LET tag <- getTag _ addr;
        LET index <- getIndex _ addr;

        LET tis: Vector TagInfoK lgWay <- $$Default;
        NCall ntis <- callInfoReadRss tis (Nat.pow 2 lgWay);
        LET itm <- doTagMatch _ tag ntis (Nat.pow 2 lgWay);

        Write readLineWriteN: Struct LineWrite <-
          STRUCT { "addr" ::= #addr;
                   "info_hit" ::= #itm!(TagMatch infoK lgWay)@."tm_hit";
                   "info_way" ::= #itm!(TagMatch infoK lgWay)@."tm_way";
                   "info_write" ::= $$false;
                   "info" ::= #itm!(TagMatch infoK lgWay)@."tm_value";
                   "value_write" ::= $$false;
                   "value" ::= $$Default (* if info-hit, then will have it next cycle *) };

        If (#itm!(TagMatch infoK lgWay)@."tm_hit")
        then (Write readStageN: ReadStage <- rsValueRq;
             Call dataPutRq (STRUCT { "write" ::= $$false;
                                      "addr" ::= {#itm!(TagMatch infoK lgWay)@."tm_way", #index};
                                      "datain" ::= $$Default });
             Retv)
        else (Write readStageN: ReadStage <- rsRsReady; Retv);
        Retv

      with Rule "read_data"+o :=
        Read readStage: ReadStage <- readStageN;
        Assert (#readStage == rsValueRq);
        Write readStageN: ReadStage <- rsRsReady;
        Call data <- dataGetRs();
        Read line: Struct LineWrite <- readLineWriteN;
        Write readLineWriteN: Struct LineWrite <-
          STRUCT { "addr" ::= #line!LineWrite@."addr";
                   "info_hit" ::= #line!LineWrite@."info_hit";
                   "info_way" ::= #line!LineWrite@."info_way";
                   "info_write" ::= #line!LineWrite@."info_write";
                   "info" ::= #line!LineWrite@."info";
                   "value_write" ::= $$false;
                   "value" ::= #data };
        Retv

      with Rule "write_info_hit"+o :=
        (* No need to update [writeLineWriteN], which will serve as information
         * for the new line as well, since it is already the up-to-date info. *)
        Read writeStage: WriteStage <- writeStageN;
        Assert (#writeStage == wsRqAcc);
        Read line: Struct LineWrite <- writeLineWriteN;
        Assert (#line!LineWrite@."info_hit");
        Write writeStageN <- wsRsReady;

        LET addr <- #line!LineWrite@."addr";
        LET tag <- getTag _ addr;
        LET index <- getIndex _ addr;
        LET way <- #line!LineWrite@."info_way";

        (* request write for the new line *)
        If (#line!LineWrite@."info_write")
        then (LET rq: Struct (BramRq indexSz TagInfoK) <-
                      STRUCT { "write" ::= $$true;
                               "addr" ::= #index;
                               "datain" ::=
                                 STRUCT { "tag" ::= #tag;
                                          "value" ::= #line!LineWrite@."info" } };
             NCall infoPutRqW way rq; Retv);

        If (#line!LineWrite@."value_write")
        then (Call dataPutRq (
                     STRUCT { "write" ::= $$true;
                              "addr" ::= {#way, #index};
                              "datain" ::= #line!LineWrite@."value" }); Retv);
        Retv

      with Rule "write_info_miss_rep_rq"+o :=
        Read writeStage: WriteStage <- writeStageN;
        Assert (#writeStage == wsRqAcc);
        Read line: Struct LineWrite <- writeLineWriteN;
        Assert (!(#line!LineWrite@."info_hit"));
        Write writeStageN <- wsRepRq;

        LET addr <- #line!LineWrite@."addr";
        LET index <- getIndex _ addr;

        LET infoRq: Struct (BramRq indexSz TagInfoK) <- STRUCT { "write" ::= $$false;
                                                                 "addr" ::= #index;
                                                                 "datain" ::= $$Default };
        NCall callInfoReadRqs infoRq (Nat.pow 2 lgWay);
        Retv

      with Rule "write_info_miss_rep_rs"+o :=
        Read writeStage: WriteStage <- writeStageN;
        Assert (#writeStage == wsRepRq);
        Write writeStageN <- wsVictimRq;

        LET tis: Vector TagInfoK lgWay <- $$Default;
        NCall ntis <- callInfoReadRss tis (Nat.pow 2 lgWay);
        LET victimWay <- findLineWrite _ ntis (Nat.pow 2 lgWay);

        Read line: Struct LineWrite <- writeLineWriteN;
        LET addr <- #line!LineWrite@."addr";
        LET index <- getIndex _ addr;

        LET vtid <- #ntis@[#victimWay];
        LET vtag <- #vtid!(TagValue infoK)@."tag";
        LET vinfo <- #vtid!(TagValue infoK)@."value";

        Write victimWayN <- #victimWay;
        Write victimLineWriteN: LineWriteK <- STRUCT { "addr" ::= buildAddr _ vtag index;
                                                  "info_hit" ::= $$false;
                                                  "info_way" ::= $$Default;
                                                  "info_write" ::= $$false;
                                                  "info" ::= #vinfo;
                                                  "value_write" ::= $$false;
                                                  "value" ::= $$Default };
        Call dataPutRq (STRUCT { "write" ::= $$false;
                                 "addr" ::= {#victimWay, #index};
                                 "datain" ::= $$Default });
        Retv

      with Rule "write_victim_rs"+o :=
        Read writeStage: WriteStage <- writeStageN;
        Assert (#writeStage == wsVictimRq);
        Read line: Struct LineWrite <- writeLineWriteN;
        Write writeStageN <- wsRsReady;

        LET addr <- #line!LineWrite@."addr";
        LET tag <- getTag _ addr;
        LET index <- getIndex _ addr;
        Read way <- victimWayN;

        (** Handle the responses about the victim line *)
        Read victims <- victimsN;
        Assert (hasVictimSlotF #victims);
        LET slotIdx <- getVictimSlotF #victims;
        Call vdata <- dataGetRs ();
        Read victim: LineWriteK <- victimLineWriteN;
        Write victimsN <-
        #victims@[#slotIdx <-
                  STRUCT { "victim_valid" ::= $$true;
                           "victim_idx" ::= #slotIdx;
                           "victim_line" ::=
                             STRUCT { "addr" ::= #victim!LineWrite@."addr";
                                      "info_hit" ::= #victim!LineWrite@."info_hit";
                                      "info_way" ::= #victim!LineWrite@."info_way";
                                      "info_write" ::= #victim!LineWrite@."info_write";
                                      "info" ::= #victim!LineWrite@."info";
                                      "value_write" ::= $$false;
                                      "value" ::= #vdata } }];

        (* Should update [writeLineWriteN], which will serve as information
         * for the new line, with the up-to-date info.
         * Note that "info_write", "value_write", and "value" can be assigned to
         * arbitrary values, since it will be updated after the bypass. *)
        Write writeLineWriteN: LineWriteK <- STRUCT { "addr" ::= #addr;
                                                 "info_hit" ::= $$true; (* MUST be true! *)
                                                 "info_way" ::= #way; (* MUST be the new way *)
                                                 "info_write" ::= $$false;
                                                 "info" ::= #line!LineWrite@."info";
                                                 "value_write" ::= $$false;
                                                 "value" ::= #line!LineWrite@."value" };

        (** request write for the new line; TODO: code duplicated with above *)
        If (#line!LineWrite@."info_write")
        then (LET rq: Struct (BramRq indexSz TagInfoK) <-
                      STRUCT { "write" ::= $$true;
                               "addr" ::= #index;
                               "datain" ::=
                                 STRUCT { "tag" ::= #tag;
                                          "value" ::= #line!LineWrite@."info" } };
             NCall infoPutRqW way rq; Retv);
        If (#line!LineWrite@."value_write")
        then (Call dataPutRq (
                     STRUCT { "write" ::= $$true;
                              "addr" ::= {#way, #index};
                              "datain" ::= #line!LineWrite@."value" }); Retv);
        Retv
    }.

  Fixpoint infoRams (w: nat) :=
    match w with
    | O => infoRam O
    | S w' => (infoRam w ++ infoRams w')%kami
    end.

  Definition cache :=
    (cacheIfc ++ infoRams (Nat.pow 2 lgWay - 1) ++ dataRam)%kami.

End IncCache.
