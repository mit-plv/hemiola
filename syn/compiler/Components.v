Require Import Numbers.DecimalString.

Require Import Hemiola.Common Hemiola.Index Hemiola.Ex.TopoTemplate.
Require Import Compiler.HemiolaDeep. (* source *)
Require Import Kami.Kami. (* target *)

Set Implicit Arguments.

Notation "'NCall' v <- f ; cont" :=
  (f (fun v => cont%kami_action))
    (at level 12, right associativity, v at level 15, f at level 15, only parsing): kami_action_scope.
Notation "'NCall' f ; cont" :=
  (f cont%kami_action)
    (at level 12, right associativity, f at level 15, only parsing): kami_action_scope.

Notation "'NCall2' v1 , v2 <- f ; cont" :=
  (f (fun v1 v2 => cont%kami_action))
    (at level 12, right associativity, v1 at level 15, v2 at level 15, f at level 15, only parsing): kami_action_scope.

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
            (infoK edirK valueK: Kind)
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

  Fixpoint makeInfoWrReqsFix (var: Kind -> Type)
           (way: var (Bit lgWay))
           (rq: var (Struct (BramWriteReq indexSz TagInfoK)))
           (n: nat) (cont: ActionT var Void): ActionT var Void :=
    match n with
    | O => cont
    | S n' =>
      (If (#way == $(Nat.pow 2 lgWay - n))
       then (Call (infoWrReq (Nat.pow 2 lgWay - n))(#rq); Retv);
       makeInfoWrReqsFix way rq n' cont)%kami_action
    end.
  Definition makeInfoWrReqs (var: Kind -> Type)
             (way: var (Bit lgWay))
             (rq: var (Struct (BramWriteReq indexSz TagInfoK)))
             (cont: ActionT var Void): ActionT var Void :=
    makeInfoWrReqsFix way rq (Nat.pow 2 lgWay) cont.

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

  Fixpoint makeEDirWrReqsFix (var: Kind -> Type)
           (way: var (Bit edirLgWay))
           (rq: var (Struct (BramWriteReq indexSz TagEDirK)))
           (n: nat) (cont: ActionT var Void): ActionT var Void :=
    match n with
    | O => cont
    | S n' =>
      (If (#way == $(Nat.pow 2 edirLgWay - n))
       then (Call (edirWrReq (Nat.pow 2 edirLgWay - n))(#rq); Retv);
       makeEDirWrReqsFix way rq n' cont)%kami_action
    end.
  Definition makeEDirWrReqs (var: Kind -> Type)
             (way: var (Bit edirLgWay))
             (rq: var (Struct (BramWriteReq indexSz TagEDirK)))
             (cont: ActionT var Void): ActionT var Void :=
    makeEDirWrReqsFix way rq (Nat.pow 2 edirLgWay) cont.

  (** Data cache *)

  Definition dataIndexSz := indexSz + lgWay.
  Definition dataRamN: string := "dataRam"+o.
  Definition dataRam := bram2 dataRamN dataIndexSz valueK.
  Definition dataRdReq := MethodSig (dataRamN -- "rdReq") (Bit dataIndexSz): Void.
  Definition dataRdResp := MethodSig (dataRamN -- "rdResp") (): valueK.
  Definition dataWrReq :=
    MethodSig (dataRamN -- "wrReq") (Struct (BramWriteReq dataIndexSz valueK)): Void.

  (** Replacement cache *)

  Definition repCntSz := 8.
  Definition RepCntK := Bit repCntSz.
  Definition repRamN := "repRam"+o.
  Let repK := Vector RepCntK lgWay.
  Definition repRam := bram2 repRamN indexSz repK.
  Definition repRdReq := MethodSig (repRamN -- "rdReq") (Bit indexSz): Void.
  Definition repRdResp := MethodSig (repRamN -- "rdResp") (): repK.
  Definition repWrReq :=
    MethodSig (repRamN -- "wrReq") (Struct (BramWriteReq indexSz repK)): Void.

  Fixpoint incRepsFix (var: Kind -> Type)
           (reps: var (Vector RepCntK lgWay))
           (n: nat) {retK} (cont: var (Vector RepCntK lgWay) -> ActionT var retK): ActionT var retK :=
    (match n with
     | O => cont reps
     | S n' => (LET irep <- #reps@[$n'] +
                            (IF (#reps@[$n'] == $0 || #reps@[$n'] == $(Nat.pow 2 repCntSz - 1))
                             then $0 else $1);
               LET nreps <- #reps@[$n' <- #irep];
               incRepsFix nreps n' cont)
     end)%kami_action.
  Definition incReps (var: Kind -> Type)
             (reps: var (Vector RepCntK lgWay))
             {retK} (cont: var (Vector RepCntK lgWay) -> ActionT var retK): ActionT var retK :=
    incRepsFix reps (Nat.pow 2 lgWay) cont.

  Fixpoint getRepWayFix (var: Kind -> Type)
           (maxWay: var (Bit lgWay)) (maxAge: var RepCntK)
           (reps: var (Vector RepCntK lgWay))
           (n: nat) {retK} (cont: var (Bit lgWay) -> var RepCntK -> ActionT var retK):
    ActionT var retK :=
    (match n with
     | O => cont maxWay maxAge
     | S n' => (LET nmaxWay <- IF (#maxAge <= #reps@[$n']) then $n' else #maxWay;
               LET nmaxAge <- IF (#maxAge <= #reps@[$n']) then #reps@[$n'] else #maxAge;
               getRepWayFix nmaxWay nmaxAge reps n' cont)
     end)%kami_action.
  Definition getRepWay (var: Kind -> Type)
             (maxWay: var (Bit lgWay)) (maxAge: var RepCntK)
             (reps: var (Vector RepCntK lgWay))
             {retK} (cont: var (Bit lgWay) -> var RepCntK -> ActionT var retK): ActionT var retK :=
    getRepWayFix maxWay maxAge reps (Nat.pow 2 lgWay) cont.

  Definition AccType := Bit 1.
  Definition accTouch {var}: Expr var (SyntaxKind AccType) := ($0)%kami_expr.
  Definition accInvalid {var}: Expr var (SyntaxKind AccType) := ($1)%kami_expr.
  Definition AccessRec :=
    STRUCT { "acc_type" :: AccType;
             "acc_reps" :: repK;
             "acc_index" :: Bit indexSz;
             "acc_way" :: Bit lgWay
           }.
  Let AccessRecK := Struct AccessRec.

  Definition repGetRqN := "repGetRq"+o.
  Definition repGetRq := MethodSig repGetRqN(Bit indexSz): Void.
  Definition repGetRsN := "repGetRs"+o.
  Definition repGetRs := MethodSig repGetRsN(): repK.
  Definition repAccessN := "repAccess"+o.
  Definition repAccess := MethodSig repAccessN(AccessRecK): Void.

  Definition repLRU :=
    MODULE {
      Method repGetRqN(index: Bit indexSz): Void :=
        Call repRdReq(#index); Retv
      with Method repGetRsN(): repK :=
        Call reps <- repRdResp(); Ret #reps
      with Method repAccessN(acc: AccessRecK): Void :=
        LET reps <- #acc!AccessRec@."acc_reps";
        NCall ireps <- incReps reps;
        If (#acc!AccessRec@."acc_type" == accTouch)
        then (LET nreps <- #ireps@[#acc!AccessRec@."acc_way" <- $1]; Ret #nreps)
        else (LET nreps <- #ireps@[#acc!AccessRec@."acc_way" <- $(Nat.pow 2 repCntSz - 1)];
             Ret #nreps)
        as nreps;
        LET app <- STRUCT { "addr" ::= #acc!AccessRec@."acc_index";
                            "datain" ::= #nreps };
        Call repWrReq(#app);
        Retv
    }.

  Definition rep := (repLRU ++ repRam)%kami.

  (** Pipe from the first stage *)
  Let MviK := Maybe (Bit victimIdxSz).
  Definition cp1 :=
    STRUCT { "tag" :: Bit tagSz;
             "index" :: Bit indexSz;
             "victim_found" :: MviK }.
  Let cpK1 := Struct cp1.
  Definition cpN1 := "cp_1"+o.
  Definition cpipe1 := fifo primPipelineFifoName cpN1 cpK1.
  Definition cpEnq1 := MethodSig (cpN1 -- "enq") (cpK1): Void.
  Definition cpDeq1 := MethodSig (cpN1 -- "deq") (): cpK1.

  (** Pipe from the second stage *)
  Definition MayVictim :=
    STRUCT { "mv_index" :: Bit indexSz;
             "mv_way" :: Bit lgWay;
             "mv_info" :: infoK }.
  Let MayVictimK := Struct MayVictim.

  Definition cp2 :=
    STRUCT { "victim_found" :: MviK; "may_victim" :: MayVictimK }.
  Let cpK2 := Struct cp2.
  Definition cpN2 := "cp_2"+o.
  Definition cpipe2 := fifo primPipelineFifoName cpN2 cpK2.
  Definition cpEnq2 := MethodSig (cpN2 -- "enq") (cpK2): Void.
  Definition cpDeq2 := MethodSig (cpN2 -- "deq") (): cpK2.

  (*! Public interface for the info/value caches *)

  Definition InfoRead :=
    STRUCT { "info_index" :: Bit indexSz;
             "info_hit" :: Bool;
             "info_way" :: Bit lgWay; (* a replaceable way, if miss *)
             "edir_hit" :: Bool;
             "edir_way" :: Bit edirLgWay;
             "edir_slot" :: Maybe (Bit edirLgWay);
             "info" :: infoK
           }.
  Let InfoReadK := Struct InfoRead.

  Definition cacheN: string := "cache"+o.

  (** Stage 1: request to read information *)
  Definition infoRqN: string := cacheN _++ "infoRq".
  Definition infoRq := MethodSig infoRqN (Bit addrSz): Void.

  (** Stage 2: get the information response, and
   * - on cache hit: request to read the value.
   * - on cache miss: hold the victim information and request to read the victim value. *)
  Definition infoRsValueRqN: string := cacheN _++ "infoRsValueRq".
  Definition infoRsValueRq := MethodSig infoRsValueRqN (): InfoReadK.

  (** Stage 3: get the value response and request to write information/value. *)
  Definition LineWrite :=
    STRUCT { "addr" :: Bit addrSz;
             "info_write" :: Bool;
             "info_hit" :: Bool;
             "info_way" :: Bit lgWay;
             "edir_hit" :: Bool;
             "edir_way" :: Bit edirLgWay;
             "edir_slot" :: Maybe (Bit edirLgWay);
             "info" :: infoK;
             "value_write" :: Bool;
             "value" :: valueK
           }.
  Let LineWriteK := Struct LineWrite.

  (* NOTE: this design implies that there is no case of read-and-modify for values. *)
  Definition valueRsLineRqN: string := cacheN _++ "valueRsLineRq".
  Definition valueRsLineRq := MethodSig valueRsLineRqN (LineWriteK): valueK.

  Definition Victim :=
    STRUCT { "victim_valid" :: Bool;
             "victim_addr" :: Bit addrSz;
             "victim_info" :: infoK;
             "victim_value" :: valueK }.
  Let VictimK := Struct Victim.

  Definition VictimWrite :=
    STRUCT { "vw_index" :: Bit victimIdxSz;
             "vw_victim" :: VictimK }.
  Let VictimWriteK := Struct VictimWrite.

  Definition victimWriteN: string := cacheN _++ "victimWrite".
  Definition victimWrite := MethodSig victimWriteN (VictimWriteK): Void.

  (* Definition getVictimN: string := cacheN _++ "getVictim". *)
  (* Definition getVictim := MethodSig getVictimN (): VictimK. *)
  (* Definition removeVictimN: string := cacheN _++ "removeVictim". *)
  (* Definition removeVictim := MethodSig removeVictimN (Bit addrSz): Void. *)

  (*! -- public interface ends here *)

  Variables (getIndex: forall ty, fullType ty (SyntaxKind (Bit addrSz)) ->
                                  Expr ty (SyntaxKind (Bit indexSz)))
            (getTag: forall ty, fullType ty (SyntaxKind (Bit addrSz)) ->
                                Expr ty (SyntaxKind (Bit tagSz)))
            (* (buildAddr: forall ty, fullType ty (SyntaxKind (Bit tagSz)) -> *)
            (*                        fullType ty (SyntaxKind (Bit indexSz)) -> *)
            (*                        Expr ty (SyntaxKind (Bit addrSz))) *)
            (edirToInfo: forall ty, fullType ty (SyntaxKind edirK) ->
                                    Expr ty (SyntaxKind infoK))
            (edirFromInfo: forall ty, fullType ty (SyntaxKind infoK) -> Expr ty (SyntaxKind edirK))
            (isJustDir: forall ty, fullType ty (SyntaxKind infoK) -> Expr ty (SyntaxKind Bool))
            (edirEmptySlot: forall ty, Expr ty (SyntaxKind edirK) -> Expr ty (SyntaxKind Bool)).

  Arguments getIndex {_}.
  Arguments getTag {_}.
  Arguments edirToInfo {_}.
  Arguments edirFromInfo {_}.
  Arguments isJustDir {_}.

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

  Fixpoint edirFindEmptySlot (var: Kind -> Type)
           (tags: var (Vector TagEDirK edirLgWay))
           (n: nat): Expr var (SyntaxKind (Maybe (Bit edirLgWay))) :=
    (match n with
     | O => MaybeNone
     | S n' =>
       (IF (edirEmptySlot (#tags@[$(Nat.pow 2 edirLgWay - n)]!(TagValue edirK)@."value"))
        then (MaybeSome ($(Nat.pow 2 edirLgWay - n)))
        else (edirFindEmptySlot _ tags n'))
     end)%kami_expr.

  (** Victim lines *)

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
      (LET victim: VictimK <- victims#[$v$(numVictim - n)];
      If ((#victim!Victim@."victim_valid")
          && #victim!Victim@."victim_addr" == addr)
       then (readF (numVictim - n) (#victim)%kami_expr)
       else (victimIterAFix victims addr readF cont n'); Retv)%kami_action
    end.

  Definition victimIterA (var: Kind -> Type)
             (victims: Expr var (SyntaxKind (Array VictimK numVictim)))
             (addr: Expr var (SyntaxKind (Bit addrSz)))
             (readF: nat -> Expr var (SyntaxKind VictimK) -> ActionT var Void)
             (cont: ActionT var Void): ActionT var Void :=
    victimIterAFix victims addr readF cont numVictim.

  Fixpoint hasVictimSlotFix (var: Kind -> Type)
           (victims: Expr var (SyntaxKind (Array VictimK numVictim)))
           (n: nat): Expr var (SyntaxKind Bool) :=
    (match n with
     | O => !(victims#[$v$0]!Victim@."victim_valid")
     | S n' =>
       ((!(victims#[$v$n]!Victim@."victim_valid")) || hasVictimSlotFix victims n')
     end)%kami_expr.
  Definition hasVictimSlot (var: Kind -> Type)
             (victims: Expr var (SyntaxKind (Array VictimK numVictim)))
    : Expr var (SyntaxKind Bool) :=
    hasVictimSlotFix victims (numVictim - 1).

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

  (** Registers *)
  Definition victimsN: string := "victims"+o.

  Definition cacheIfc :=
    MODULE {
      Register victimsN: Array VictimK numVictim <- Default

      with Method infoRqN (addr: Bit addrSz): Void :=
        Read victims <- victimsN;
        victimIterA
          (#victims)%kami_expr (#addr)%kami_expr
          (fun i _ =>
             (Call cpEnq1(STRUCT { "tag" ::= getTag addr;
                                   "index" ::= getIndex addr;
                                   "victim_found" ::= MaybeSome ($i) });
             Retv))
          (LET index <- getIndex addr;
          NCall makeInfoRdReqs index;
          NCall makeEDirRdReqs index;
          Call repGetRq(#index);
          Call cpEnq1(STRUCT { "tag" ::= getTag addr;
                               "index" ::= getIndex addr;
                               "victim_found" ::= MaybeNone });
          Retv)

      with Method infoRsValueRqN (): InfoReadK :=
        Call cpipe <- cpDeq1();
        LET tag <- #cpipe!cp1@."tag";
        LET index <- #cpipe!cp1@."index";
        If (#cpipe!cp1@."victim_found"!(MaybeStr (Bit victimIdxSz))@."valid")
        then (LET vi <- #cpipe!cp1@."victim_found"!(MaybeStr (Bit victimIdxSz))@."data";
             Read victims <- victimsN;
             LET victim <- #victims@[#vi];
             LET linfo: InfoReadK <- STRUCT { "info_index" ::= #index;
                                              "info_hit" ::= $$true;
                                              (* [info_way] has no meaning for victim lines *)
                                              "info_way" ::= $$Default;
                                              "edir_hit" ::= $$false;
                                              "edir_way" ::= $$Default;
                                              "edir_slot" ::= MaybeNone;
                                              "info" ::= #victim!Victim@."victim_info"
                                            };
             Call cpEnq2(STRUCT { "victim_found" ::= #cpipe!cp1@."victim_found";
                                  "may_victim" ::= $$Default });
             Ret #linfo)
        else (LET tis: Vector TagInfoK lgWay <- $$Default;
             NCall ntis <- makeInfoRdResps tis;
             LET itm <- doTagMatch _ tag ntis (Nat.pow 2 lgWay);

             LET tes: Vector TagEDirK edirLgWay <- $$Default;
             NCall ntes <- makeEDirRdResps tes;
             LET etm <- doTagMatch _ tag ntes (Nat.pow 2 edirLgWay);
             LET edirV <- #etm!(TagMatch edirK edirLgWay)@."tm_value";
             LET ees <- edirFindEmptySlot _ ntes (Nat.pow 2 edirLgWay);

             Call reps <- repGetRs();
             LET maxWay: Bit lgWay <- $$Default;
             LET maxAge: RepCntK <- $$Default;
             NCall2 repWay, _ <- getRepWay maxWay maxAge reps;

             LET linfo: InfoReadK <-
                        STRUCT { "info_index" ::= #index;
                                 "info_hit" ::= #itm!(TagMatch infoK lgWay)@."tm_hit";
                                 "info_way" ::= #itm!(TagMatch infoK lgWay)@."tm_way";
                                 "edir_hit" ::= #etm!(TagMatch edirK edirLgWay)@."tm_hit";
                                 "edir_way" ::= #etm!(TagMatch edirK edirLgWay)@."tm_way";
                                 "edir_slot" ::= #ees;
                                 "info" ::=
                                   (IF (#itm!(TagMatch infoK lgWay)@."tm_hit")
                                    then (#itm!(TagMatch infoK lgWay)@."tm_value")
                                    else (edirToInfo edirV)) };

             LET repTagInfo <- #ntis@[#repWay];
             LET repInfo <- #repTagInfo!(TagValue infoK)@."value";
             Call cpEnq2(STRUCT { "victim_found" ::= MaybeNone;
                                  "may_victim" ::=
                                    STRUCT { "mv_index" ::= #index;
                                             "mv_way" ::= #repWay;
                                             "mv_info" ::= #repInfo } });
             (** On cache hit, request the line value; otherwise, request the victim line value. *)
             Call dataRdReq({(IF (#itm!(TagMatch infoK lgWay)@."tm_hit")
                              then (#itm!(TagMatch infoK lgWay)@."tm_way")
                              else #repWay), #index});
             Ret #linfo)
        as linfo; Ret #linfo

      (** Cache-write cases:
       * 1) info-hit and info-write: trivial
       * 2) info-miss and edir-hit
       * 2-1) info write: just write it (the victim line is already fetched)
       *          and invalidate the edir line.
       * 2-2) edir write: just write it (BUT this case may never happen).
       * 3) info miss and edir miss
       * 3-1) info write: just write it
       * 3-2) edir write: write to edir if there's an empty slot, otherwise to the info cache.
       *)
      with Method valueRsLineRqN (lw: LineWriteK): valueK :=
        Call cpipe <- cpDeq2();
        If (#cpipe!cp2@."victim_found"!(MaybeStr (Bit victimIdxSz))@."valid")
        then (Read victims: Array VictimK numVictim <- victimsN;
             LET vi <- #cpipe!cp2@."victim_found"!(MaybeStr (Bit victimIdxSz))@."data";
             LET pv <- #victims#[#vi];
             LET nv: VictimK <- STRUCT { "victim_valid" ::= $$true;
                                         "victim_addr" ::= #pv!Victim@."victim_addr";
                                         "victim_info" ::=
                                           (IF (#lw!LineWrite@."info_write")
                                            then (#lw!LineWrite@."info")
                                            else (#pv!Victim@."victim_info"));
                                         "victim_value" ::=
                                           (IF (#lw!LineWrite@."value_write")
                                            then (#lw!LineWrite@."value")
                                            else (#pv!Victim@."victim_value")) };
             Write victimsN <- #victims#[#vi <- #nv];
             Ret (#pv!Victim@."victim_value"))
      else (Call value <- dataRdResp();
           LET mv <- #cpipe!cp2@."may_victim";
           LET addr <- #lw!LineWrite@."addr";
           LET info_way <- #lw!LineWrite@."info_way";
           LET ninfo <- #lw!LineWrite@."info";
           LET justDir <- isJustDir ninfo;

           (** * TODO: register [MayVictim] to the victim lines accordingly. *)

           (** traditional cache-line write *)
           If ((#lw!LineWrite@."info_hit") ||
               (!#justDir) ||
               ((!(#lw!LineWrite@."edir_hit")) && #justDir))
           then (If (#lw!LineWrite@."info_write")
                 then (LET irq <- STRUCT { "addr" ::= getIndex addr;
                                           "datain" ::=
                                             STRUCT { "tag" ::= getTag addr;
                                                      "value" ::= #ninfo } };
                      NCall makeInfoWrReqs info_way irq; Retv);
                 If (#lw!LineWrite@."value_write")
                 then (LET drq <- STRUCT { "addr" ::= {#info_way, getIndex addr};
                                           "datain" ::= #lw!LineWrite@."value" };
                      Call dataWrReq(#drq); Retv);
                 Retv);

           If (#lw!LineWrite@."info_write" && #lw!LineWrite@."edir_hit")
           then (LET edir_way <- #lw!LineWrite@."edir_way";
                (** When writing new information and extended-directory hit:
                 * 1) update the line if the new information is just about directory, or
                 * 2) invalidate the line if the new information is updating something more;
                 *    the new information is updated in the traditional cache (i.e., migration). *)
                LET erq <- STRUCT { "addr" ::= getIndex addr;
                                    "datain" ::=
                                      STRUCT { "tag" ::= getTag addr;
                                               "value" ::= (IF #justDir
                                                            then (edirFromInfo ninfo)
                                                            else $$Default) } };
                NCall makeEDirWrReqs edir_way erq; Retv)
           else (** If the information is just about directory and an empty slot exists,
                 * register the line to the extended directory. *)
             (LET mes <- #lw!LineWrite@."edir_slot";
             If ((!(#lw!LineWrite@."edir_hit")) &&
                 (#mes!(MaybeStr (Bit edirLgWay))@."valid") &&
                 #justDir)
              then (LET edir_way <- #mes!(MaybeStr (Bit edirLgWay))@."data";
                   LET erq <- STRUCT { "addr" ::= getIndex addr;
                                       "datain" ::=
                                         STRUCT { "tag" ::= getTag addr;
                                                  "value" ::= edirFromInfo ninfo } };
                   NCall makeEDirWrReqs edir_way erq; Retv); Retv);
           Ret #value)
      as pval;
      Ret #pval
  }.

  Fixpoint infoRams (w: nat) :=
    match w with
    | O => infoRam O
    | S w' => (infoRam w ++ infoRams w')%kami
    end.

  Fixpoint edirRams (w: nat) :=
    match w with
    | O => edirRam O
    | S w' => (edirRam w ++ edirRams w')%kami
    end.

  Definition ncid :=
    (cacheIfc
       ++ (cpipe1 ++ cpipe2)
       ++ infoRams (Nat.pow 2 lgWay - 1)
       ++ edirRams (Nat.pow 2 edirLgWay - 1)
       ++ dataRam
       ++ rep)%kami.

End NCID.
