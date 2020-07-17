Require Import Numbers.DecimalString.

Require Import Hemiola.Common Hemiola.Index Hemiola.Ex.TopoTemplate.
Require Import Compiler.HemiolaDeep. (* source *)
Require Import Kami.Lib.Struct Kami Kami.PrimFifo Kami.PrimBram. (* target *)

Set Implicit Arguments.

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

  Variable numPRqs numCRqs slotSz: nat.
  Let numSlots := S (numPRqs + numCRqs - 1).
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

  (** TODO: move to Kami *)
  Notation "v '#[' idx <- val ] " := (UpdateArray v idx val) (at level 10) : kami_expr_scope.

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

Section Cache.
  Variables (oidx: IdxT)
            (* MSB                                  LSB
             * |----------------(addr)----------------|
             * |--(tag)--|--(index)--|---|--(offset)--|
             * |---------|--(dataIndex)--|------------|
             *              (= index + lgWay)
             *)
            (tagSz indexSz offsetSz addrSz: nat)
            (lgWay lgNumVictim: nat)
            (infoK dataK: Kind).

  Local Notation "s '+o'" := (s ++ "_" ++ idx_to_string oidx)%string (at level 60).
  Local Notation "s1 _++ s2" := (s1 ++ "_" ++ s2)%string (at level 60).

  Definition TagValue (valueK: Kind) :=
    STRUCT { "tag" :: Bit tagSz; "value" :: valueK }.

  (** The information (= ownership bit + status + dir) cache *)
  Definition TagInfo := TagValue infoK.
  Definition TagInfoK := Struct TagInfo.

  Definition infoRamN (way: nat): string :=
    "infoRam"+o _++ nat_to_string way.
  Definition infoRam (way: nat) := bram1 (infoRamN way) indexSz TagInfoK.
  Definition infoPutRq (way: nat) :=
    MethodSig ((infoRamN way) -- "putRq")(Struct (BramRq indexSz TagInfoK)): Void.
  Definition infoGetRs (way: nat) :=
    MethodSig ((infoRamN way) -- "getRs")(): TagInfoK.

  (** The data cache *)
  Definition dataIndexSz := lgWay + indexSz.
  Definition dataRamN: string := "dataRam"+o.
  Definition dataRam := bram1 dataRamN dataIndexSz dataK.
  Definition dataPutRq :=
    MethodSig (dataRamN -- "putRq")
              (Struct (BramRq dataIndexSz dataK)): Void.
  Definition dataGetRs :=
    MethodSig (dataRamN -- "getRs")(): dataK.

  (*! Public interface for the info/data caches *)

  Definition cacheN: string := "cache"+o.
  Definition CacheLine :=
    STRUCT { "addr" :: Bit addrSz; (* This [addr] field might not be used at all
                                    * for read responses, but used when requesting
                                    * write. At least we need to know the index
                                    * (where to put the value), but when not hit,
                                    * we need the entire address.
                                    *)
             "info_hit" :: Bool;
             "info_way" :: Bit lgWay;
             "info_write" :: Bool; (* is this struct used for writing info? *)
             "info" :: infoK;
             "value_write" :: Bool; (* used for writing a value? *)
             "value" :: dataK (* [info_hit] implies value-hit *)
           }.
  Definition CacheLineK := Struct CacheLine.

  Definition readRqN: string := cacheN _++ "readRq".
  Definition readRq := MethodSig readRqN (Bit addrSz): Void.
  Definition readRsN: string := cacheN _++ "readRs".
  Definition readRs := MethodSig readRsN (): CacheLineK.

  Definition writeRqN: string := cacheN _++ "writeRq".
  Definition writeRq := MethodSig writeRqN (CacheLineK): Void.
  Definition writeRsN: string := cacheN _++ "writeRs".
  Definition writeRs := MethodSig writeRsN (): CacheLineK.

  Definition hasVictimN: string := cacheN _++ "hasVictimSlot".
  Definition hasVictim := MethodSig hasVictimN (): Bool.

  Definition Victim :=
    STRUCT { "victim_valid" :: Bool;
             "victim_idx" :: Bit lgNumVictim;
             "victim_line" :: CacheLineK }.
  Definition VictimK := Struct Victim.

  (* Always pick a first-found victim; check if it makes starvation of eviction *)
  Definition getVictimN: string := cacheN _++ "getVictim".
  Definition getVictim := MethodSig getVictimN (): VictimK.
  Definition removeVictimN: string := cacheN _++ "removeVictim".
  Definition removeVictim := MethodSig removeVictimN (Bit addrSz): Void.

  (** -- public interface ends *)

  Variables (getIndex: forall ty, fullType ty (SyntaxKind (Bit addrSz)) ->
                                  Expr ty (SyntaxKind (Bit indexSz)))
            (getTag: forall ty, fullType ty (SyntaxKind (Bit addrSz)) ->
                                Expr ty (SyntaxKind (Bit tagSz)))
            (buildAddr: forall ty, fullType ty (SyntaxKind (Bit tagSz)) ->
                                   fullType ty (SyntaxKind (Bit indexSz)) ->
                                   Expr ty (SyntaxKind (Bit addrSz)))
            (evictF: forall ty, Expr ty (SyntaxKind infoK) ->
                                Expr ty (SyntaxKind Bool)).

  Local Notation "'NCall' v <- f ; cont" :=
    (f (fun v => cont%kami_action))
      (at level 12, right associativity, v at level 15, f at level 15, only parsing): kami_action_scope.
  Local Notation "'NCall' f ; cont" :=
    (f cont%kami_action)
      (at level 12, right associativity, f at level 15, only parsing): kami_action_scope.

  Fixpoint callInfoReadRqs (var: Kind -> Type)
           (infoRq: var (Struct (BramRq indexSz TagInfoK)))
           (n: nat) (cont: ActionT var Void): ActionT var Void :=
    (match n with
     | O => cont
     | S n' => callInfoReadRqs infoRq n' (Call (infoPutRq n')(#infoRq); cont)
     end)%kami_action.

  Fixpoint callInfoReadRss (var: Kind -> Type)
           (tis: var (Vector TagInfoK lgWay))
           (n: nat) (cont: var (Vector TagInfoK lgWay) -> ActionT var Void)
    : ActionT var Void :=
    (match n with
     | O => cont tis
     | S n' => (NCall ptis <- callInfoReadRss tis n';
               Call ti <- (infoGetRs n')();
               LET ntis <- UpdateVector #ptis $n' #ti;
               (cont ntis))
     end)%kami_action.

  Definition readStageN: string := "readStage"+o.
  Definition readAddrN: string := "readAddr"+o.
  Definition readLineN: string := "readLine"+o.
  Definition writeStageN: string := "writeStage"+o.
  Definition writeLineN: string := "writeLine"+o.
  Definition victimsN: string := "victims"+o.
  Definition victimLineN: string := "victimLine"+o.
  Definition victimWayN: string := "victimWay"+o.

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

  Fixpoint findLine (var: Kind -> Type)
           (tags: var (Vector (Struct (TagValue infoK)) lgWay))
           (n: nat): Expr var (SyntaxKind (Bit lgWay)) :=
    (match n with
     | O => $$Default (* cannot happen *)
     | S n' =>
       (IF (evictF (#tags@[$(Nat.pow 2 lgWay - n)]!(TagValue infoK)@."value"))
        then $(Nat.pow 2 lgWay - n)
        else (findLine _ tags n'))
     end)%kami_expr.

  Fixpoint infoPutRqWFix (var: Kind -> Type)
           (way: var (Bit lgWay))
           (rq: var (Struct (BramRq indexSz TagInfoK)))
           (n: nat) (cont: ActionT var Void): ActionT var Void :=
    match n with
    | O => cont
    | S n' =>
      (If (#way == $(Nat.pow 2 lgWay - n))
       then (Call (infoPutRq (Nat.pow 2 lgWay - n))(#rq); Retv);
       infoPutRqWFix way rq n' cont)%kami_action
    end.

  Definition infoPutRqW (var: Kind -> Type)
             (way: var (Bit lgWay))
             (rq: var (Struct (BramRq indexSz TagInfoK)))
             (cont: ActionT var Void): ActionT var Void :=
    infoPutRqWFix way rq (Nat.pow 2 lgWay) cont.

  Fixpoint infoGetRsWFix (var: Kind -> Type)
           (way: var (Bit lgWay))
           (ti: var TagInfoK)
           (n: nat) (cont: var TagInfoK -> ActionT var Void): ActionT var Void :=
    match n with
    | O => cont ti
    | S n' =>
      (If (#way == $(Nat.pow 2 lgWay - n))
       then (Call nti <- (infoGetRs (Nat.pow 2 lgWay - n))(); Ret #nti)
       else (Ret $$Default)
        as mti;
      infoGetRsWFix way mti n' cont)%kami_action
    end.

  Definition infoGetRsW (var: Kind -> Type)
             (way: var (Bit lgWay))
             (cont: var TagInfoK -> ActionT var Void): ActionT var Void :=
    (LET tid <- $$Default;
    infoGetRsWFix way tid (Nat.pow 2 lgWay) cont)%kami_action.

  Fixpoint victimIterAFix (var: Kind -> Type)
           (victims: Expr var (SyntaxKind (Vector VictimK lgNumVictim)))
           (addr: Expr var (SyntaxKind (Bit addrSz)))
           (readF: Expr var (SyntaxKind (Bit lgNumVictim)) ->
                   Expr var (SyntaxKind VictimK) -> ActionT var Void)
           (cont: ActionT var Void) (n: nat): ActionT var Void :=
    match n with
    | O => cont
    | S n' =>
      (LET victim: VictimK <- victims@[$(Nat.pow 2 lgWay - n)];
      If (#victim!Victim@."victim_valid" && #victim!Victim@."victim_line"!CacheLine@."addr" == addr)
       then (readF ($(Nat.pow 2 lgWay - n))%kami_expr (#victim)%kami_expr)
       else (victimIterAFix victims addr readF cont n'); Retv)%kami_action
    end.

  Definition victimIterA (var: Kind -> Type)
             (victims: Expr var (SyntaxKind (Vector VictimK lgNumVictim)))
             (addr: Expr var (SyntaxKind (Bit addrSz)))
             (readF: Expr var (SyntaxKind (Bit lgNumVictim)) ->
                     Expr var (SyntaxKind VictimK) -> ActionT var Void)
             (cont: ActionT var Void): ActionT var Void :=
    victimIterAFix victims addr readF cont (Nat.pow 2 lgNumVictim).

  Fixpoint hasVictimSlotFix (var: Kind -> Type)
           (victims: Expr var (SyntaxKind (Vector VictimK lgNumVictim)))
           (n: nat): Expr var (SyntaxKind Bool) :=
    (match n with
     | O => !(victims@[$0]!Victim@."victim_valid")
     | S n' =>
       ((!(victims@[$n]!Victim@."victim_valid")) || hasVictimSlotFix victims n')
     end)%kami_expr.

  Fixpoint hasVictimSlotF (var: Kind -> Type)
           (victims: Expr var (SyntaxKind (Vector VictimK lgNumVictim)))
    : Expr var (SyntaxKind Bool) :=
    hasVictimSlotFix victims (Nat.pow 2 lgNumVictim - 1).

  Fixpoint hasVictimFix (var: Kind -> Type)
           (victims: Expr var (SyntaxKind (Vector VictimK lgNumVictim)))
           (n: nat): Expr var (SyntaxKind Bool) :=
    (match n with
     | O => (victims@[$0]!Victim@."victim_valid")
     | S n' =>
       ((victims@[$n]!Victim@."victim_valid") || hasVictimFix victims n')
     end)%kami_expr.

  Fixpoint hasVictimF (var: Kind -> Type)
           (victims: Expr var (SyntaxKind (Vector VictimK lgNumVictim)))
    : Expr var (SyntaxKind Bool) :=
    hasVictimFix victims (Nat.pow 2 lgNumVictim - 1).

  Fixpoint getVictimSlotFix (var: Kind -> Type)
           (victims: Expr var (SyntaxKind (Vector VictimK lgNumVictim)))
           (n: nat): Expr var (SyntaxKind (Bit lgNumVictim)) :=
    (match n with
     | O => $0
     | S n' =>
       (IF (victims@[$n]!Victim@."victim_valid")
        then getVictimSlotFix victims n'
        else $n)
     end)%kami_expr.

  Fixpoint getVictimSlotF (var: Kind -> Type)
           (victims: Expr var (SyntaxKind (Vector VictimK lgNumVictim)))
    : Expr var (SyntaxKind (Bit lgNumVictim)) :=
    getVictimSlotFix victims (Nat.pow 2 lgNumVictim - 1).

  Fixpoint getVictimFix (var: Kind -> Type)
           (victims: Expr var (SyntaxKind (Vector VictimK lgNumVictim)))
           (n: nat): Expr var (SyntaxKind CacheLineK) :=
    (match n with
     | O => (victims@[$0]!Victim@."victim_line")
     | S n' =>
       (IF (victims@[$n]!Victim@."victim_valid")
        then victims@[$n]!Victim@."victim_line"
        else getVictimFix victims n')
     end)%kami_expr.

  Fixpoint getVictimF (var: Kind -> Type)
           (victims: Expr var (SyntaxKind (Vector VictimK lgNumVictim)))
    : Expr var (SyntaxKind CacheLineK) :=
    getVictimFix victims (Nat.pow 2 lgNumVictim - 1).

  Definition ReadStage := Bit 2.
  Definition rsNone {var}: Expr var (SyntaxKind ReadStage) := ($0)%kami_expr.
  Definition rsInfoRq {var}: Expr var (SyntaxKind ReadStage) := ($1)%kami_expr.
  Definition rsValueRq {var}: Expr var (SyntaxKind ReadStage) := ($2)%kami_expr.
  Definition rsRsReady {var}: Expr var (SyntaxKind ReadStage) := ($3)%kami_expr.

  Definition WriteStage := Bit 3.
  Definition wsNone {var}: Expr var (SyntaxKind WriteStage) := ($0)%kami_expr.
  Definition wsRqAcc {var}: Expr var (SyntaxKind WriteStage) := ($1)%kami_expr.
  Definition wsRepRq {var}: Expr var (SyntaxKind WriteStage) := ($2)%kami_expr.
  Definition wsVictimRq {var}: Expr var (SyntaxKind WriteStage) := ($3)%kami_expr.
  Definition wsRsReady {var}: Expr var (SyntaxKind WriteStage) := ($7)%kami_expr.

  Definition cacheIfc :=
    MODULE {
      Register readStageN: ReadStage <- Default
      with Register readAddrN: Bit addrSz <- Default
      with Register readLineN: CacheLineK <- Default
      with Register writeStageN: WriteStage <- Default
      with Register writeLineN: CacheLineK <- Default
      with Register victimsN: Vector VictimK lgNumVictim <- Default
      with Register victimLineN: CacheLineK <- Default
      with Register victimWayN: Bit lgWay <- Default

      with Method readRqN (addr: Bit addrSz): Void :=
        (** Do not allow reads when a write is in progress *)
        Read writeStage: WriteStage <- writeStageN;
        Assert (#writeStage == wsNone);
        Read readStage: ReadStage <- readStageN;
        Assert (#readStage == rsNone);

        Read victims <- victimsN;
        victimIterA
          (#victims)%kami_expr (#addr)%kami_expr
          (fun _ victim => (Write readStageN: ReadStage <- rsRsReady;
                           Write readLineN <- victim!Victim@."victim_line";
                           Retv))%kami_action
          (Write readStageN: ReadStage <- rsInfoRq;
          Write readAddrN <- #addr;
          LET index <- getIndex _ addr;
          LET infoRq: Struct (BramRq indexSz TagInfoK) <- STRUCT { "write" ::= $$false;
                                                                   "addr" ::= #index;
                                                                   "datain" ::= $$Default };
          NCall callInfoReadRqs infoRq (Nat.pow 2 lgWay);
          Retv)%kami_action

      with Method readRsN (): CacheLineK :=
        Read readStage: ReadStage <- readStageN;
        Assert (#readStage == rsRsReady);
        Write readStageN: ReadStage <- rsNone;
        Read line: Struct CacheLine <- readLineN;
        Ret #line

      with Method writeRqN (line: CacheLineK): Void :=
        (** Do not allow writes when a read is in progress *)
        Read readStage: ReadStage <- readStageN;
        Assert (#readStage == rsNone);
        Read writeStage: WriteStage <- writeStageN;
        Assert (#writeStage == wsNone);

        (* When writing to a victim which is not evicted yet, need to check
         * if the new victim is still evictable (by checking [evictF]).
         * If so, it's fine to overwrite the victim with the new value.
         * Otherwise, remove the victim (consider it released) and perform an
         * ordinary write. *)
        Read victims <- victimsN;
        LET evictable <- evictF (#line!CacheLine@."info");
        victimIterA
          (#victims)%kami_expr (#line!CacheLine@."addr")%kami_expr
          (fun vidx victim =>
             (LET mline <- updStruct (ls:= CacheLine) (#line)
                                     (CacheLine !! "info_hit") ($$false);
             Write writeStageN <- (IF #evictable then wsRsReady else wsRqAcc);
             Write writeLineN <- #mline; (* meaningless when evictable *)
             Write victimsN <-
             #victims@[vidx <- STRUCT { "victim_valid" ::= #evictable;
                                        "victim_idx" ::= vidx;
                                        "victim_line" ::=
                                          #mline (* meaningless when not evictable *) }];
             Retv))%kami_action
          (Write writeStageN <- wsRqAcc;
          Write writeLineN <- #line;
          Retv)%kami_action

      with Method writeRsN (): CacheLineK :=
        Read writeStage: WriteStage <- writeStageN;
        Assert (#writeStage == wsRsReady);
        Write writeStageN <- wsNone;
        Read nline: CacheLineK <- writeLineN;
        Ret #nline

      with Method hasVictimN (): Bool :=
        Read victims <- victimsN;
        LET hasV <- hasVictimF #victims;
        Ret #hasV

      with Method getVictimN (): CacheLineK :=
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
        Assert (#readStage == rsInfoRq);
        Read addr: Bit addrSz <- readAddrN;
        LET tag <- getTag _ addr;
        LET index <- getIndex _ addr;

        LET tis: Vector TagInfoK lgWay <- $$Default;
        NCall ntis <- callInfoReadRss tis (Nat.pow 2 lgWay);
        LET itm <- doTagMatch _ tag ntis (Nat.pow 2 lgWay);

        Write readLineN: Struct CacheLine <-
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
                                      "addr" ::= {#index,
                                                  #itm!(TagMatch infoK lgWay)@."tm_way"};
                                      "datain" ::= $$Default });
             Retv)
        else (Write readStageN: ReadStage <- rsRsReady; Retv);
        Retv

      with Rule "read_data"+o :=
        Read readStage: ReadStage <- readStageN;
        Assert (#readStage == rsValueRq);
        Write readStageN: ReadStage <- rsRsReady;
        Call data <- dataGetRs();
        Read line: Struct CacheLine <- readLineN;
        Write readLineN: Struct CacheLine <-
          STRUCT { "addr" ::= #line!CacheLine@."addr";
                   "info_hit" ::= #line!CacheLine@."info_hit";
                   "info_way" ::= #line!CacheLine@."info_way";
                   "info_write" ::= #line!CacheLine@."info_write";
                   "info" ::= #line!CacheLine@."info";
                   "value_write" ::= $$false;
                   "value" ::= #data };
        Retv

      with Rule "write_info_hit"+o :=
        (* No need to update [writeLineN], which will serve as information
         * for the new line as well, since it is already the up-to-date info. *)
        Read writeStage: WriteStage <- writeStageN;
        Assert (#writeStage == wsRqAcc);
        Read line: Struct CacheLine <- writeLineN;
        Assert (#line!CacheLine@."info_hit");
        Write writeStageN <- wsRsReady;

        LET addr <- #line!CacheLine@."addr";
        LET tag <- getTag _ addr;
        LET index <- getIndex _ addr;
        LET way <- #line!CacheLine@."info_way";

        (* request write for the new line *)
        If (#line!CacheLine@."info_write")
        then (LET rq: Struct (BramRq indexSz TagInfoK) <-
                      STRUCT { "write" ::= $$true;
                               "addr" ::= #index;
                               "datain" ::=
                                 STRUCT { "tag" ::= #tag;
                                          "value" ::= #line!CacheLine@."info" } };
             NCall infoPutRqW way rq; Retv);

        If (#line!CacheLine@."value_write")
        then (Call dataPutRq (
                     STRUCT { "write" ::= $$true;
                              "addr" ::= {#index, #way};
                              "datain" ::= #line!CacheLine@."value" }); Retv);
        Retv

      with Rule "write_info_miss_rep_rq"+o :=
        Read writeStage: WriteStage <- writeStageN;
        Assert (#writeStage == wsRqAcc);
        Read line: Struct CacheLine <- writeLineN;
        Assert (!(#line!CacheLine@."info_hit"));
        Write writeStageN <- wsRepRq;

        LET addr <- #line!CacheLine@."addr";
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
        LET victimWay <- findLine _ ntis (Nat.pow 2 lgWay);

        Read line: Struct CacheLine <- writeLineN;
        LET addr <- #line!CacheLine@."addr";
        LET index <- getIndex _ addr;

        LET vtid <- #ntis@[#victimWay];
        LET vtag <- #vtid!(TagValue infoK)@."tag";
        LET vinfo <- #vtid!(TagValue infoK)@."value";

        Write victimWayN <- #victimWay;
        Write victimLineN: CacheLineK <- STRUCT { "addr" ::= buildAddr _ vtag index;
                                                  "info_hit" ::= $$false;
                                                  "info_way" ::= $$Default;
                                                  "info_write" ::= $$false;
                                                  "info" ::= #vinfo;
                                                  "value_write" ::= $$false;
                                                  "value" ::= $$Default };
        Call dataPutRq (STRUCT { "write" ::= $$false;
                                 "addr" ::= {#index, #victimWay};
                                 "datain" ::= $$Default });
        Retv

      with Rule "write_victim_rs"+o :=
        Read writeStage: WriteStage <- writeStageN;
        Assert (#writeStage == wsVictimRq);
        Read line: Struct CacheLine <- writeLineN;
        Write writeStageN <- wsRsReady;

        LET addr <- #line!CacheLine@."addr";
        LET tag <- getTag _ addr;
        LET index <- getIndex _ addr;
        Read way <- victimWayN;

        (** Handle the responses about the victim line *)
        Read victims <- victimsN;
        Assert (hasVictimSlotF #victims);
        LET slotIdx <- getVictimSlotF #victims;
        Call vdata <- dataGetRs ();
        Read victim: CacheLineK <- victimLineN;
        Write victimsN <-
        #victims@[#slotIdx <-
                  STRUCT { "victim_valid" ::= $$true;
                           "victim_idx" ::= #slotIdx;
                           "victim_line" ::=
                             STRUCT { "addr" ::= #victim!CacheLine@."addr";
                                      "info_hit" ::= #victim!CacheLine@."info_hit";
                                      "info_way" ::= #victim!CacheLine@."info_way";
                                      "info_write" ::= #victim!CacheLine@."info_write";
                                      "info" ::= #victim!CacheLine@."info";
                                      "value_write" ::= $$false;
                                      "value" ::= #vdata } }];

        (* Should update [writeLineN], which will serve as information
         * for the new line, with the up-to-date info.
         * Note that "info_write", "value_write", and "value" can be assigned to
         * arbitrary values, since it will be updated after the bypass. *)
        Write writeLineN: CacheLineK <- STRUCT { "addr" ::= #addr;
                                                 "info_hit" ::= $$true; (* MUST be true! *)
                                                 "info_way" ::= #way; (* MUST be the new way *)
                                                 "info_write" ::= $$false;
                                                 "info" ::= #line!CacheLine@."info";
                                                 "value_write" ::= $$false;
                                                 "value" ::= #line!CacheLine@."value" };

        (** request write for the new line; TODO: code duplicated with above *)
        If (#line!CacheLine@."info_write")
        then (LET rq: Struct (BramRq indexSz TagInfoK) <-
                      STRUCT { "write" ::= $$true;
                               "addr" ::= #index;
                               "datain" ::=
                                 STRUCT { "tag" ::= #tag;
                                          "value" ::= #line!CacheLine@."info" } };
             NCall infoPutRqW way rq; Retv);
        If (#line!CacheLine@."value_write")
        then (Call dataPutRq (
                     STRUCT { "write" ::= $$true;
                              "addr" ::= {#index, #way};
                              "datain" ::= #line!CacheLine@."value" }); Retv);
        Retv
    }.

  Fixpoint infoRams (w: nat) :=
    match w with
    | O => infoRam O
    | S w' => (infoRam w ++ infoRams w')%kami
    end.

  Definition cache :=
    (cacheIfc ++ infoRams (Nat.pow 2 lgWay - 1) ++ dataRam)%kami.

End Cache.
