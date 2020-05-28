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
  | i :: idx' => idx_to_string idx' ++ "_" ++ nat_to_string i
  end.
(* Eval compute in (idx_to_string (0~>1~>2)). *)

Definition MaybeStr (k: Kind) :=
  STRUCT { "valid" :: Bool; "data" :: k }.
Definition Maybe (k: Kind) := Struct (MaybeStr k).

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

  Definition bvSingleton (bv: (Bit sz) @ var) (i: (Bit sz_lg) @ var): Bool @ var :=
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

Section Kinds.
  Context `{hcfg: hconfig}.

  Definition KCIdx := Bit hcfg_children_max_lg.
  Definition KQIdx := Bit (hcfg_children_max_lg + 2).
  Definition KCBv := Bit hcfg_children_max. (* as a bitvector *)
  Definition KIdxM := Bit ∘hcfg_msg_id_sz.
  Definition KAddr := Bit hcfg_addr_sz.
  Definition KValue := Bit hcfg_value_sz.

  Definition KMsg :=
    STRUCT { "id" :: KIdxM;
             "type" :: Bool;
             "addr" :: KAddr;
             "value" :: KValue }.

End Kinds.

Section MSHR.
  Context `{hcfg: hconfig}.
  Variable oidx: IdxT.

  Definition UL :=
    STRUCT { "ul_valid" :: Bool;
             "ul_rsb" :: Bool;
             "ul_msg" :: Struct KMsg; (* The message contains a line address as well *)
             "ul_rsbTo" :: KCIdx }.

  Definition DL :=
    STRUCT { "dl_valid" :: Bool;
             "dl_rsb" :: Bool;
             "dl_msg" :: Struct KMsg; (* The message contains a line address as well *)
             "dl_rss_from" :: KCBv;
             "dl_rss_recv" :: KCBv;
             "dl_rss" :: Array (Struct KMsg) hcfg_children_max;
             "dl_rsbTo" :: KQIdx }.

  (* Uplock free and has an UL slot. *)
  Definition upLockableN: string := "upLockable" ++ idx_to_string oidx.
  Definition upLockable: Attribute SignatureT :=
    {| attrName := upLockableN;
       attrType := {| arg := KAddr; ret := Bool |} |}.

  (* Downlock free and has a DL slot. *)
  Definition downLockableN: string := "downLockable" ++ idx_to_string oidx.
  Definition downLockable: Attribute SignatureT :=
    {| attrName := downLockableN;
       attrType := {| arg := KAddr; ret := Bool |} |}.

  Definition upLockGetN: string := "upLockGet" ++ idx_to_string oidx.
  Definition upLockGet: Attribute SignatureT :=
    {| attrName := upLockGetN;
       attrType := {| arg := KAddr; ret := Maybe (Struct UL) |} |}.

  Definition downLockGetN: string := "downLockGet" ++ idx_to_string oidx.
  Definition downLockGet: Attribute SignatureT :=
    {| attrName := downLockGetN;
       attrType := {| arg := KAddr; ret := Maybe (Struct DL) |} |}.

  Definition downLockRssFullN: string := "downLockRssFull" ++ idx_to_string oidx.
  Definition downLockRssFull: Attribute SignatureT :=
    {| attrName := downLockRssFullN;
       attrType := {| arg := Void; ret := Maybe (Struct DL) |} |}.

  Definition RegUL :=
    STRUCT { "r_ul_rsb" :: Bool;
             "r_ul_msg" :: Struct KMsg; (* contains a line address *)
             "r_ul_rsbTo" :: KCIdx }.
  Definition registerULN: string := "registerUL" ++ idx_to_string oidx.
  Definition registerUL: Attribute SignatureT :=
    {| attrName := registerULN;
       attrType := {| arg := Struct RegUL; ret := Void |} |}.

  Definition releaseULN: string := "releaseUL" ++ idx_to_string oidx.
  Definition releaseUL: Attribute SignatureT :=
    {| attrName := releaseULN;
       attrType := {| arg := KAddr; ret := Void |} |}.

  Definition RegDL :=
    STRUCT { "r_dl_rsb" :: Bool;
             "r_dl_msg" :: Struct KMsg;
             "r_dl_rss_from" :: KCBv;
             "r_dl_rsbTo" :: KQIdx }.
  Definition registerDLN: string := "registerDL" ++ idx_to_string oidx.
  Definition registerDL: Attribute SignatureT :=
    {| attrName := registerDLN;
       attrType := {| arg := Struct RegDL; ret := Void |} |}.

  Definition releaseDLN: string := "releaseDL" ++ idx_to_string oidx.
  Definition releaseDL: Attribute SignatureT :=
    {| attrName := releaseDLN;
       attrType := {| arg := KAddr; ret := Void |} |}.

  Definition TrsfUpDown :=
    STRUCT { "r_dl_addr" :: KAddr; "r_dl_rss_from" :: KCBv }.
  Definition transferUpDownN: string := "transferUpDown" ++ idx_to_string oidx.
  Definition transferUpDown: Attribute SignatureT :=
    {| attrName := transferUpDownN;
       attrType := {| arg := Struct TrsfUpDown; ret := Void |} |}.

  Definition AddRs :=
    STRUCT { "r_dl_addr" :: KAddr;
             "r_dl_midx" :: KCIdx;
             "r_dl_msg" :: Struct KMsg }.
  Definition addRsN: string := "addRs" ++ idx_to_string oidx.
  Definition addRs: Attribute SignatureT :=
    {| attrName := addRsN;
       attrType := {| arg := Struct AddRs; ret := Void |} |}.

  Variables logNumUls logNumDls: nat.

  Fixpoint ulFix {var k}
           (lc: Expr var (SyntaxKind k))
           (tc: nat -> Expr var (SyntaxKind (Struct UL)) -> Expr var (SyntaxKind k))
           (cond: Expr var (SyntaxKind (Struct UL)) -> Expr var (SyntaxKind Bool))
           (uls: Expr var (SyntaxKind (Vector (Struct UL) logNumUls)))
           (n: nat): Expr var (SyntaxKind k) :=
    (match n with
     | O => lc
     | S n' =>
       let ul := uls@[$(Nat.pow 2 logNumUls - n)] in
       (IF (cond ul) then tc n ul else ulFix lc tc cond uls n')
     end)%kami_expr.

  Fixpoint ulIter {var k}
           (lc: Expr var (SyntaxKind k))
           (tc: nat -> Expr var (SyntaxKind (Struct UL)) -> Expr var (SyntaxKind k))
           (cond: Expr var (SyntaxKind (Struct UL)) -> Expr var (SyntaxKind Bool))
           (uls: Expr var (SyntaxKind (Vector (Struct UL) logNumUls)))
    : Expr var (SyntaxKind k) :=
    ulFix lc tc cond uls (Nat.pow 2 logNumUls).

  Fixpoint dlFix {var k}
           (lc: Expr var (SyntaxKind k))
           (tc: nat -> Expr var (SyntaxKind (Struct DL)) -> Expr var (SyntaxKind k))
           (cond: Expr var (SyntaxKind (Struct DL)) -> Expr var (SyntaxKind Bool))
           (dls: Expr var (SyntaxKind (Vector (Struct DL) logNumDls)))
           (n: nat): Expr var (SyntaxKind k) :=
    (match n with
     | O => lc
     | S n' =>
       let dl := dls@[$(Nat.pow 2 logNumDls - n)] in
       (IF (cond dl) then tc n dl else dlFix lc tc cond dls n')
     end)%kami_expr.

  Fixpoint dlIter {var k}
           (lc: Expr var (SyntaxKind k))
           (tc: nat -> Expr var (SyntaxKind (Struct DL)) -> Expr var (SyntaxKind k))
           (cond: Expr var (SyntaxKind (Struct DL)) -> Expr var (SyntaxKind Bool))
           (dls: Expr var (SyntaxKind (Vector (Struct DL) logNumDls)))
    : Expr var (SyntaxKind k) :=
    dlFix lc tc cond dls (Nat.pow 2 logNumDls).

  Definition hasULIter {var}
             (uls: Expr var (SyntaxKind (Vector (Struct UL) logNumUls)))
    : Expr var (SyntaxKind Bool) :=
    (ulIter $$false (fun _ _ => $$true)
            (fun ul => !(ul!UL@."ul_valid")) uls)%kami_expr.

  Definition hasDLIter {var}
             (dls: Expr var (SyntaxKind (Vector (Struct DL) logNumDls)))
    : Expr var (SyntaxKind Bool) :=
    (dlIter $$false (fun _ _ => $$true)
            (fun dl => !(dl!DL@."dl_valid")) dls)%kami_expr.

  Definition upLockedF {var}
             (a: Expr var (SyntaxKind KAddr))
             (ul: Expr var (SyntaxKind (Struct UL))): Expr var (SyntaxKind Bool) :=
    (ul!UL@."ul_valid" && ul!UL@."ul_msg"!KMsg@."addr" == a)%kami_expr.

  Definition upLockFreeIter {var}
             (a: Expr var (SyntaxKind KAddr))
             (uls: Expr var (SyntaxKind (Vector (Struct UL) logNumUls)))
    : Expr var (SyntaxKind Bool) :=
    (ulIter $$true (fun _ _ => $$false) (upLockedF a) uls)%kami_expr.

  Definition downLockedF {var}
             (a: Expr var (SyntaxKind KAddr))
             (dl: Expr var (SyntaxKind (Struct DL))): Expr var (SyntaxKind Bool) :=
    (dl!DL@."dl_valid" && dl!DL@."dl_msg"!KMsg@."addr" == a)%kami_expr.

  Definition downLockFreeIter {var}
             (a: Expr var (SyntaxKind KAddr))
             (dls: Expr var (SyntaxKind (Vector (Struct DL) logNumDls)))
    : Expr var (SyntaxKind Bool) :=
    (dlIter $$true (fun _ _ => $$false) (downLockedF a) dls)%kami_expr.

  Definition upLockGetIter {var}
             (a: Expr var (SyntaxKind KAddr))
             (uls: Expr var (SyntaxKind (Vector (Struct UL) logNumUls)))
    : Expr var (SyntaxKind (Maybe (Struct UL))) :=
    (ulIter (k:= Maybe (Struct UL)) $$Default
            (fun _ ul => STRUCT { "valid" ::= $$true; "data" ::= ul })
            (upLockedF a) uls)%kami_expr.

  Definition downLockGetIter {var}
             (a: Expr var (SyntaxKind KAddr))
             (dls: Expr var (SyntaxKind (Vector (Struct DL) logNumDls)))
    : Expr var (SyntaxKind (Maybe (Struct DL))) :=
    (dlIter (k:= Maybe (Struct DL)) $$Default
            (fun _ dl => STRUCT { "valid" ::= $$true; "data" ::= dl })
            (downLockedF a) dls)%kami_expr.

  Definition downLockRssFullF {var}
             (dl: Expr var (SyntaxKind (Struct DL))): Expr var (SyntaxKind Bool) :=
    (dl!DL@."dl_valid" && dl!DL@."dl_rss_recv" == dl!DL@."dl_rss_from")%kami_expr.

  Definition downLockRssFullIter {var}
             (dls: Expr var (SyntaxKind (Vector (Struct DL) logNumDls)))
    : Expr var (SyntaxKind (Maybe (Struct DL))) :=
    (dlIter (k:= Maybe (Struct DL)) $$Default
            (fun _ dl => STRUCT { "valid" ::= $$true; "data" ::= dl })
            downLockRssFullF dls)%kami_expr.

  Definition getULSlotIter {var}
             (uls: Expr var (SyntaxKind (Vector (Struct UL) logNumUls)))
    : Expr var (SyntaxKind (Bit logNumUls)) :=
    (ulIter $$Default (fun n ul => $(Nat.pow 2 logNumUls - n))
            (fun ul => !(ul!UL@."ul_valid")) uls)%kami_expr.

  Definition getDLSlotIter {var}
             (dls: Expr var (SyntaxKind (Vector (Struct DL) logNumDls)))
    : Expr var (SyntaxKind (Bit logNumDls)) :=
    (dlIter $$Default (fun n dl => $(Nat.pow 2 logNumDls - n))
            (fun dl => !(dl!DL@."dl_valid")) dls)%kami_expr.

  Definition findULIter {var}
             (a: Expr var (SyntaxKind KAddr))
             (uls: Expr var (SyntaxKind (Vector (Struct UL) logNumUls)))
    : Expr var (SyntaxKind (Bit logNumUls)) :=
    (ulIter $$Default (fun n ul => $(Nat.pow 2 logNumUls - n))
            (fun ul => ul!UL@."ul_valid" && ul!UL@."ul_msg"!KMsg@."addr" == a)
            uls)%kami_expr.

  Definition findDLIter {var}
             (a: Expr var (SyntaxKind KAddr))
             (dls: Expr var (SyntaxKind (Vector (Struct DL) logNumDls)))
    : Expr var (SyntaxKind (Bit logNumDls)) :=
    (dlIter $$Default (fun n dl => $(Nat.pow 2 logNumDls - n))
            (fun dl => dl!DL@."dl_valid" && dl!DL@."dl_msg"!KMsg@."addr" == a)
            dls)%kami_expr.

  Definition mshrs: Kami.Syntax.Modules :=
    MODULE {
      Register "uls" : Vector (Struct UL) logNumUls <- Default
      with Register "dls" : Vector (Struct DL) logNumDls <- Default
      with Method upLockableN (a: KAddr): Bool :=
        Read uls <- "uls";
        LET hasSlot <- hasULIter #uls;
        LET ulFree <- upLockFreeIter #a #uls;
        Ret (#hasSlot && #ulFree)
      with Method downLockableN (a: KAddr): Bool :=
        Read dls <- "dls";
        LET hasSlot <- hasDLIter #dls;
        LET dlFree <- downLockFreeIter #a #dls;
        Ret (#hasSlot && #dlFree)
      with Method upLockGetN (a: KAddr): Maybe (Struct UL) :=
        Read uls <- "uls";
        LET retv <- upLockGetIter #a #uls;
        Ret #retv
      with Method downLockGetN (a: KAddr): Maybe (Struct DL) :=
        Read dls <- "dls";
        LET retv <- downLockGetIter #a #dls;
        Ret #retv
      with Method downLockRssFullN (): Maybe (Struct DL) :=
        Read dls <- "dls";
        LET retv <- downLockRssFullIter #dls;
        Ret #retv

      with Method registerULN (r: Struct RegUL): Void :=
        Read uls <- "uls";
        LET uli <- getULSlotIter #uls;
        Write "uls" <- #uls@[#uli <- STRUCT { "ul_valid" ::= $$true;
                                              "ul_rsb" ::= #r!RegUL@."r_ul_rsb";
                                              "ul_msg" ::= #r!RegUL@."r_ul_msg";
                                              "ul_rsbTo" ::= #r!RegUL@."r_ul_rsbTo" }];
        Retv
      with Method releaseULN (a: KAddr): Void :=
        Read uls <- "uls";
        LET uli <- findULIter #a #uls;
        Write "uls" <- #uls@[#uli <- $$Default];
        Retv

      with Method registerDLN (r: Struct RegDL): Void :=
        Read dls <- "dls";
        LET dli <- getDLSlotIter #dls;
        Write "dls" <- #dls@[#dli <- STRUCT { "dl_valid" ::= $$true;
                                              "dl_rsb" ::= #r!RegDL@."r_dl_rsb";
                                              "dl_msg" ::= #r!RegDL@."r_dl_msg";
                                              "dl_rss_from" ::= #r!RegDL@."r_dl_rss_from";
                                              "dl_rss_recv" ::= $$Default;
                                              "dl_rss" ::= $$Default;
                                              "dl_rsbTo" ::= #r!RegDL@."r_dl_rsbTo" }];
        Retv
      with Method releaseDLN (a: KAddr): Void :=
        Read dls <- "dls";
        LET dli <- findDLIter #a #dls;
        Write "dls" <- #dls@[#dli <- $$Default];
        Retv

      with Method transferUpDownN (r: Struct TrsfUpDown): Void :=
        Read uls <- "uls";
        LET a <- #r!TrsfUpDown@."r_dl_addr";
        LET uli <- findULIter #a #uls;
        LET ul <- #uls@[#uli];
        Read dls <- "dls";
        LET dli <- getDLSlotIter #dls;
        Write "uls" <- #uls@[#uli <- $$Default];
        Write "dls" <- #dls@[#dli <- STRUCT { "dl_valid" ::= $$true;
                                              "dl_rsb" ::= #ul!UL@."ul_rsb";
                                              "dl_msg" ::= #ul!UL@."ul_msg";
                                              "dl_rss_from" ::= #r!TrsfUpDown@."r_dl_rss_from";
                                              "dl_rss_recv" ::= $$Default;
                                              "dl_rss" ::= $$Default;
                                              "dl_rsbTo" ::= {$downIdx, #ul!UL@."ul_rsbTo"} }];
        Retv

      with Method addRsN (r: Struct AddRs): Void :=
        Read dls <- "dls";
        LET dli <- findDLIter (#r!AddRs@."r_dl_addr") #dls;
        LET odl <- downLockGetIter (#r!AddRs@."r_dl_addr") #dls;
        LET dl <- #odl!(MaybeStr (Struct DL))@."data";
        Write "dls" <- #dls@[#dli <- STRUCT { "dl_valid" ::= #dl!DL@."dl_valid";
                                              "dl_rsb" ::= #dl!DL@."dl_rsb";
                                              "dl_msg" ::= #dl!DL@."dl_msg";
                                              "dl_rss_from" ::= #dl!DL@."dl_rss_from";
                                              "dl_rss_recv" ::=
                                                bvSet (#dl!DL@."dl_rss_recv")
                                                      (#r!AddRs@."r_dl_midx");
                                              "dl_rss" ::=
                                                UpdateArray
                                                  (#dl!DL@."dl_rss")
                                                  (#r!AddRs@."r_dl_midx")
                                                  (#r!AddRs@."r_dl_msg");
                                              "dl_rsbTo" ::= #dl!DL@."dl_rsbTo" }];
        Retv
    }.

End MSHR.

Section Cache.

  (** Implement so-called an information cache (containing ownership bit and
   *  status), a directory, and a data (value) cache. *)

  Variables (oidx: IdxT)
            (* MSB                                  LSB
             * |----------------(addr)----------------|
             * |--(tag)--|--(index)--|---|--(offset)--|
             * |---------|--(dataIndex)--|------------|
             *              (= index + lgWay)
             *)
            (tagSz indexSz offsetSz addrSz: nat)
            (lgWay dirLgWay: nat)
            (infoK dirK dataK: Kind).

  Local Notation "s '+o'" := (s ++ idx_to_string oidx)%string (at level 60).
  Local Notation "s1 _++ s2" := (s1 ++ "_" ++ s2)%string (at level 60).

  (** The information cache: way -> index -> (tag + info) *)
  Definition TagInfo :=
    STRUCT { "tag" :: Bit tagSz;
             "info" :: infoK }.
  Definition TagInfoK := Struct TagInfo.

  Definition infoRamN (way: nat): string :=
    "infoRam"+o _++ nat_to_string way.
  Definition infoRam (way: nat) := bram1 (infoRamN way) indexSz TagInfoK.
  Definition infoPutRq (way: nat) :=
    MethodSig ((infoRamN way) -- "putRq")(Struct (BramRq indexSz TagInfoK)): Void.
  Definition infoGetRs (way: nat) :=
    MethodSig ((infoRamN way) -- "getRs")(): TagInfoK.

  (** The directory: dirWay -> index -> (tag + dir) *)
  Definition TagDir :=
    STRUCT { "tag" :: Bit tagSz;
             "dir" :: dirK }.
  Definition TagDirK := Struct TagDir.

  Definition dirRamN (way: nat): string :=
    "dirRam"+o _++ nat_to_string way.
  Definition dirRam (way: nat) := bram1 (dirRamN way) indexSz TagDirK.
  Definition dirPutRq (way: nat) :=
    MethodSig ((dirRamN way) -- "putRq")(Struct (BramRq indexSz TagDirK)): Void.
  Definition dirGetRs (way: nat) :=
    MethodSig ((dirRamN way) -- "getRs")(): TagDirK.

  (** The data cache: index *)
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
             "value" :: dataK; (* [info_hit] implies value-hit *)
             (* NOTE: in the cache is inclusive, then this interface is redundant
              * in that always [info_hit = dir_hit] and [lgWay = dirLgWay].
              * However, in non-inclusive caches, we need to have extended directory
              * structure that may have different hit and ways.
              *)
             "dir_hit" :: Bool;
             "dir_way" :: Bit dirLgWay;
             "dir_write" :: Bool; (* used for writing the value? *)
             "dir" :: dirK }.
  Definition CacheLineK := Struct CacheLine.

  Definition readRqN: string := cacheN _++ "readRq".
  Definition readRq := MethodSig readRqN (Bit addrSz): Void.
  Definition readRsN: string := cacheN _++ "readRs".
  Definition readRs := MethodSig readRsN (): CacheLineK.

  Definition writeRqN: string := cacheN _++ "writeRq".
  Definition writeRq := MethodSig writeRqN (CacheLineK): Void.
  Definition writeRsN: string := cacheN _++ "writeRs".
  Definition Victim :=
    STRUCT { "vc_evicted" :: Bool;
             "vc_addr" :: Bit addrSz;
             "vc_info" :: infoK;
             "vc_dir" :: dirK;
             "vc_data" :: dataK }.
  Definition VictimK := Struct Victim.
  Definition writeRs := MethodSig writeRsN (): VictimK.

  Variables (getIndex: forall ty, fullType ty (SyntaxKind (Bit addrSz)) ->
                                  Expr ty (SyntaxKind (Bit indexSz)))
            (getTag: forall ty, fullType ty (SyntaxKind (Bit addrSz)) ->
                                Expr ty (SyntaxKind (Bit tagSz))).
  (* (readTagMatch: forall ty, fullType ty (SyntaxKind (Bit (tagSz + 1))) -> *)
  (*                           fullType ty (SyntaxKind (Bit tagSz)) -> *)
  (*                           Expr ty (SyntaxKind Bool)) *)
  (* (writeTagMatch: forall ty, fullType ty (SyntaxKind (Bit (tagSz + 1))) -> *)
  (*                            fullType ty (SyntaxKind (Bit tagSz)) -> *)
  (*                            Expr ty (SyntaxKind Bool)). *)

  Fixpoint callInfoReadRqs (var: Kind -> Type)
           (infoRq: var (Struct (BramRq indexSz TagInfoK)))
           (n: nat) (cont: ActionT var Void): ActionT var Void :=
    (match n with
     | O => cont
     | S n' => callInfoReadRqs infoRq n' (Call (infoPutRq n')(#infoRq); cont)
     end)%kami_action.

  Fixpoint callDirReadRqs (var: Kind -> Type)
           (dirRq: var (Struct (BramRq indexSz TagDirK)))
           (n: nat) (cont: ActionT var Void): ActionT var Void :=
    (match n with
     | O => cont
     | S n' => callDirReadRqs dirRq n' (Call (dirPutRq n')(#dirRq); cont)
     end)%kami_action.

  (* Definition onRqN: string := "onRq"+o. *)
  (* Definition rqWriteN: string := "rqWrite"+o. *)
  (* Definition rqIndexN: string := "rqIndex"+o. *)
  (* Definition rqTagN: string := "rqTag"+o. *)
  (* Definition rqDataN: string := "rqData"+o. *)
  (* Definition victimTagN: string := "victimTag"+o. *)
  (* Definition onWriteN: string := "onWrite"+o. *)
  Definition onInfoReadN: string := "onInfoRead"+o.
  Definition infoReadTagN: string := "infoReadTag"+o.

  (* Definition cache (infoNumWays dirNumWays: nat) := *)
  (*   MODULE { *)
  (*     Register onInfoReadN: Bool <- Default *)
  (*     with Register infoReadTagN: Bit tagSz <- Default *)

  (*     with Method infoReadRqN (addr: Bit addrSz): Void := *)
  (*       Read onInfoRead <- onInfoReadN; *)
  (*       Assert !#onInfoRead; *)
  (*       Write onInfoReadN <- $$true; *)
  (*       Write infoReadTagN <- getTag _ addr; *)

  (*       LET index <- getIndex _ addr; *)
  (*       LET infoRq: Struct (BramRq indexSz TagInfoK) <- STRUCT { "write" ::= $$false; *)
  (*                                                                "addr" ::= #index; *)
  (*                                                                "datain" ::= $$Default }; *)
  (*       LET dirRq: Struct (BramRq indexSz TagDirK) <- STRUCT { "write" ::= $$false; *)
  (*                                                              "addr" ::= #index; *)
  (*                                                              "datain" ::= $$Default }; *)
  (*       callInfoReadRqs *)
  (*         infoRq infoNumWays *)
  (*         (callDirReadRqs dirRq dirNumWays Retv) *)

  (*     with Method infoReadRsN (): InfoDirK := *)
  (*       Read onInfoRead <- onInfoReadN; *)
  (*       Assert #onInfoRead; *)
  (*       Write onInfoReadN <- $$false; *)
  (*       Read tag <- infoReadTagN; *)

  (*     }. *)

  (* Register onRqN: Bool <- Default *)
  (* with Register onWriteN: Bool <- Default *)
  (* with Register rqWriteN: Bool <- Default *)
  (* with Register rqIndexN: Bit indexSz <- Default *)
  (* with Register rqTagN: Bit tagSz <- Default *)
  (* with Register rqDataN: dataK <- Default *)
  (* with Register victimTagN: Bit tagSz <- Default *)

  (* with Rule cacheWriteTagRsN := *)
  (*   Read onRq <- onRqN; *)
  (*   Read rqWrite <- rqWriteN; *)
  (*   Read onWrite <- onWriteN; *)
  (*   Assert (#onRq && #rqWrite && !#onWrite); *)
  (*   Read rqTag <- rqTagN; *)
  (*   Call tag <- tagGetRs (); *)
  (*   If (writeTagMatch _ tag rqTag) *)
  (*   then (Read rqIndex <- rqIndexN; *)
  (*        Read rqData <- rqDataN; *)
  (*        Call dataPutRq (STRUCT { "write" ::= $$true; *)
  (*                                 "addr" ::= #rqIndex; *)
  (*                                 "datain" ::= #rqData }); *)
  (*        Write onWriteN <- $$true; *)
  (*        Retv) *)
  (*   else (Write victimTagN <- #tag; Retv); *)
  (*   Retv *)

  (* with Method cacheRqN (rq: Struct CacheRq): Void := *)
  (*   Read onRq <- onRqN; *)
  (*   Assert !#onRq; *)
  (*   LET isWrite <- #rq!CacheRq@."cache_write"; *)
  (*   LET addr <- #rq!CacheRq@."cache_addr"; *)
  (*   LET index <- getIndex _ addr; *)
  (*   LET tag <- getTag _ addr; *)
  (*   Call tagPutRq (STRUCT { "write" ::= $$false; *)
  (*                           "addr" ::= #index; *)
  (*                           "datain" ::= $$Default }); *)
  (*   Write rqWriteN <- #isWrite; *)
  (*   Write rqIndexN <- #index; *)
  (*   Write rqTagN <- #tag; *)
  (*   If #isWrite *)
  (*   then (Write rqDataN <- #rq!CacheRq@."cache_data"; *)
  (*        Retv) *)
  (*   else (Call dataPutRq (STRUCT { "write" ::= $$false; *)
  (*                                  "addr" ::= #index; *)
  (*                                  "datain" ::= $$Default }); *)
  (*        Retv); *)
  (*   Write onRqN <- $$true; *)
  (*   Retv *)

  (* with Method cacheReadRsN (): Maybe dataK := *)
  (*   Read onRq <- onRqN; *)
  (*   Read rqWrite <- rqWriteN; *)
  (*   Assert (#onRq && !#rqWrite); *)
  (*   Read rqTag <- rqTagN; *)
  (*   Call tag <- tagGetRs (); *)
  (*   Call data <- dataGetRs (); *)
  (*   LET retv: Maybe dataK <- STRUCT { "valid" ::= readTagMatch _ tag rqTag; *)
  (*                                     "data" ::= #data }; *)
  (*   Write onRqN <- $$false; *)
  (*   Ret #retv *)

  (* with Method cacheWriteRsN (): Void := *)
  (*   Read onRq <- onRqN; *)
  (*   Read rqWrite <- rqWriteN; *)
  (*   Assert (#onRq && #rqWrite); *)
  (*   Read onWrite <- onWriteN; *)
  (*   If #onWrite then (Call dataGetRs (); *)
  (*                    Write onWriteN <- $$false; *)
  (*                    Retv); *)
  (*                    Read victimTag <- victimTagN; *)
  (*                    LET retv: Maybe (Bit tagSz) <- STRUCT { "valid" ::= !#onWrite; *)
  (*                                                            "data" ::= #victimTag }; *)
  (*                    Write onRqN <- $$false; *)
  (*                    (* Ret #retv *) Retv *)

End Cache.
