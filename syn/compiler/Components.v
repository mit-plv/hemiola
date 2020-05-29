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
  (** Implement several caches based on non-inclusiveness:
   * 1) an information cache: [index -> way -> (tag + info + dir)]
   * 2) an extended directory cache: [index -> edirWay -> dir]
   *)

  Variables (oidx: IdxT)
            (* MSB                                  LSB
             * |----------------(addr)----------------|
             * |--(tag)--|--(index)--|---|--(offset)--|
             * |---------|--(dataIndex)--|------------|
             *              (= index + lgWay)
             *)
            (tagSz indexSz offsetSz addrSz: nat)
            (lgWay edirLgWay: nat)
            (infoK dirK dataK: Kind).

  Local Notation "s '+o'" := (s ++ idx_to_string oidx)%string (at level 60).
  Local Notation "s1 _++ s2" := (s1 ++ "_" ++ s2)%string (at level 60).

  Definition TagValue (valueK: Kind) :=
    STRUCT { "tag" :: Bit tagSz; "value" :: valueK }.

  (** The information cache *)
  Definition InfoDir := STRUCT { "info" :: infoK; "dir" :: dirK }.
  Definition InfoDirK := Struct InfoDir.
  Definition TagInfoDir := TagValue InfoDirK.
  Definition TagInfoDirK := Struct TagInfoDir.

  Definition infoRamN (way: nat): string :=
    "infoRam"+o _++ nat_to_string way.
  Definition infoRam (way: nat) := bram1 (infoRamN way) indexSz TagInfoDirK.
  Definition infoPutRq (way: nat) :=
    MethodSig ((infoRamN way) -- "putRq")(Struct (BramRq indexSz TagInfoDirK)): Void.
  Definition infoGetRs (way: nat) :=
    MethodSig ((infoRamN way) -- "getRs")(): TagInfoDirK.

  (** The extended directory: edirWay -> index -> (tag + dir) *)
  Definition TagDir := TagValue dirK.
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
             (* NOTE: if the cache is inclusive, then below fields for the extended
              * directory are totally useless. *)
             "edir_hit" :: Bool;
             "edir_way" :: Bit edirLgWay;
             "edir_write" :: Bool; (* used for writing a directory status? *)
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

  Local Notation "'NCall' v <- f ; cont" :=
    (f (fun v => cont%kami_action))
      (at level 12, right associativity, v at level 15, f at level 15, only parsing): kami_action_scope.
  Local Notation "'NCall' f ; cont" :=
    (f cont%kami_action)
      (at level 12, right associativity, f at level 15, only parsing): kami_action_scope.

  Fixpoint callInfoReadRqs (var: Kind -> Type)
           (infoRq: var (Struct (BramRq indexSz TagInfoDirK)))
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

  Fixpoint callInfoReadRss (var: Kind -> Type)
           (tis: var (Vector TagInfoDirK lgWay))
           (n: nat) (cont: var (Vector TagInfoDirK lgWay) -> ActionT var Void)
    : ActionT var Void :=
    (match n with
     | O => cont tis
     | S n' => (NCall ptis <- callInfoReadRss tis n';
               Call ti <- (infoGetRs n')();
               LET ntis <- UpdateVector #ptis $n' #ti;
               (cont ntis))
     end)%kami_action.

  Fixpoint callDirReadRss (var: Kind -> Type)
           (tds: var (Vector TagDirK edirLgWay))
           (n: nat) (cont: var (Vector TagDirK edirLgWay) -> ActionT var Void)
    : ActionT var Void :=
    (match n with
     | O => cont tds
     | S n' => (NCall ptds <- callDirReadRss tds n';
               Call ti <- (dirGetRs n')();
               LET ntds <- UpdateVector #ptds $n' #ti;
               (cont ntds))
     end)%kami_action.

  Definition readStageN: string := "readStage"+o.
  Definition readAddrN: string := "readAddr"+o.
  Definition readLineN: string := "readLine"+o.
  Definition writeStageN: string := "writeStage"+o.

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

  Fixpoint infoPutRqWFix (var: Kind -> Type)
           (way: var (Bit lgWay))
           (rq: var (Struct (BramRq indexSz TagInfoDirK)))
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
             (rq: var (Struct (BramRq indexSz TagInfoDirK)))
             (cont: ActionT var Void): ActionT var Void :=
    infoPutRqWFix way rq (Nat.pow 2 lgWay) cont.

  Fixpoint dirPutRqWFix (var: Kind -> Type)
           (way: var (Bit edirLgWay))
           (rq: var (Struct (BramRq indexSz TagDirK)))
           (n: nat) (cont: ActionT var Void): ActionT var Void :=
    match n with
    | O => cont
    | S n' =>
      (If (#way == $(Nat.pow 2 edirLgWay - n))
       then (Call (dirPutRq (Nat.pow 2 edirLgWay - n))(#rq); Retv);
       dirPutRqWFix way rq n' cont)%kami_action
    end.

  Definition dirPutRqW (var: Kind -> Type)
             (way: var (Bit edirLgWay))
             (rq: var (Struct (BramRq indexSz TagDirK)))
             (cont: ActionT var Void): ActionT var Void :=
    dirPutRqWFix way rq (Nat.pow 2 edirLgWay) cont.

  Definition ReadStage := Bit 2.
  Definition rsNone {var}: Expr var (SyntaxKind ReadStage) := ($0)%kami_expr.
  Definition rsInfoRq {var}: Expr var (SyntaxKind ReadStage) := ($1)%kami_expr.
  Definition rsValueRq {var}: Expr var (SyntaxKind ReadStage) := ($2)%kami_expr.
  Definition rsRsOk {var}: Expr var (SyntaxKind ReadStage) := ($3)%kami_expr.

  Definition WriteStage := Bit 2.
  Definition wsNone {var}: Expr var (SyntaxKind WriteStage) := ($0)%kami_expr.

  Definition cacheIfc :=
    MODULE {
      Register readStageN: ReadStage <- Default
      with Register readAddrN: Bit addrSz <- Default
      with Register readLineN: Struct CacheLine <- Default

      with Register writeStageN: WriteStage <- Default
      (* with Register writeLineN: CacheLineK <- Default *)

      with Method readRqN (addr: Bit addrSz): Void :=
        Read readStage: ReadStage <- readStageN;
        Assert (#readStage == rsNone);
        Write readStageN: ReadStage <- rsInfoRq;
        Write readAddrN <- #addr;
        LET index <- getIndex _ addr;
        LET infoRq: Struct (BramRq indexSz TagInfoDirK) <- STRUCT { "write" ::= $$false;
                                                                 "addr" ::= #index;
                                                                 "datain" ::= $$Default };
        LET dirRq: Struct (BramRq indexSz TagDirK) <- STRUCT { "write" ::= $$false;
                                                               "addr" ::= #index;
                                                               "datain" ::= $$Default };
        NCall callInfoReadRqs infoRq (Nat.pow 2 lgWay);
        NCall callDirReadRqs dirRq (Nat.pow 2 edirLgWay);
        Retv

      with Method readRsN (): CacheLineK :=
        Read readStage: ReadStage <- readStageN;
        Assert (#readStage == rsRsOk);
        Write readStageN: ReadStage <- rsNone;
        Read line: Struct CacheLine <- readLineN;
        Ret #line

      with Method writeRqN (line: CacheLineK): Void :=
        Read writeStage: WriteStage <- writeStageN;
        Assert (#writeStage == wsNone);
        (* Write writeLineN <- #line; *)

        LET addr <- #line!CacheLine@."addr";
        LET tag <- getTag _ addr;
        LET index <- getIndex _ addr;

        If (#line!CacheLine@."info_hit")
        then (LET way <- #line!CacheLine@."info_way";
             If (#line!CacheLine@."info_write")
              then (LET rq: Struct (BramRq indexSz TagInfoDirK) <-
                            STRUCT { "write" ::= $$true;
                                     "addr" ::= #index;
                                     "datain" ::=
                                       STRUCT { "tag" ::= #tag;
                                                "value" ::=
                                                  STRUCT { "info" ::= #line!CacheLine@."info";
                                                           "dir" ::= #line!CacheLine@."dir" }
                                              }
                                   };
                   NCall infoPutRqW way rq; Retv);
              If (#line!CacheLine@."value_write")
              then (Call dataPutRq (
                           STRUCT { "write" ::= $$true;
                                    "addr" ::= {#index, #way};
                                    "datain" ::= #line!CacheLine@."value" }); Retv); Retv);
        Retv

      with Rule "readTagMatch" :=
        Read readStage: ReadStage <- readStageN;
        Assert (#readStage == rsInfoRq);
        Read addr: Bit addrSz <- readAddrN;
        LET tag <- getTag _ addr;
        LET index <- getIndex _ addr;

        LET tis: Vector TagInfoDirK lgWay <- $$Default;
        NCall ntis <- callInfoReadRss tis (Nat.pow 2 lgWay);
        LET tds: Vector TagDirK edirLgWay <- $$Default;
        NCall ntds <- callDirReadRss tds (Nat.pow 2 edirLgWay);

        LET itm <- doTagMatch _ tag ntis (Nat.pow 2 lgWay);
        LET dtm <- doTagMatch _ tag ntds (Nat.pow 2 edirLgWay);

        Write readLineN: Struct CacheLine <-
          STRUCT { "addr" ::= #addr;
                   "info_hit" ::= #itm!(TagMatch InfoDirK lgWay)@."tm_hit";
                   "info_way" ::= #itm!(TagMatch InfoDirK lgWay)@."tm_way";
                   "info_write" ::= $$false;
                   "info" ::= #itm!(TagMatch InfoDirK lgWay)@."tm_value"!InfoDir@."info";
                   "value_write" ::= $$false;
                   "value" ::= $$Default; (* if info-hit, then will have it next cycle *)
                   "edir_hit" ::= #dtm!(TagMatch dirK edirLgWay)@."tm_hit";
                   "edir_way" ::= #dtm!(TagMatch dirK edirLgWay)@."tm_way";
                   "edir_write" ::= $$false;
                   "dir" ::=
                     (IF #itm!(TagMatch InfoDirK lgWay)@."tm_hit"
                      then #itm!(TagMatch InfoDirK lgWay)@."tm_value"!InfoDir@."dir"
                      else #dtm!(TagMatch dirK edirLgWay)@."tm_value") };

        If (#itm!(TagMatch InfoDirK lgWay)@."tm_hit")
        then (Write readStageN: ReadStage <- rsValueRq;
             Call dataPutRq (STRUCT { "write" ::= $$false;
                                      "addr" ::= {#index,
                                                  #itm!(TagMatch InfoDirK lgWay)@."tm_way"};
                                      "datain" ::= $$Default });
             Retv)
        else (Write readStageN: ReadStage <- rsRsOk; Retv);
        Retv

      with Rule "readData" :=
        Read readStage: ReadStage <- readStageN;
        Assert (#readStage == rsValueRq);
        Write readStageN: ReadStage <- rsRsOk;
        Call data <- dataGetRs();
        Read line: Struct CacheLine <- readLineN;
        Write readLineN: Struct CacheLine <-
          STRUCT { "addr" ::= #line!CacheLine@."addr";
                   "info_hit" ::= #line!CacheLine@."info_hit";
                   "info_way" ::= #line!CacheLine@."info_way";
                   "info_write" ::= #line!CacheLine@."info_write";
                   "info" ::= #line!CacheLine@."info";
                   "value_write" ::= $$false;
                   "value" ::= #data;
                   "edir_hit" ::= #line!CacheLine@."edir_hit";
                   "edir_way" ::= #line!CacheLine@."edir_way";
                   "edir_write" ::= #line!CacheLine@."edir_write";
                   "dir" ::= #line!CacheLine@."dir" };
        Retv
   }.

End Cache.
