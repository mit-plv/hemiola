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
  Variables (oidx: IdxT)
            (* MSB                                  LSB
             * |----------------(addr)----------------|
             * |--(tag)--|--(index)--|---|--(offset)--|
             * |---------|--(dataIndex)--|------------|
             *              (= index + lgWay)
             *)
            (tagSz indexSz offsetSz addrSz: nat)
            (lgWay: nat)
            (infoK dataK: Kind).

  Local Notation "s '+o'" := (s ++ idx_to_string oidx)%string (at level 60).
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

  Definition getVictimN: string := cacheN _++ "getVictim".
  Definition getVictim := MethodSig getVictimN (): CacheLineK.
  Definition removeVictimN: string := cacheN _++ "removeVictim".
  Definition removeVictim := MethodSig removeVictimN (): Void.

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
  Definition victimExN: string := "victimEx"+o.
  Definition victimN: string := "victim"+o.
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
      with Register victimExN: Bool <- Default
      with Register victimN: CacheLineK <- Default
      with Register victimWayN: Bit lgWay <- Default

      with Method readRqN (addr: Bit addrSz): Void :=
        (* Do not allow reads when a write is in progress;
         * OPT: no need to block reads for different addresses. *)
        Read writeStage: WriteStage <- writeStageN;
        Assert (#writeStage == wsNone);
        Read readStage: ReadStage <- readStageN;
        Assert (#readStage == rsNone);

        Read victimEx <- victimExN;
        Read victim: CacheLineK <- victimN;
        If (#victimEx && #victim!CacheLine@."addr" == #addr)
        then (Write readStageN: ReadStage <- rsRsReady;
             Write readLineN <- #victim;
             Retv)
        else (Write readStageN: ReadStage <- rsInfoRq;
             Write readAddrN <- #addr;
             LET index <- getIndex _ addr;
             LET infoRq: Struct (BramRq indexSz TagInfoK) <- STRUCT { "write" ::= $$false;
                                                                      "addr" ::= #index;
                                                                      "datain" ::= $$Default };
             NCall callInfoReadRqs infoRq (Nat.pow 2 lgWay);
             Retv);
        Retv

      with Method readRsN (): CacheLineK :=
        Read readStage: ReadStage <- readStageN;
        Assert (#readStage == rsRsReady);
        Write readStageN: ReadStage <- rsNone;
        Read line: Struct CacheLine <- readLineN;
        Ret #line

      with Method writeRqN (line: CacheLineK): Void :=
        Read writeStage: WriteStage <- writeStageN;
        Assert (#writeStage == wsNone);

        Read victimEx <- victimExN;
        Read victim: CacheLineK <- victimN;
        If (#victimEx && #victim!CacheLine@."addr" == #line!CacheLine@."addr")
        then (Write writeStageN <- wsRsReady;
             Write victimN <- #line; (* update the victim line *)
             Retv)
        else (Write writeStageN <- wsRqAcc;
             Write writeLineN <- #line;
             Retv);
        Retv

      with Method writeRsN (): CacheLineK :=
        Read writeStage: WriteStage <- writeStageN;
        Assert (#writeStage == wsRsReady);
        Write writeStageN <- wsNone;
        Read nline: CacheLineK <- writeLineN;
        Ret #nline

      with Method getVictimN (): CacheLineK :=
        Read victimEx <- victimExN;
        Assert (#victimEx);
        Read victim <- victimN;
        Ret #victim

      with Method removeVictimN (): Void :=
        Read victimEx <- victimExN;
        Assert (#victimEx);
        Write victimExN <- $$false;
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

        Read victimEx <- victimExN;
        Assert (!#victimEx);
        Write victimWayN <- #victimWay;
        LET vtid <- #ntis@[#victimWay];
        LET vtag <- #vtid!(TagValue infoK)@."tag";
        LET vinfo <- #vtid!(TagValue infoK)@."value";
        Write victimN: CacheLineK  <- STRUCT { "addr" ::= buildAddr _ vtag index;
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

        (* handle the responses about the victim line *)
        Read victimEx <- victimExN;
        Assert (!#victimEx);
        Write victimExN <- $$true;

        Call vdata <- dataGetRs ();
        Read victim: CacheLineK <- victimN;
        Write victimN: CacheLineK <- STRUCT { "addr" ::= #victim!CacheLine@."addr";
                                              "info_hit" ::= #victim!CacheLine@."info_hit";
                                              "info_way" ::= #victim!CacheLine@."info_way";
                                              "info_write" ::= #victim!CacheLine@."info_write";
                                              "info" ::= #victim!CacheLine@."info";
                                              "value_write" ::= $$false;
                                              "value" ::= #vdata };

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
