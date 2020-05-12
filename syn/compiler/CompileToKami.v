Require Import Numbers.DecimalString.

Require Import Hemiola.Common Hemiola.Index Hemiola.Syntax.
Require Import Hemiola.Ex.TopoTemplate.

Require Import Compiler.HemiolaDeep. (* source *)
Require Import Kami.Lib.Struct Kami Kami.PrimFifo. (* target *)

Set Implicit Arguments.

Lemma Vector_nth_map_comp {A B} (f: A -> B) {n} (v: Vector.t A n) (p: Fin.t n):
  Vector.nth (Vector.map f v) p = f (Vector.nth v p).
Proof.
  induction p.
  - revert n v; refine (@Vector.caseS _ _ _); now simpl.
  - revert n v p IHp; refine (@Vector.caseS _  _ _); now simpl.
Defined.

Import MonadNotations.

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

Fixpoint array_of_list {A} (def: A) (l: list A) sz: Vector.t A sz :=
  match l with
  | nil => vector_repeat sz def
  | a :: l' =>
    match sz with
    | O => Vector.nil _
    | S sz' => Vector.cons _ a _ (@array_of_list A def l' sz')
    end
  end.

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

Section Compile.
  Context `{hcfg: hconfig} `{dv: DecValue} `{hdv: @HDecValue dv hcfg}
          `{oifc: OStateIfc}
          `{het: ExtType}
          `{hoifc: @HOStateIfc dv oifc}
          `{hoifcf: @HOStateIfcFull dv oifc hoifc het}.

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

  Definition MaybeStr (k: Kind) :=
    STRUCT { "valid" :: Bool; "data" :: k }.
  Definition Maybe (k: Kind) := Struct (MaybeStr k).

  Section MSHR.
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
         attrType := {| arg := KAddr; ret := Maybe (Struct DL) |} |}.

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
               (a: Expr var (SyntaxKind KAddr))
               (dl: Expr var (SyntaxKind (Struct DL))): Expr var (SyntaxKind Bool) :=
      (dl!DL@."dl_valid" &&
       dl!DL@."dl_msg"!KMsg@."addr" == a &&
       dl!DL@."dl_rss_recv" == dl!DL@."dl_rss_from")%kami_expr.

    Definition downLockRssFullIter {var}
               (a: Expr var (SyntaxKind KAddr))
               (dls: Expr var (SyntaxKind (Vector (Struct DL) logNumDls)))
      : Expr var (SyntaxKind (Maybe (Struct DL))) :=
      (dlIter (k:= Maybe (Struct DL)) $$Default
              (fun _ dl => STRUCT { "valid" ::= $$true; "data" ::= dl })
              (downLockRssFullF a) dls)%kami_expr.

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
        with Method downLockRssFullN (a: KAddr): Maybe (Struct DL) :=
          Read dls <- "dls";
          LET retv <- downLockRssFullIter #a #dls;
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
          LET oul <- upLockGetIter (#r!TrsfUpDown@."r_dl_addr") #uls;
          LET ul <- #oul!(MaybeStr (Struct UL))@."data";
          Read dls <- "dls";
          LET dli <- getDLSlotIter #dls;
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

      Fixpoint compile_Rule_ost_vars_fix (n: nat) {sz} (htys: Vector.t htype sz)
               (cont: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) htys) ->
                      ActionT var Void) {struct htys}: ActionT var Void :=
        match htys in Vector.t _ sz
              return (HVector.hvec (Vector.map (fun hty => var (kind_of hty)) htys) ->
                      ActionT var Void) -> ActionT var Void with
        | Vector.nil _ => fun cont => cont tt
        | Vector.cons _ hty _ htys =>
          fun cont =>
            (Read ov: (kind_of hty) <- (ostValNameN n);
            compile_Rule_ost_vars_fix
              (S n) htys (fun vars => cont (HVector.hvcons ov vars)))%kami_action
        end cont.

      Definition compile_Rule_ost_vars :=
        compile_Rule_ost_vars_fix O hostf_ty.

      Variables (msgIn: var (Struct KMsg))
                (uln: string) (ul: var (Struct UL))
                (dln: string) (dl: var (Struct DL))
                (ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty)).

      Fixpoint compile_bexp {hbt} (he: hbexp (hbvar_of var) hbt)
        : Expr var (SyntaxKind (kind_of_hbtype hbt)) :=
        (match he with
         | HBConst _ c => Const _ (compile_const c)
         | HVar _ _ v => Var _ (SyntaxKind _) v
         | HIdmId pe => ((compile_bexp pe)!KCIdm@."cidx")
         | HIdmMsg pe => ((compile_bexp pe)!KCIdm@."msg")
         | HObjIdxOf midx => (_truncate_ (compile_bexp midx))
         | HAddrB _ => $0 (** Used only when making an eviction request with a nondet. addr *)
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

      Definition compile_Rule_uplock
                 (cont: var (Struct UL) -> ActionT var Void): ActionT var Void :=
        (Read ul: Struct UL <- uln; cont ul)%kami_action.

      Definition compile_Rule_downlock
                 (cont: var (Struct DL) -> ActionT var Void): ActionT var Void :=
        (Read dl: Struct DL <- dln; cont dl)%kami_action.

      Definition compile_Rule_msg_from (mf: HMsgFrom)
                 (cont: var (Struct KMsg) -> ActionT var Void): ActionT var Void :=
        (match mf with
         | HMsgFromNil =>
           (* This is a hack, just by feeding a random value to the continuation *)
           (LET msgIn <- $$Default; cont msgIn)
         | HMsgFromParent pmidx =>
           (Call msgIn <- (deqFromParent pmidx)(); cont msgIn)
         | HMsgFromChild cmidx =>
           (Call msgIn <- (deqFromChild cmidx)(); cont msgIn)
         | HMsgFromExt emidx =>
           (Call msgIn <- (deqFromExt emidx)(); cont msgIn)
         | HMsgFromUpLock =>
           (Call msgIn <- (deqFromParent (downTo oidx))(); cont msgIn)
         | HMsgFromDownLock cidx =>
           (Call msgIn <- (deqFromChild cidx)(); cont msgIn)
         end)%kami_action.

      Definition compile_Rule_rqrs_prec (rrp: HOPrecR)
                 (cont: ActionT var Void): ActionT var Void :=
        (match rrp with
         | HRqAccepting => (Assert (!(#msgIn!KMsg@."type")); cont)
         | HRsAccepting => (Assert (#msgIn!KMsg@."type"); cont)
         | HUpLockFree =>
           (Call canUl <- (upLockable oidx) (#msgIn!KMsg@."addr"); Assert #canUl; cont)
         | HDownLockFree =>
           (Call canDl <- (downLockable oidx) (#msgIn!KMsg@."addr"); Assert #canDl; cont)
         | HUpLockMsgId _ _ =>
           (Call ul <- (upLockGet oidx) (#msgIn!KMsg@."addr");
           Assert #ul!(MaybeStr (Struct UL))@."valid";
           Write uln <- #ul!(MaybeStr (Struct UL))@."data";
           cont)
         | HUpLockMsg => cont
         | HUpLockIdxBack => cont
         | HUpLockBackNone => cont
         | HDownLockMsgId _ _ =>
           (Call dl <- (downLockGet oidx) (#msgIn!KMsg@."addr");
           Assert #dl!(MaybeStr (Struct DL))@."valid";
           Write dln <- #dl!(MaybeStr (Struct DL))@."data";
           cont)
         | HDownLockMsg => cont
         | HDownLockIdxBack => cont
         | HMsgIdFrom msgId => cont
         | HRssFull =>
           (Call dl <- (downLockRssFull oidx) (#msgIn!KMsg@."addr");
           Assert #dl!(MaybeStr (Struct DL))@."valid";
           Write dln <- #dl!(MaybeStr (Struct DL))@."data";
           cont)
         end)%kami_action.

      Fixpoint compile_Rule_prop_prec (pp: HOPrecP (hvar_of var))
        : Expr var (SyntaxKind Bool) :=
        (match pp with
         | HTrue _ => $$true
         | HAnd pp1 pp2 =>
           (compile_Rule_prop_prec pp1) && (compile_Rule_prop_prec pp2)
         | HOr pp1 pp2 =>
           (compile_Rule_prop_prec pp1) || (compile_Rule_prop_prec pp2)
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

      Fixpoint compile_Rule_prec (rp: HOPrecT (hvar_of var))
               (cont: ActionT var Void): ActionT var Void :=
        match rp with
        | HOPrecAnd prec1 prec2 =>
          let crule2 := compile_Rule_prec prec2 cont in
          compile_Rule_prec prec1 crule2
        | HOPrecRqRs _ rrprec => compile_Rule_rqrs_prec rrprec cont
        | HOPrecProp pprec =>
          (Assert (compile_Rule_prop_prec pprec); cont)%kami_action
        end.

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

      Definition compile_midx_to_cidx (midx: IdxT): Expr var (SyntaxKind KCIdx) :=
        Const _ (compile_midx_to_cidx_const midx).

      Definition compile_midx_to_qidx (midx: IdxT): Expr var (SyntaxKind KQIdx) :=
        Const _ (compile_midx_to_qidx_const midx).

      Definition compile_oidx_to_cidx (oidx: IdxT): Expr var (SyntaxKind KCIdx) :=
        Const _ (compile_oidx_to_cidx_const oidx).

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
                           (** FIXME: [msg] should contain a nondet. address *)
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
                           (** FIXME: [msg] should contain a nondet. address *)
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

      Definition compile_Rule_trs (rtrs: HOTrs): ActionT var Void :=
        match rtrs with
        | HTrsMTrs mtrs => compile_state_trs mtrs
        end.

    End Phoas.

  End ExtComp.

  Context `{CompExtExp}.

  Section WithObj.
    Variables (oidx: IdxT) (uln dln ostin: string).

    Definition ruleNameBase: string := "rule".
    Definition ruleNameI (ridx: IdxT) :=
      (ruleNameBase ++ "_" ++ idx_to_string oidx ++ "_" ++ idx_to_string ridx)%string.

    Local Notation "v <- f ; cont" :=
      (f (fun v => cont)) (at level 99, right associativity, only parsing).
    Local Notation "f ;; cont" :=
      (f cont) (at level 60, right associativity, only parsing).
    Definition compile_Rule (rule: {sr: Hemiola.Syntax.Rule & HRule sr}):
      Attribute (Action Void) :=
      let hr := projT2 rule in
      {| attrName := ruleNameI (rule_idx (projT1 rule));
         attrType :=
           fun var =>
             (ostVars <- compile_Rule_ost_vars ostin;
             msgIn <- compile_Rule_msg_from oidx (hrule_msg_from hr);
             ul <- compile_Rule_uplock uln;
             dl <- compile_Rule_downlock dln;
             compile_Rule_prec
               oidx msgIn uln ul dln dl ostVars (hrule_precond hr (hvar_of var));;
             compile_Rule_trs
               oidx ostin msgIn ul dl ostVars (hrule_trs hr))
      |}.

    Definition compile_Rules (rules: list {sr: Hemiola.Syntax.Rule & HRule sr}):
      list (Attribute (Action Void)) :=
      map compile_Rule rules.

  End WithObj.

  Definition upLockReg (oidx: IdxT): string :=
    "ul" ++ idx_to_string oidx.
  Definition downLockReg (oidx: IdxT): string :=
    "dl" ++ idx_to_string oidx.
  Definition ostIReg (oidx: IdxT): string :=
    "ost" ++ idx_to_string oidx.

  Fixpoint compile_inits (oidx: IdxT) (n: nat) (hts: list htype): list RegInitT :=
    match hts with
    | nil => nil
    | ht :: hts' =>
      {| attrName := ostValNameN (ostIReg oidx) n;
         attrType := RegInitDefault (SyntaxKind (kind_of ht)) |}
        :: compile_inits oidx (S n) hts'
    end.

  Definition compile_OState_init (oidx: IdxT): list RegInitT :=
    {| attrName := upLockReg oidx;
       attrType := RegInitDefault (SyntaxKind (Struct UL)) |}
      :: {| attrName := downLockReg oidx;
            attrType := RegInitDefault (SyntaxKind (Struct DL)) |}
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

  Definition compile_Object (obj: {sobj: Hemiola.Syntax.Object & HObject sobj})
    : Modules :=
    let cregs := compile_OState_init (obj_idx (projT1 obj)) in
    let crules := compile_Rules (obj_idx (projT1 obj))
                                (upLockReg (obj_idx (projT1 obj)))
                                (downLockReg (obj_idx (projT1 obj)))
                                (ostIReg (obj_idx (projT1 obj)))
                                (hobj_rules (projT2 obj)) in
    Mod cregs crules nil.

  Definition compile_Object_with_init
             (obj: {sobj: Hemiola.Syntax.Object & HObject sobj})
             (kinit: list RegInitT) :=
    let crules := compile_Rules (obj_idx (projT1 obj))
                                (upLockReg (obj_idx (projT1 obj)))
                                (downLockReg (obj_idx (projT1 obj)))
                                (ostIReg (obj_idx (projT1 obj)))
                                (hobj_rules (projT2 obj)) in
    Mod kinit crules nil.

  Fixpoint compile_Objects (objs: list {sobj: Hemiola.Syntax.Object & HObject sobj})
    : option Kami.Syntax.Modules :=
    match objs with
    | nil => None
    | obj :: nil => Some (compile_Object obj)
    | obj :: objs' =>
      (let cmod := compile_Object obj in
       cmods <-- compile_Objects objs';
      Some (ConcatMod cmod cmods))
    end.

  Definition compile_System (sys: {ssys: Hemiola.Syntax.System & HSystem ssys})
    : option Kami.Syntax.Modules :=
    compile_Objects (hsys_objs (projT2 sys)).

End Compile.
