Require Import Numbers.DecimalString.

Require Import Hemiola.Lib.Common Hemiola.Lib.Index Hemiola.Ex.TopoTemplate.
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
  | i :: idx' => idx_to_string idx' ++ "_" ++ nat_to_string i
  end.
(* Eval compute in (idx_to_string (0~>1~>2)). *)

Definition MaybeStr (k: Kind) :=
  STRUCT { "valid" :: Bool; "data" :: k }.
Definition Maybe (k: Kind) := Struct (MaybeStr k).
Definition MaybeNone {var k}: Expr var (SyntaxKind (Maybe k)) :=
  (STRUCT { "valid" ::= $$false; "data" ::= $$Default })%kami_expr.
Definition MaybeSome {var k} (v: Expr var (SyntaxKind k)): Expr var (SyntaxKind (Maybe k)) :=
  (STRUCT { "valid" ::= $$true; "data" ::= v })%kami_expr.

Section Acceptor2.
  Variable acceptorName: string.
  Variables (peltT0 peltT1 eltT: Kind).
  Variables (eltF0: forall {var}, var peltT0 -> Expr var (SyntaxKind eltT))
            (eltF1: forall {var}, var peltT1 -> Expr var (SyntaxKind eltT)).
  Variables (acceptN0 acceptN1 forwardN: string).

  Local Notation "s '+o'" := (s ++ "_" ++ acceptorName)%string (at level 60).

  Local Notation acceptF0 := (MethodSig acceptN0(): peltT0).
  Local Notation acceptF1 := (MethodSig acceptN1(): peltT1).
  Local Notation forward := (MethodSig forwardN(eltT): Void).

  Let rrSz := 1.

  Definition acceptor2: Kami.Syntax.Modules :=
    MODULE {
        Register ("rr"+o): Bit rrSz <- Default
        with Rule "inc_rr"+o :=
          Read rr: Bit rrSz <- "rr"+o;
          Write "rr"+o <- #rr + $1;
          Retv
        with Rule "accept0"+o :=
          Read rr: Bit rrSz <- "rr"+o; Assert (#rr == $0);
          Call pval <- acceptF0(); LET val <- eltF0 pval;
          Call forward(#val); Retv
        with Rule "accept1"+o :=
          Read rr: Bit rrSz <- "rr"+o; Assert (#rr == $1);
          Call pval <- acceptF1(); LET val <- eltF1 pval;
          Call forward(#val); Retv
      }.

End Acceptor2.

Section Acceptor3.
  Variable acceptorName: string.
  Variables (peltT0 peltT1 peltT2 eltT: Kind).
  Variables (eltF0: forall {var}, var peltT0 -> Expr var (SyntaxKind eltT))
            (eltF1: forall {var}, var peltT1 -> Expr var (SyntaxKind eltT))
            (eltF2: forall {var}, var peltT2 -> Expr var (SyntaxKind eltT)).
  Variables (acceptN0 acceptN1 acceptN2 forwardN: string).

  Local Notation "s '+o'" := (s ++ "_" ++ acceptorName)%string (at level 60).

  Local Notation acceptF0 := (MethodSig acceptN0(): peltT0).
  Local Notation acceptF1 := (MethodSig acceptN1(): peltT1).
  Local Notation acceptF2 := (MethodSig acceptN2(): peltT2).
  Local Notation forward := (MethodSig forwardN(eltT): Void).

  Let rrSz := 2.

  Definition acceptor3: Kami.Syntax.Modules :=
    MODULE {
        Register ("rr"+o): Bit rrSz <- Default
        with Rule "inc_rr"+o :=
          Read rr: Bit rrSz <- "rr"+o;
          Write "rr"+o <- IF #rr == $2 then $0 else #rr + $1;
          Retv
        with Rule "accept0"+o :=
          Read rr: Bit rrSz <- "rr"+o; Assert (#rr == $0);
          Call pval <- acceptF0(); LET val <- eltF0 pval;
          Call forward(#val); Retv
        with Rule "accept1"+o :=
          Read rr: Bit rrSz <- "rr"+o; Assert (#rr == $1);
          Call pval <- acceptF1(); LET val <- eltF1 pval;
          Call forward(#val); Retv
        with Rule "accept2"+o :=
          Read rr: Bit rrSz <- "rr"+o; Assert (#rr == $2);
          Call pval <- acceptF2(); LET val <- eltF2 pval;
          Call forward(#val); Retv
      }.

End Acceptor3.

Section Acceptor4.
  Variable acceptorName: string.
  Variables (peltT0 peltT1 peltT2 peltT3 eltT: Kind).
  Variables (eltF0: forall {var}, var peltT0 -> Expr var (SyntaxKind eltT))
            (eltF1: forall {var}, var peltT1 -> Expr var (SyntaxKind eltT))
            (eltF2: forall {var}, var peltT2 -> Expr var (SyntaxKind eltT))
            (eltF3: forall {var}, var peltT3 -> Expr var (SyntaxKind eltT)).
  Variables (acceptN0 acceptN1 acceptN2 acceptN3 forwardN: string).

  Local Notation "s '+o'" := (s ++ "_" ++ acceptorName)%string (at level 60).

  Local Notation acceptF0 := (MethodSig acceptN0(): peltT0).
  Local Notation acceptF1 := (MethodSig acceptN1(): peltT1).
  Local Notation acceptF2 := (MethodSig acceptN2(): peltT2).
  Local Notation acceptF3 := (MethodSig acceptN3(): peltT3).
  Local Notation forward := (MethodSig forwardN(eltT): Void).

  Let rrSz := 2.

  Definition acceptor4: Kami.Syntax.Modules :=
    MODULE {
        Register ("rr"+o): Bit rrSz <- Default
        with Rule "inc_rr"+o :=
          Read rr: Bit rrSz <- "rr"+o;
          Write "rr"+o <- #rr + $1;
          Retv
        with Rule "accept0"+o :=
          Read rr: Bit rrSz <- "rr"+o; Assert (#rr == $0);
          Call pval <- acceptF0(); LET val <- eltF0 pval;
          Call forward(#val); Retv
        with Rule "accept1"+o :=
          Read rr: Bit rrSz <- "rr"+o; Assert (#rr == $1);
          Call pval <- acceptF1(); LET val <- eltF1 pval;
          Call forward(#val); Retv
        with Rule "accept2"+o :=
          Read rr: Bit rrSz <- "rr"+o; Assert (#rr == $2);
          Call pval <- acceptF2(); LET val <- eltF2 pval;
          Call forward(#val); Retv
        with Rule "accept3"+o :=
          Read rr: Bit rrSz <- "rr"+o; Assert (#rr == $3);
          Call pval <- acceptF3(); LET val <- eltF3 pval;
          Call forward(#val); Retv
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

  Definition MSHRStatus := Bit 3.
  Definition mshrInvalid {var}: Expr var (SyntaxKind MSHRStatus) := ($0)%kami_expr.
  Definition mshrWaiting {var}: Expr var (SyntaxKind MSHRStatus) := ($1)%kami_expr.
  Definition mshrFirstWait {var}: Expr var (SyntaxKind MSHRStatus) := ($2)%kami_expr.
  (* Definition mshrRetrying {var}: Expr var (SyntaxKind MSHRStatus) := ($3)%kami_expr. *)
  Definition mshrOwned {var}: Expr var (SyntaxKind MSHRStatus) := ($4)%kami_expr.
  Definition mshrValid {var}: Expr var (SyntaxKind MSHRStatus) := ($5)%kami_expr.
  Definition mshrReleasing {var}: Expr var (SyntaxKind MSHRStatus) := ($6)%kami_expr.

  Local Notation "s '+o'" := (s ++ "_" ++ idx_to_string oidx)%string (at level 60).
  Local Notation "s1 _++ s2" := (s1 ++ "_" ++ s2)%string (at level 60).

  Variable numPRqs numCRqs: nat.
  Let predNumSlots := numPRqs + numCRqs - 1.
  Let numSlots := S predNumSlots.
  Let slotSz := S (Nat.log2 predNumSlots).
  Let MshrId := Bit slotSz.

  Definition MSHR :=
    STRUCT { "m_is_ul" :: Bool;
             (** Heads-up: when [m_status == mshrValid] then the index refers to the
              * response queue; if [m_status == mshrWaiting || m_status == mshrFirstWait] then
              * it refers to the input queue, which will be used when [getWait] is called. *)
             "m_qidx" :: KQIdx;
             "m_rsb" :: Bool;
             "m_dl_rss_from" :: KCBv;
             "m_dl_rss_recv" :: KCBv }.

  Definition MSHRAddr := KAddr.
  Definition MSHRNext := Maybe MshrId.
  Definition MSHRRq := KMsg.
  (** Heads-up: in principle all the response messages (from children) should be stored in
   * an MSHR slot, but in cache coherence the line value of the response is required only
   * when the parent gets the dirty line value from the exclusive child.
   * Therefore, in order for space optimization, we only store a single response message. *)
  Definition MSHRRs := KMsg. (* Array (Struct KMsg) hcfg_children_max *)

  Definition getMSHR: Attribute SignatureT := MethodSig ("getMSHR"+o)(MshrId): Struct MSHR.
  Definition getMSHRRq: Attribute SignatureT := MethodSig ("getMSHRRq"+o)(MshrId): Struct KMsg.
  Definition getMSHRFirstRs: Attribute SignatureT :=
    MethodSig ("getMSHRFirstRs"+o)(MshrId): Struct KMsg.

  Definition PreMSHR :=
    STRUCT { "r_id" :: MshrId;
             "r_msg" :: Struct KMsg;
             "r_msg_from" :: KQIdx }.
  Let PreMSHRK := Struct PreMSHR.

  Definition GetSlot :=
    STRUCT { "s_has_slot" :: Bool;
             "s_conflict" :: Bool; (* set if there is an address conflict *)
             "s_id" :: MshrId }.
  Let GetSlotK := Struct GetSlot.
  Definition getPRqSlot: Attribute SignatureT := MethodSig ("getPRqSlot"+o)(PreMSHRK): GetSlotK.
  Definition getCRqSlot: Attribute SignatureT := MethodSig ("getCRqSlot"+o)(PreMSHRK): GetSlotK.

  Definition getWait: Attribute SignatureT := MethodSig ("getWait"+o)(): PreMSHRK.

  Definition RegUL :=
    STRUCT { "r_id" :: MshrId;
             "r_ul_rsb" :: Bool;
             "r_ul_rsbTo" :: KCIdx }.
  Let RegULK := Struct RegUL.
  Definition registerUL: Attribute SignatureT := MethodSig ("registerUL"+o)(RegULK): Void.

  Definition RegDL :=
    STRUCT { "r_id" :: MshrId;
             "r_dl_rss_from" :: KCBv;
             "r_dl_rsb" :: Bool;
             "r_dl_rsbTo" :: KQIdx }.
  Let RegDLK := Struct RegDL.
  Definition registerDL: Attribute SignatureT := MethodSig ("registerDL"+o)(RegDLK): Void.

  Definition canImm: Attribute SignatureT := MethodSig ("canImm"+o)(KAddr): Void.
  Definition setULImm: Attribute SignatureT := MethodSig ("setULImm"+o)(Struct KMsg): Void.

  Definition TrsfUpDown :=
    STRUCT { "r_id" :: MshrId; "r_dl_rss_from" :: KCBv }.
  Let TrsfUpDownK := Struct TrsfUpDown.
  Definition transferUpDown: Attribute SignatureT :=
    MethodSig ("transferUpDown"+o)(TrsfUpDownK): Void.

  Definition AddRs :=
    STRUCT { "r_midx" :: KCIdx; "r_msg" :: Struct KMsg }.
  Definition addRs: Attribute SignatureT := MethodSig ("addRs"+o)(Struct AddRs): Void.

  Definition getULReady: Attribute SignatureT := MethodSig ("getULReady"+o)(KAddr): MshrId.
  Definition DLReady :=
    STRUCT { "r_id" :: MshrId; "r_addr" :: KAddr }.
  Let DLReadyK := Struct DLReady.
  Definition getDLReady: Attribute SignatureT := MethodSig ("getDLReady"+o)(): DLReadyK.

  Definition startRelease: Attribute SignatureT := MethodSig ("startRelease"+o)(MshrId): Void.
  Definition releaseMSHR: Attribute SignatureT := MethodSig ("releaseMSHR"+o)(MshrId): Void.

  Section Iterators.

    Section One.
      Context {var: Kind -> Type} {k ek: Kind}.
      Variables (lc: Expr var (SyntaxKind k))
                (tc: nat -> Expr var (SyntaxKind ek) -> Expr var (SyntaxKind k))
                (cond: Expr var (SyntaxKind ek) -> Expr var (SyntaxKind Bool))
                (el: Expr var (SyntaxKind (Array ek numSlots))).

      Fixpoint mfix (n: nat): Expr var (SyntaxKind k) :=
        (match n with
         | O => lc
         | S n' =>
           let m := el#[$$(natToWord slotSz (numSlots - n))] in
           (IF (cond m) then tc (numSlots - n)%nat m else mfix n')
         end)%kami_expr.
      Definition miter := mfix numSlots.

      Fixpoint pmfix (n: nat): Expr var (SyntaxKind k) :=
        (match n with
         | O => lc
         | S n' =>
           let m := el#[$$(natToWord slotSz (numPRqs - n))] in
           (IF (cond m) then tc (numPRqs - n)%nat m else pmfix n')
         end)%kami_expr.
      Definition pmiter := pmfix numPRqs.

      Fixpoint cmfix (n: nat): Expr var (SyntaxKind k) :=
        (match n with
         | O => lc
         | S n' =>
           let m := el#[$$(natToWord slotSz (numCRqs - n + numPRqs))] in
           (IF (cond m) then tc (numCRqs - n + numPRqs)%nat m else cmfix n')
         end)%kami_expr.
      Definition cmiter := cmfix numCRqs.

    End One.

    Definition miterM {var k} := @miter var k (Struct MSHR).
    Definition pmiterM {var k} := @pmiter var k (Struct MSHR).
    Definition cmiterM {var k} := @cmiter var k (Struct MSHR).
    Definition miterS {var k} := @miter var k MSHRStatus.
    Definition pmiterS {var k} := @pmiter var k MSHRStatus.
    Definition cmiterS {var k} := @cmiter var k MSHRStatus.

    Section Two.
      Context {var: Kind -> Type} {k ek1 ek2: Kind}.
      Variables (lc: Expr var (SyntaxKind k))
                (tc: nat -> Expr var (SyntaxKind ek1) ->
                     Expr var (SyntaxKind k))
                (cond: Expr var (SyntaxKind ek1) ->
                       Expr var (SyntaxKind ek2) ->
                       Expr var (SyntaxKind Bool))
                (el1: Expr var (SyntaxKind (Array ek1 numSlots)))
                (el2: Expr var (SyntaxKind (Array ek2 numSlots))).

      Fixpoint mfix2 (n: nat): Expr var (SyntaxKind k) :=
        (match n with
         | O => lc
         | S n' =>
           let m := el1#[$$(natToWord slotSz (numSlots - n))] in
           let st := el2#[$$(natToWord slotSz (numSlots - n))] in
           (IF (cond m st) then tc (numSlots - n)%nat m else mfix2 n')
         end)%kami_expr.
      Definition miter2 := mfix2 numSlots.

      Fixpoint pmfix2 (n: nat): Expr var (SyntaxKind k) :=
        (match n with
         | O => lc
         | S n' =>
           let m := el1#[$$(natToWord slotSz (numPRqs - n))] in
           let st := el2#[$$(natToWord slotSz (numPRqs - n))] in
           (IF (cond m st) then tc (numPRqs - n)%nat m else pmfix2 n')
         end)%kami_expr.
      Definition pmiter2 := pmfix2 numPRqs.

      Fixpoint cmfix2 (n: nat): Expr var (SyntaxKind k) :=
        (match n with
         | O => lc
         | S n' =>
           let m := el1#[$$(natToWord slotSz (numCRqs - n + numPRqs))] in
           let st := el2#[$$(natToWord slotSz (numCRqs - n + numPRqs))] in
           (IF (cond m st) then tc (numCRqs - n + numPRqs)%nat m else cmfix2 n')
         end)%kami_expr.
      Definition cmiter2 := cmfix2 numCRqs.

    End Two.

    Definition miterMS {var k} := @miter2 var k (Struct MSHR) MSHRStatus.
    Definition pmiterMS {var k} := @pmiter2 var k (Struct MSHR) MSHRStatus.
    Definition cmiterMS {var k} := @cmiter2 var k (Struct MSHR) MSHRStatus.
    Definition miterAS {var k} := @miter2 var k MSHRAddr MSHRStatus.
    Definition pmiterAS {var k} := @pmiter2 var k MSHRAddr MSHRStatus.
    Definition cmiterAS {var k} := @cmiter2 var k MSHRAddr MSHRStatus.

    Section Three.
      Context {var: Kind -> Type} {k ek1 ek2 ek3: Kind}.
      Variables (lc: Expr var (SyntaxKind k))
                (tc: nat -> Expr var (SyntaxKind ek1) ->
                     Expr var (SyntaxKind k))
                (cond: Expr var (SyntaxKind ek1) ->
                       Expr var (SyntaxKind ek2) ->
                       Expr var (SyntaxKind ek3) ->
                       Expr var (SyntaxKind Bool))
                (el1: Expr var (SyntaxKind (Array ek1 numSlots)))
                (el2: Expr var (SyntaxKind (Array ek2 numSlots)))
                (el3: Expr var (SyntaxKind (Array ek3 numSlots))).

      Fixpoint mfix3 (n: nat): Expr var (SyntaxKind k) :=
        (match n with
         | O => lc
         | S n' =>
           let m := el1#[$$(natToWord slotSz (numSlots - n))] in
           let st := el2#[$$(natToWord slotSz (numSlots - n))] in
           let nx := el3#[$$(natToWord slotSz (numSlots - n))] in
           (IF (cond m st nx) then tc (numSlots - n)%nat m else mfix3 n')
         end)%kami_expr.
      Definition miter3 := mfix3 numSlots.

      Fixpoint pmfix3 (n: nat): Expr var (SyntaxKind k) :=
        (match n with
         | O => lc
         | S n' =>
           let m := el1#[$$(natToWord slotSz (numPRqs - n))] in
           let st := el2#[$$(natToWord slotSz (numPRqs - n))] in
           let nx := el3#[$$(natToWord slotSz (numPRqs - n))] in
           (IF (cond m st nx) then tc (numPRqs - n)%nat m else pmfix3 n')
         end)%kami_expr.
      Definition pmiter3 := pmfix3 numPRqs.

      Fixpoint cmfix3 (n: nat): Expr var (SyntaxKind k) :=
        (match n with
         | O => lc
         | S n' =>
           let m := el1#[$$(natToWord slotSz (numCRqs - n + numPRqs))] in
           let st := el2#[$$(natToWord slotSz (numCRqs - n + numPRqs))] in
           let nx := el3#[$$(natToWord slotSz (numCRqs - n + numPRqs))] in
           (IF (cond m st nx) then tc (numCRqs - n + numPRqs)%nat m else cmfix3 n')
         end)%kami_expr.
      Definition cmiter3 := cmfix3 numCRqs.
    End Three.

    Definition miterMAS {var k} := @miter3 var k (Struct MSHR) MSHRAddr MSHRStatus.
    Definition pmiterMAS {var k} := @pmiter3 var k (Struct MSHR) MSHRAddr MSHRStatus.
    Definition cmiterMAS {var k} := @cmiter3 var k (Struct MSHR) MSHRAddr MSHRStatus.
    Definition miterASN {var k} := @miter3 var k MSHRAddr MSHRStatus MSHRNext.
    Definition pmiterASN {var k} := @pmiter3 var k MSHRAddr MSHRStatus MSHRNext.
    Definition cmiterASN {var k} := @cmiter3 var k MSHRAddr MSHRStatus MSHRNext.

    Section Four.
      Context {var: Kind -> Type} {k ek1 ek2 ek3 ek4: Kind}.
      Variables (lc: Expr var (SyntaxKind k))
                (tc: nat -> Expr var (SyntaxKind ek1) ->
                     Expr var (SyntaxKind k))
                (cond: Expr var (SyntaxKind ek1) ->
                       Expr var (SyntaxKind ek2) ->
                       Expr var (SyntaxKind ek3) ->
                       Expr var (SyntaxKind ek4) ->
                       Expr var (SyntaxKind Bool))
                (el1: Expr var (SyntaxKind (Array ek1 numSlots)))
                (el2: Expr var (SyntaxKind (Array ek2 numSlots)))
                (el3: Expr var (SyntaxKind (Array ek3 numSlots)))
                (el4: Expr var (SyntaxKind (Array ek4 numSlots))).

      Fixpoint mfix4 (n: nat): Expr var (SyntaxKind k) :=
        (match n with
         | O => lc
         | S n' =>
           let m := el1#[$$(natToWord slotSz (numSlots - n))] in
           let a := el2#[$$(natToWord slotSz (numSlots - n))] in
           let st := el3#[$$(natToWord slotSz (numSlots - n))] in
           let nx := el4#[$$(natToWord slotSz (numSlots - n))] in
           (IF (cond m a st nx) then tc (numSlots - n)%nat m else mfix4 n')
         end)%kami_expr.
      Definition miter4 := mfix4 numSlots.

      Fixpoint pmfix4 (n: nat): Expr var (SyntaxKind k) :=
        (match n with
         | O => lc
         | S n' =>
           let m := el1#[$$(natToWord slotSz (numPRqs - n))] in
           let a := el2#[$$(natToWord slotSz (numPRqs - n))] in
           let st := el3#[$$(natToWord slotSz (numPRqs - n))] in
           let nx := el4#[$$(natToWord slotSz (numPRqs - n))] in
           (IF (cond m a st nx) then tc (numPRqs - n)%nat m else pmfix4 n')
         end)%kami_expr.
      Definition pmiter4 := pmfix4 numPRqs.

      Fixpoint cmfix4 (n: nat): Expr var (SyntaxKind k) :=
        (match n with
         | O => lc
         | S n' =>
           let m := el1#[$$(natToWord slotSz (numCRqs - n + numPRqs))] in
           let a := el2#[$$(natToWord slotSz (numCRqs - n + numPRqs))] in
           let st := el3#[$$(natToWord slotSz (numCRqs - n + numPRqs))] in
           let nx := el4#[$$(natToWord slotSz (numCRqs - n + numPRqs))] in
           (IF (cond m a st nx) then tc (numCRqs - n + numPRqs)%nat m else cmfix4 n')
         end)%kami_expr.
      Definition cmiter4 := cmfix4 numCRqs.
    End Four.

    Definition miterMASN {var k} := @miter4 var k (Struct MSHR) MSHRAddr MSHRStatus MSHRNext.
    Definition pmiterMASN {var k} := @pmiter4 var k (Struct MSHR) MSHRAddr MSHRStatus MSHRNext.
    Definition cmiterMASN {var k} := @cmiter4 var k (Struct MSHR) MSHRAddr MSHRStatus MSHRNext.

  End Iterators.

  Variable (conflictF: forall ty, Expr ty (SyntaxKind KAddr) ->
                                  Expr ty (SyntaxKind KAddr) ->
                                  Expr ty (SyntaxKind Bool)).

  Definition mshrsL1: Kami.Syntax.Modules :=
    MODULE {
        Register ("mshrs"+o): Array (Struct MSHR) numSlots <- Default
        with Register ("maddrs"+o): Array MSHRAddr numSlots <- Default
        with Register ("msts"+o): Array MSHRStatus numSlots <- Default
        with Register ("mnexts"+o): Array MSHRNext numSlots <- Default
        with Register ("rqs"+o): Array (Struct KMsg) numSlots <- Default

        with Method ("getMSHR"+o)(mid: MshrId): Struct MSHR :=
          Read mshrs: Array (Struct MSHR) numSlots <- "mshrs"+o;
          Ret #mshrs#[#mid]
        with Method ("getMSHRRq"+o)(mid: MshrId): Struct KMsg :=
          Read rqs: Array (Struct MSHRRq) numSlots <- "rqs"+o;
          Ret #rqs#[#mid]

        with Method ("getPRqSlot"+o)(pmshr: PreMSHRK): GetSlotK :=
          Read mshrs <- "mshrs"+o;
          Read maddrs <- "maddrs"+o;
          Read msts <- "msts"+o;
          Read mnexts <- "mnexts"+o;
          LET mmid <- (pmiterS MaybeNone
                               (fun n _ => MaybeSome $n)
                               (fun st => st == mshrInvalid)
                               #msts);
          LET hasSlot <- #mmid!(MaybeStr MshrId)@."valid";
          LET mid <- #mmid!(MaybeStr MshrId)@."data";
          LET addr <- #pmshr!PreMSHR@."r_msg"!KMsg@."addr";

          (* Stall when either
           * 1) an index-equivalent line is in the pipeline or
           * 2) a same-address line is in the pipeline -- should not become to
           *    the waiting mode in this case, since a downlock must proceed
           *    even when the uplock is set. *)
          LET stall <- (miterAS $$false
                                (fun _ _ => $$true)
                                (fun a st =>
                                   ((st == mshrOwned) || (st == mshrReleasing)) &&
                                   ((conflictF a (#addr)) || (a == #addr)))
                                #maddrs #msts);

          (* Conflict when a valid downlock exists ([cmmid]).
           * Find the last of the chain when conflict ([pmid]). *)
          LET cmmid <- (miterMAS MaybeNone
                                 (fun i m => MaybeSome $i)
                                 (fun m a st => (st == mshrValid) &&
                                                (!(m!MSHR@."m_is_ul")) &&
                                                a == #addr)
                                 #mshrs #maddrs #msts);
          LET conflict <- #cmmid!(MaybeStr MshrId)@."valid";
          LET ret: GetSlotK <- STRUCT { "s_has_slot" ::= #hasSlot && !#stall;
                                        "s_conflict" ::= #conflict;
                                        "s_id" ::= #mid };

          If (#hasSlot && !#stall)
          then (Write "mshrs"+o <-
                #mshrs#[#mid <- STRUCT { "m_is_ul" ::= $$Default;
                                         "m_qidx" ::= #pmshr!PreMSHR@."r_msg_from";
                                         "m_rsb" ::= $$Default;
                                         "m_dl_rss_from" ::= $$Default;
                                         "m_dl_rss_recv" ::= $$Default }];
               Write "maddrs"+o <- #maddrs#[#mid <- #pmshr!PreMSHR@."r_msg"!KMsg@."addr"];
               Write "msts"+o <- #msts#[#mid <- (IF #conflict then mshrWaiting else mshrOwned)];
               Read rqs: Array (Struct KMsg) numSlots <- "rqs"+o;
               Write "rqs"+o <- #rqs#[#mid <- #pmshr!PreMSHR@."r_msg"];

               If (#conflict)
               then (LET pmid: MshrId <-
                               (miterASN $$Default
                                         (fun i m => $i)
                                         (fun a st nx =>
                                            (st != mshrInvalid) &&
                                            (!(nx!(MaybeStr MshrId)@."valid")) &&
                                            a == #addr)
                                         #maddrs #msts #mnexts);
                    LET pnext <- #mnexts#[#pmid];
                    Write "mnexts"+o <- #mnexts#[#pmid <- (MaybeSome #mid)];
                    Retv);
               Retv);
          Ret #ret

        with Method ("getCRqSlot"+o)(pmshr: PreMSHRK): GetSlotK :=
          Read mshrs <- "mshrs"+o;
          Read maddrs <- "maddrs"+o;
          Read msts <- "msts"+o;
          Read mnexts <- "mnexts"+o;
          LET mmid <- (cmiterMS MaybeNone
                               (fun n _ => MaybeSome $n)
                               (fun m st => st == mshrInvalid)
                               #mshrs #msts);
          LET hasSlot <- #mmid!(MaybeStr MshrId)@."valid";
          LET mid <- #mmid!(MaybeStr MshrId)@."data";
          LET addr <- #pmshr!PreMSHR@."r_msg"!KMsg@."addr";

          (* Should stall when an index-equivalent line is in the pipeline *)
          LET stall <- (miterAS $$false
                                (fun _ _ => $$true)
                                (fun a st =>
                                   ((st == mshrOwned) || (st == mshrReleasing)) &&
                                   conflictF a (#addr))
                                #maddrs #msts);

          LET cmmidUL <- (cmiterMASN MaybeNone
                                     (fun i m => MaybeSome $i)
                                     (fun m a st nx =>
                                        (st != mshrInvalid) &&
                                        (!(nx!(MaybeStr MshrId)@."valid")) &&
                                        (m!MSHR@."m_is_ul") && a == #addr)
                                     #mshrs #maddrs #msts #mnexts);
          LET cmmidDL <- (miterMASN MaybeNone
                                    (fun i m => MaybeSome $i)
                                    (fun m a st nx =>
                                       (st != mshrInvalid) &&
                                       (!(nx!(MaybeStr MshrId)@."valid")) &&
                                       (!(m!MSHR@."m_is_ul")) &&
                                       a == #addr)
                                    #mshrs #maddrs #msts #mnexts);
          LET conflictUL <- #cmmidUL!(MaybeStr MshrId)@."valid";
          LET conflictDL <- #cmmidDL!(MaybeStr MshrId)@."valid";
          LET conflict <- #conflictUL || #conflictDL;
          LET ret: GetSlotK <- STRUCT { "s_has_slot" ::= #hasSlot && !#stall;
                                        "s_conflict" ::= #conflict;
                                        "s_id" ::= #mid };

          If (#hasSlot && !#stall)
          then (Write "mshrs"+o <-
                #mshrs#[#mid <- STRUCT { "m_is_ul" ::= $$Default;
                                         "m_qidx" ::= #pmshr!PreMSHR@."r_msg_from";
                                         "m_rsb" ::= $$Default;
                                         "m_dl_rss_from" ::= $$Default;
                                         "m_dl_rss_recv" ::= $$Default }];
               Write "maddrs"+o <- #maddrs#[#mid <- #pmshr!PreMSHR@."r_msg"!KMsg@."addr"];
               Write "msts"+o <- #msts#[#mid <- (IF #conflict then mshrWaiting else mshrOwned)];
               Read rqs: Array (Struct KMsg) numSlots <- "rqs"+o;
               Write "rqs"+o <- #rqs#[#mid <- #pmshr!PreMSHR@."r_msg"];
               If (#conflict)
               then (LET pmid <- (IF #conflictUL
                                  then #cmmidUL!(MaybeStr MshrId)@."data"
                                  else #cmmidDL!(MaybeStr MshrId)@."data");
                    LET pnext <- #mnexts#[#pmid];
                    Write "mnexts"+o <- #mnexts#[#pmid <- (MaybeSome #mid)];
                    Retv);
               Retv);
          Ret #ret

        with Method ("getWait"+o)(): PreMSHRK :=
          Read mshrs <- "mshrs"+o;
          Read maddrs <- "maddrs"+o;
          Read msts <- "msts"+o;
          Read rqs: Array (Struct KMsg) numSlots <- "rqs"+o;

          LET mwait <- (miterMS MaybeNone
                               (fun i _ => MaybeSome $i)
                               (fun m st => st == mshrFirstWait)
                               #mshrs #msts);
          Assert (#mwait!(MaybeStr MshrId)@."valid");
          LET mid <- #mwait!(MaybeStr MshrId)@."data";
          LET mshr <- #mshrs#[#mid];
          LET addr <- #maddrs#[#mid];
          LET rq <- #rqs#[#mid];

          (* Still must wait when either
           * 1) a same-address line is in progress or
           * 2) an index-equivalent line is in the pipeline. *)
          LET stall <- (miterAS $$false
                                (fun _ _ => $$true)
                                (fun a st =>
                                   ((st >= mshrOwned) && (a == #addr)) ||
                                   (((st == mshrOwned) || st == mshrReleasing) &&
                                    (conflictF a (#addr))))
                                #maddrs #msts);
          Assert !#stall;

          Write "msts"+o <- #msts#[#mid <- mshrOwned];
          LET pre: PreMSHRK <- STRUCT { "r_id" ::= #mid;
                                        "r_msg" ::= #rq;
                                        "r_msg_from" ::= #mshr!MSHR@."m_qidx" };
          Ret #pre

        with Method ("registerUL"+o)(ul: RegULK): Void :=
          Read mshrs: Array (Struct MSHR) numSlots <- "mshrs"+o;
          Read msts: Array MSHRStatus numSlots <- "msts"+o;
          LET mid <- #ul!RegUL@."r_id";
          Write "mshrs"+o <-
          #mshrs#[#mid <- STRUCT { "m_is_ul" ::= $$true;
                                   (* Concatenating [$downIdx] is very important here;
                                    * when it turns into a downlock (by [transferUpDown])
                                    * it should have a precise [KQIdx] value. *)
                                   "m_qidx" ::= {$downIdx, (#ul!RegUL@."r_ul_rsbTo")};
                                   "m_rsb" ::= #ul!RegUL@."r_ul_rsb";
                                   "m_dl_rss_from" ::= $$Default;
                                   "m_dl_rss_recv" ::= $$Default }];
          Write "msts"+o <- #msts#[#mid <- mshrValid];
          Retv

        with Method ("canImm"+o)(addr: KAddr): Void :=
          Read maddrs <- "maddrs"+o;
          Read msts <- "msts"+o;
          Read mnexts <- "mnexts"+o;
          LET mmid <- (cmiterS MaybeNone
                               (fun n _ => MaybeSome $n)
                               (fun st => st == mshrInvalid)
                               #msts);
          Assert (#mmid!(MaybeStr MshrId)@."valid"); (* Has a slot *)
          LET cmmid <- (miterASN MaybeNone
                                 (fun i m => MaybeSome $i)
                                 (fun a st nx =>
                                    (st != mshrInvalid) &&
                                    (!(nx!(MaybeStr MshrId)@."valid")) &&
                                    a == #addr)
                                 #maddrs #msts #mnexts);
          Assert !(#cmmid!(MaybeStr MshrId)@."valid"); (* No conflicts with the other MSHRs *)
          Retv

        with Method ("setULImm"+o)(msg: Struct KMsg): Void :=
          Read mshrs <- "mshrs"+o;
          Read maddrs <- "maddrs"+o;
          Read msts <- "msts"+o;
          Read rqs: Array (Struct KMsg) numSlots <- "rqs"+o;
          LET mmid <- (cmiterMS MaybeNone
                               (fun n _ => MaybeSome $n)
                               (fun m st => st == mshrInvalid)
                               #mshrs #msts);
          Assert (#mmid!(MaybeStr MshrId)@."valid"); (* Has a slot *)
          LET mid <- #mmid!(MaybeStr MshrId)@."data";
          LET addr <- #msg!KMsg@."addr";
          LET cmmid <- (miterAS MaybeNone
                                (fun i m => MaybeSome $i)
                                (fun a st => (st != mshrInvalid) && a == #addr)
                                #maddrs #msts);
          Assert !(#cmmid!(MaybeStr MshrId)@."valid"); (* No conflicts with the other MSHRs *)
          Write "mshrs"+o <- #mshrs#[#mid <- STRUCT { "m_is_ul" ::= $$true;
                                                      "m_qidx" ::= $$Default;
                                                      "m_rsb" ::= $$false;
                                                      "m_dl_rss_from" ::= $$Default;
                                                      "m_dl_rss_recv" ::= $$Default }];
          Write "maddrs"+o <- #maddrs#[#mid <- #msg!KMsg@."addr"];
          Write "msts"+o <- #msts#[#mid <- mshrValid];
          Write "rqs"+o <- #rqs#[#mid <- #msg];
          Retv

        with Method ("getULReady"+o)(addr: KAddr): MshrId :=
          Read mshrs <- "mshrs"+o;
          Read maddrs <- "maddrs"+o;
          Read msts <- "msts"+o;

          (* Should stall if either
           * 1) an index-equivalent line is in the pipeline or
           * 2) there is a downlock with the same address. *)
          LET stall <- (miterMAS $$false
                                 (fun _ _ => $$true)
                                 (fun m a st =>
                                    (((st == mshrOwned) || st == mshrReleasing) &&
                                     conflictF a (#addr)) ||
                                    ((st >= mshrOwned) && (!(m!MSHR@."m_is_ul")) &&
                                     a == #addr))
                                 #mshrs #maddrs #msts);
          Assert !#stall;

          (* [cmiter] is used below, since PRq cannot make any uplocks. *)
          LET mmidUL <- (cmiterMAS MaybeNone
                                   (fun n _ => MaybeSome $n)
                                   (fun m a st =>
                                      (st == mshrValid) && m!MSHR@."m_is_ul" && a == #addr)
                                   #mshrs #maddrs #msts);
          Assert (#mmidUL!(MaybeStr MshrId)@."valid");
          LET mid <- #mmidUL!(MaybeStr MshrId)@."data";
          Ret #mid

        with Method ("startRelease"+o)(mid: MshrId): Void :=
          Read msts: Array MSHRStatus numSlots <- "msts"+o;
          Write "msts"+o <- #msts#[#mid <- mshrReleasing];
          Retv

        with Method ("releaseMSHR"+o)(mid: MshrId): Void :=
          Read mshrs: Array (Struct MSHR) numSlots <- "mshrs"+o;
          Read msts: Array MSHRStatus numSlots <- "msts"+o;
          Read mnexts: Array MSHRNext numSlots <- "mnexts"+o;
          Write "mshrs"+o <- #mshrs#[#mid <- $$Default];
          Write "mnexts"+o <- #mnexts#[#mid <- $$Default];

          LET msts1 <- #msts#[#mid <- $$Default];
          LET next <- #mnexts#[#mid];
          If (#next!(MaybeStr MshrId)@."valid")
          then (LET cmid <- #next!(MaybeStr MshrId)@."data";
               LET msts2 <- #msts1#[#cmid <- mshrFirstWait];
               Ret #msts2)
          else (Ret #msts1) as nmsts;
          Write "msts"+o <- #nmsts;
          Retv }.

  Definition mshrsLi: Kami.Syntax.Modules :=
    MODULE {
        Register ("mshrs"+o): Array (Struct MSHR) numSlots <- Default
        with Register ("maddrs"+o): Array MSHRAddr numSlots <- Default
        with Register ("msts"+o): Array MSHRStatus numSlots <- Default
        with Register ("mnexts"+o): Array MSHRNext numSlots <- Default
        with Register ("rqs"+o): Array (Struct MSHRRq) numSlots <- Default
        with Register ("rss"+o): Array (Struct MSHRRs) numSlots <- Default

        with Method ("getMSHR"+o)(mid: MshrId): Struct MSHR :=
          Read mshrs: Array (Struct MSHR) numSlots <- "mshrs"+o;
          Ret #mshrs#[#mid]
        with Method ("getMSHRRq"+o)(mid: MshrId): Struct KMsg :=
          Read rqs: Array (Struct MSHRRq) numSlots <- "rqs"+o;
          Ret #rqs#[#mid]
        with Method ("getMSHRFirstRs"+o)(mid: MshrId): Struct KMsg :=
          Read rss: Array (Struct MSHRRs) numSlots <- "rss"+o;
          Ret #rss#[#mid]

        with Method ("getPRqSlot"+o)(pmshr: PreMSHRK): GetSlotK :=
          Read mshrs <- "mshrs"+o;
          Read maddrs <- "maddrs"+o;
          Read msts <- "msts"+o;
          Read mnexts <- "mnexts"+o;
          LET mmid <- (pmiterS MaybeNone
                               (fun n _ => MaybeSome $n)
                               (fun st => st == mshrInvalid)
                               #msts);
          LET hasSlot <- #mmid!(MaybeStr MshrId)@."valid";
          LET mid <- #mmid!(MaybeStr MshrId)@."data";
          LET addr <- #pmshr!PreMSHR@."r_msg"!KMsg@."addr";

          (* Stall when either
           * 1) an index-equivalent line is in the pipeline or
           * 2) a same-address line is in the pipeline -- should not become to
           *    the waiting mode in this case, since a downlock must proceed
           *    even when the uplock is set. *)
          LET stall <- (miterAS $$false
                                (fun _ _ => $$true)
                                (fun a st =>
                                   ((st == mshrOwned) || (st == mshrReleasing)) &&
                                   ((conflictF a (#addr)) || (a == #addr)))
                                #maddrs #msts);

          (* Conflict when a valid downlock exists ([cmmid]).
           * Find the last of the chain when conflict ([pmid]). *)
          LET cmmid <- (miterMAS MaybeNone
                                 (fun i m => MaybeSome $i)
                                 (fun m a st => (st == mshrValid) &&
                                                (!(m!MSHR@."m_is_ul")) &&
                                                a == #addr)
                                 #mshrs #maddrs #msts);
          LET conflict <- #cmmid!(MaybeStr MshrId)@."valid";
          LET ret: GetSlotK <- STRUCT { "s_has_slot" ::= #hasSlot && !#stall;
                                        "s_conflict" ::= #conflict;
                                        "s_id" ::= #mid };

          If (#hasSlot && !#stall)
          then (Write "mshrs"+o <-
                #mshrs#[#mid <- STRUCT { "m_is_ul" ::= $$Default;
                                         "m_qidx" ::= #pmshr!PreMSHR@."r_msg_from";
                                         "m_rsb" ::= $$Default;
                                         "m_dl_rss_from" ::= $$Default;
                                         "m_dl_rss_recv" ::= $$Default }];
               Write "maddrs"+o <- #maddrs#[#mid <- #pmshr!PreMSHR@."r_msg"!KMsg@."addr"];
               Write "msts"+o <- #msts#[#mid <- (IF #conflict then mshrWaiting else mshrOwned)];
               Read rqs: Array (Struct KMsg) numSlots <- "rqs"+o;
               Write "rqs"+o <- #rqs#[#mid <- #pmshr!PreMSHR@."r_msg"];

               If (#conflict)
               then (LET pmid: MshrId <-
                               (miterASN $$Default
                                         (fun i m => $i)
                                         (fun a st nx =>
                                            (st != mshrInvalid) &&
                                            (!(nx!(MaybeStr MshrId)@."valid")) &&
                                            a == #addr)
                                         #maddrs #msts #mnexts);
                    LET pnext <- #mnexts#[#pmid];
                    Write "mnexts"+o <- #mnexts#[#pmid <- (MaybeSome #mid)];
                    Retv);
               Retv);
          Ret #ret

        with Method ("getCRqSlot"+o)(pmshr: PreMSHRK): GetSlotK :=
          Read mshrs <- "mshrs"+o;
          Read maddrs <- "maddrs"+o;
          Read msts <- "msts"+o;
          Read mnexts <- "mnexts"+o;
          LET mmid <- (cmiterMS MaybeNone
                               (fun n _ => MaybeSome $n)
                               (fun m st => st == mshrInvalid)
                               #mshrs #msts);
          LET hasSlot <- #mmid!(MaybeStr MshrId)@."valid";
          LET mid <- #mmid!(MaybeStr MshrId)@."data";
          LET addr <- #pmshr!PreMSHR@."r_msg"!KMsg@."addr";

          (* Should stall when an index-equivalent line is in the pipeline *)
          LET stall <- (miterAS $$false
                                (fun _ _ => $$true)
                                (fun a st =>
                                   ((st == mshrOwned) || (st == mshrReleasing)) &&
                                   conflictF a (#addr))
                                #maddrs #msts);

          LET cmmidUL <- (cmiterMASN MaybeNone
                                     (fun i m => MaybeSome $i)
                                     (fun m a st nx =>
                                        (st != mshrInvalid) &&
                                        (!(nx!(MaybeStr MshrId)@."valid")) &&
                                        (m!MSHR@."m_is_ul") && a == #addr)
                                     #mshrs #maddrs #msts #mnexts);
          LET cmmidDL <- (miterMASN MaybeNone
                                    (fun i m => MaybeSome $i)
                                    (fun m a st nx =>
                                       (st != mshrInvalid) &&
                                       (!(nx!(MaybeStr MshrId)@."valid")) &&
                                       (!(m!MSHR@."m_is_ul")) &&
                                       a == #addr)
                                    #mshrs #maddrs #msts #mnexts);
          LET conflictUL <- #cmmidUL!(MaybeStr MshrId)@."valid";
          LET conflictDL <- #cmmidDL!(MaybeStr MshrId)@."valid";
          LET conflict <- #conflictUL || #conflictDL;
          LET ret: GetSlotK <- STRUCT { "s_has_slot" ::= #hasSlot && !#stall;
                                        "s_conflict" ::= #conflict;
                                        "s_id" ::= #mid };

          If (#hasSlot && !#stall)
          then (Write "mshrs"+o <-
                #mshrs#[#mid <- STRUCT { "m_is_ul" ::= $$Default;
                                         "m_qidx" ::= #pmshr!PreMSHR@."r_msg_from";
                                         "m_rsb" ::= $$Default;
                                         "m_dl_rss_from" ::= $$Default;
                                         "m_dl_rss_recv" ::= $$Default }];
               Write "maddrs"+o <- #maddrs#[#mid <- #pmshr!PreMSHR@."r_msg"!KMsg@."addr"];
               Write "msts"+o <- #msts#[#mid <- (IF #conflict then mshrWaiting else mshrOwned)];
               Read rqs: Array (Struct KMsg) numSlots <- "rqs"+o;
               Write "rqs"+o <- #rqs#[#mid <- #pmshr!PreMSHR@."r_msg"];
               If (#conflict)
               then (LET pmid <- (IF #conflictUL
                                  then #cmmidUL!(MaybeStr MshrId)@."data"
                                  else #cmmidDL!(MaybeStr MshrId)@."data");
                    LET pnext <- #mnexts#[#pmid];
                    Write "mnexts"+o <- #mnexts#[#pmid <- (MaybeSome #mid)];
                    Retv);
               Retv);
          Ret #ret

        with Method ("getWait"+o)(): PreMSHRK :=
          Read mshrs <- "mshrs"+o;
          Read maddrs <- "maddrs"+o;
          Read msts <- "msts"+o;
          Read rqs: Array (Struct KMsg) numSlots <- "rqs"+o;

          LET mwait <- (miterMS MaybeNone
                               (fun i _ => MaybeSome $i)
                               (fun m st => st == mshrFirstWait)
                               #mshrs #msts);
          Assert (#mwait!(MaybeStr MshrId)@."valid");
          LET mid <- #mwait!(MaybeStr MshrId)@."data";
          LET mshr <- #mshrs#[#mid];
          LET addr <- #maddrs#[#mid];
          LET rq <- #rqs#[#mid];

          (* Still must wait when either
           * 1) a same-address line is in progress or
           * 2) an index-equivalent line is in the pipeline. *)
          LET stall <- (miterAS $$false
                                (fun _ _ => $$true)
                                (fun a st =>
                                   ((st >= mshrOwned) && (a == #addr)) ||
                                   (((st == mshrOwned) || st == mshrReleasing) &&
                                    (conflictF a (#addr))))
                                #maddrs #msts);
          Assert !#stall;

          Write "msts"+o <- #msts#[#mid <- mshrOwned];
          LET pre: PreMSHRK <- STRUCT { "r_id" ::= #mid;
                                        "r_msg" ::= #rq;
                                        "r_msg_from" ::= #mshr!MSHR@."m_qidx" };
          Ret #pre

        with Method ("registerUL"+o)(ul: RegULK): Void :=
          Read mshrs: Array (Struct MSHR) numSlots <- "mshrs"+o;
          Read msts: Array MSHRStatus numSlots <- "msts"+o;
          LET mid <- #ul!RegUL@."r_id";
          Write "mshrs"+o <-
          #mshrs#[#mid <- STRUCT { "m_is_ul" ::= $$true;
                                   (* Concatenating [$downIdx] is very important here;
                                    * when it turns into a downlock (by [transferUpDown])
                                    * it should have a precise [KQIdx] value. *)
                                   "m_qidx" ::= {$downIdx, (#ul!RegUL@."r_ul_rsbTo")};
                                   "m_rsb" ::= #ul!RegUL@."r_ul_rsb";
                                   "m_dl_rss_from" ::= $$Default;
                                   "m_dl_rss_recv" ::= $$Default }];
          Write "msts"+o <- #msts#[#mid <- mshrValid];
          Retv
        with Method ("registerDL"+o)(dl: RegDLK): Void :=
          Read mshrs: Array (Struct MSHR) numSlots <- "mshrs"+o;
          Read msts: Array MSHRStatus numSlots <- "msts"+o;
          LET mid <- #dl!RegDL@."r_id";
          Write "mshrs"+o <-
          #mshrs#[#mid <- STRUCT { "m_is_ul" ::= $$false;
                                   "m_qidx" ::= #dl!RegDL@."r_dl_rsbTo";
                                   "m_rsb" ::= #dl!RegDL@."r_dl_rsb";
                                   "m_dl_rss_from" ::= #dl!RegDL@."r_dl_rss_from";
                                   "m_dl_rss_recv" ::= $$Default }];
          Write "msts"+o <- #msts#[#mid <- mshrValid];
          Retv

        with Method ("canImm"+o)(addr: KAddr): Void :=
          Read maddrs <- "maddrs"+o;
          Read msts <- "msts"+o;
          Read mnexts <- "mnexts"+o;
          LET mmid <- (cmiterS MaybeNone
                               (fun n _ => MaybeSome $n)
                               (fun st => st == mshrInvalid)
                               #msts);
          Assert (#mmid!(MaybeStr MshrId)@."valid"); (* Has a slot *)
          LET cmmid <- (miterASN MaybeNone
                                 (fun i m => MaybeSome $i)
                                 (fun a st nx =>
                                    (st != mshrInvalid) &&
                                    (!(nx!(MaybeStr MshrId)@."valid")) &&
                                    a == #addr)
                                 #maddrs #msts #mnexts);
          Assert !(#cmmid!(MaybeStr MshrId)@."valid"); (* No conflicts with the other MSHRs *)
          Retv

        with Method ("setULImm"+o)(msg: Struct KMsg): Void :=
          Read mshrs <- "mshrs"+o;
          Read maddrs <- "maddrs"+o;
          Read msts <- "msts"+o;
          Read rqs: Array (Struct KMsg) numSlots <- "rqs"+o;
          LET mmid <- (cmiterMS MaybeNone
                               (fun n _ => MaybeSome $n)
                               (fun m st => st == mshrInvalid)
                               #mshrs #msts);
          Assert (#mmid!(MaybeStr MshrId)@."valid"); (* Has a slot *)
          LET mid <- #mmid!(MaybeStr MshrId)@."data";
          LET addr <- #msg!KMsg@."addr";
          LET cmmid <- (miterAS MaybeNone
                                (fun i m => MaybeSome $i)
                                (fun a st => (st != mshrInvalid) && a == #addr)
                                #maddrs #msts);
          Assert !(#cmmid!(MaybeStr MshrId)@."valid"); (* No conflicts with the other MSHRs *)
          Write "mshrs"+o <- #mshrs#[#mid <- STRUCT { "m_is_ul" ::= $$true;
                                                      "m_qidx" ::= $$Default;
                                                      "m_rsb" ::= $$false;
                                                      "m_dl_rss_from" ::= $$Default;
                                                      "m_dl_rss_recv" ::= $$Default }];
          Write "maddrs"+o <- #maddrs#[#mid <- #msg!KMsg@."addr"];
          Write "msts"+o <- #msts#[#mid <- mshrValid];
          Write "rqs"+o <- #rqs#[#mid <- #msg];
          Retv

        with Method ("transferUpDown"+o)(trsf: TrsfUpDownK): Void :=
          (* [transferUpDown] requires that the line is free of downlocks;
           * it is checked by [getULReady] early in the pipeline. *)
          Read mshrs: Array (Struct MSHR) numSlots <- "mshrs"+o;
          Read msts: Array MSHRStatus numSlots <- "msts"+o;
          LET mid <- #trsf!TrsfUpDown@."r_id";
          LET pmshr <- #mshrs#[#mid];
          Write "mshrs"+o <-
          #mshrs#[#mid <- STRUCT { "m_is_ul" ::= $$false;
                                   "m_qidx" ::= #pmshr!MSHR@."m_qidx";
                                   "m_rsb" ::= #pmshr!MSHR@."m_rsb";
                                   "m_dl_rss_from" ::= #trsf!TrsfUpDown@."r_dl_rss_from";
                                   "m_dl_rss_recv" ::= $$Default }];
          Write "msts"+o <- #msts#[#mid <- mshrValid];
          Retv

        with Method ("addRs"+o)(a: Struct AddRs): Void :=
          Read mshrs <- "mshrs"+o;
          Read maddrs <- "maddrs"+o;
          Read msts <- "msts"+o;
          LET addr <- #a!AddRs@."r_msg"!KMsg@."addr";
          LET mmid <- (miterMAS MaybeNone
                                (fun n _ => MaybeSome $n)
                                (fun m a st =>
                                   (st == mshrValid) && (!(m!MSHR@."m_is_ul")) && a == #addr)
                                #mshrs #maddrs #msts);
          Assert (#mmid!(MaybeStr MshrId)@."valid");
          LET mid <- #mmid!(MaybeStr MshrId)@."data";

          LET pmshr <- #mshrs#[#mid];
          Write "mshrs"+o <-
          #mshrs#[#mid <- STRUCT { "m_is_ul" ::= #pmshr!MSHR@."m_is_ul";
                                   "m_qidx" ::= #pmshr!MSHR@."m_qidx";
                                   "m_rsb" ::= #pmshr!MSHR@."m_rsb";
                                   "m_dl_rss_from" ::= #pmshr!MSHR@."m_dl_rss_from";
                                   "m_dl_rss_recv" ::=
                                     bvSet (#pmshr!MSHR@."m_dl_rss_recv")
                                           (#a!AddRs@."r_midx") }];
          Read rss: Array (Struct MSHRRs) numSlots <- "rss"+o;
          LET prs <- #rss#[#mid];
          (* It is safe to overwrite the response;
           * see the comment in the [MSHRRs] definition. *)
          Write "rss"+o <- #rss#[#mid <- #a!AddRs@."r_msg"];
          Retv

        with Method ("getULReady"+o)(addr: KAddr): MshrId :=
          Read mshrs <- "mshrs"+o;
          Read maddrs <- "maddrs"+o;
          Read msts <- "msts"+o;

          (* Should stall if either
           * 1) an index-equivalent line is in the pipeline or
           * 2) there is a downlock with the same address. *)
          LET stall <- (miterMAS $$false
                                 (fun _ _ => $$true)
                                 (fun m a st =>
                                    (((st == mshrOwned) || st == mshrReleasing) &&
                                     conflictF a (#addr)) ||
                                    ((st >= mshrOwned) && (!(m!MSHR@."m_is_ul")) &&
                                     a == #addr))
                                 #mshrs #maddrs #msts);
          Assert !#stall;

          (* [cmiter] is used below, since PRq cannot make any uplocks. *)
          LET mmidUL <- (cmiterMAS MaybeNone
                                   (fun n _ => MaybeSome $n)
                                   (fun m a st =>
                                      (st == mshrValid) && m!MSHR@."m_is_ul" && a == #addr)
                                   #mshrs #maddrs #msts);
          Assert (#mmidUL!(MaybeStr MshrId)@."valid");
          LET mid <- #mmidUL!(MaybeStr MshrId)@."data";
          Ret #mid

        with Method ("getDLReady"+o)(): DLReadyK :=
          Read mshrs <- "mshrs"+o;
          Read maddrs <- "maddrs"+o;
          Read msts: Array MSHRStatus numSlots <- "msts"+o;
          LET mmid <- (miterMS MaybeNone
                              (fun n _ => MaybeSome $n)
                              (fun m st =>
                                 (st == mshrValid) &&
                                 (!(m!MSHR@."m_is_ul")) &&
                                 m!MSHR@."m_dl_rss_from" == m!MSHR@."m_dl_rss_recv")
                              #mshrs #msts);
          Assert (#mmid!(MaybeStr MshrId)@."valid");
          LET mid <- #mmid!(MaybeStr MshrId)@."data";
          LET addr <- #maddrs#[#mid];

          (* Should stall when an index-equivalent line is in the pipeline *)
          LET stall <- (miterAS $$false
                                (fun _ _ => $$true)
                                (fun a st =>
                                   ((st == mshrOwned) || st == mshrReleasing) &&
                                   conflictF a (#addr))
                                #maddrs #msts);
          Assert !#stall;

          LET ret: DLReadyK <- STRUCT { "r_id" ::= #mid; "r_addr" ::= #addr };
          Ret #ret

        with Method ("startRelease"+o)(mid: MshrId): Void :=
          Read msts: Array MSHRStatus numSlots <- "msts"+o;
          Write "msts"+o <- #msts#[#mid <- mshrReleasing];
          Retv

        with Method ("releaseMSHR"+o)(mid: MshrId): Void :=
          Read mshrs: Array (Struct MSHR) numSlots <- "mshrs"+o;
          Read msts: Array MSHRStatus numSlots <- "msts"+o;
          Read mnexts: Array MSHRNext numSlots <- "mnexts"+o;
          Write "mshrs"+o <- #mshrs#[#mid <- $$Default];
          Write "mnexts"+o <- #mnexts#[#mid <- $$Default];

          LET msts1 <- #msts#[#mid <- $$Default];
          LET next <- #mnexts#[#mid];
          If (#next!(MaybeStr MshrId)@."valid")
          then (LET cmid <- #next!(MaybeStr MshrId)@."data";
               LET msts2 <- #msts1#[#cmid <- mshrFirstWait];
               Ret #msts2)
          else (Ret #msts1) as nmsts;
          Write "msts"+o <- #nmsts;
          Retv }.

End MSHR.

Section Victims.
  Variables (oidx: IdxT)
            (addrSz predNumVictims: nat)
            (infoK valueK: Kind)
            (mshrSlotSz: nat).

  Local Notation "s '+o'" := (s ++ "__" ++ idx_to_string oidx)%string (at level 60).
  Local Notation "s1 _++ s2" := (s1 ++ "__" ++ s2)%string (at level 60).

  Let MshrId := Bit mshrSlotSz.

  Let numVictims := S predNumVictims.
  Let victimIdxSz := S (Nat.log2 predNumVictims).
  Let MviK := Maybe (Bit victimIdxSz).

  Definition Victim :=
    STRUCT { "victim_valid" :: Bool;
             "victim_addr" :: Bit addrSz;
             "victim_info" :: infoK;
             "victim_value" :: valueK;
             "victim_req" :: Bool }.
  Let VictimK := Struct Victim.

  Definition victimsN: string := "victims"+o.

  Definition findVictimN: string := victimsN _++ "findVictim".
  Definition findVictim := MethodSig findVictimN (Bit addrSz): MviK.

  Definition getVictimN: string := victimsN _++ "getVictim".
  Definition getVictim := MethodSig getVictimN (Bit victimIdxSz): VictimK.

  Definition SetVictim :=
    STRUCT { "victim_idx" :: Bit victimIdxSz;
             "victim_info" :: infoK;
             "victim_value" :: valueK }.
  Let SetVictimK := Struct SetVictim.
  Definition setVictimN: string := victimsN _++ "setVictim".
  Definition setVictim := MethodSig setVictimN (SetVictimK): Void.

  Definition registerVictimN: string := victimsN _++ "registerVictim".
  Definition registerVictim := MethodSig registerVictimN (VictimK): Void.

  Definition getFirstVictimN: string := victimsN _++ "getFirstVictim".
  Definition getFirstVictim := MethodSig getFirstVictimN (): VictimK.

  Definition hasVictimN: string := victimsN _++ "hasVictim".
  Definition hasVictim := MethodSig hasVictimN (): Bool.

  Definition setVictimRqN: string := victimsN _++ "setVictimRq".
  Definition setVictimRq := MethodSig setVictimRqN (Bit addrSz): Void.

  Definition releaseVictimN: string := victimsN _++ "releaseVictim".
  Definition releaseVictim := MethodSig releaseVictimN (Bit addrSz): Void.

  (** Registers *)
  Definition victimRegsN: string := "victimRegs"+o.

  (** Victim lines *)
  Local Notation "$v$ n" :=
    (Const _ (natToWord victimIdxSz n)) (at level 5): kami_expr_scope.

  Fixpoint victimIterAFix (var: Kind -> Type)
           (victims: Expr var (SyntaxKind (Array VictimK numVictims)))
           (addr: Expr var (SyntaxKind (Bit addrSz)))
           {retK} (readF: nat -> Expr var (SyntaxKind VictimK) -> ActionT var retK)
           (cont: ActionT var retK) (n: nat): ActionT var retK :=
    match n with
    | O => cont
    | S n' =>
      (LET victim: VictimK <- victims#[$v$(numVictims - n)];
      If ((#victim!Victim@."victim_valid")
          && #victim!Victim@."victim_addr" == addr)
       then (readF (numVictims - n) (#victim)%kami_expr)
       else (victimIterAFix victims addr readF cont n')
        as ret;
      Ret #ret)%kami_action
    end.

  Definition victimIterA (var: Kind -> Type)
             (victims: Expr var (SyntaxKind (Array VictimK numVictims)))
             (addr: Expr var (SyntaxKind (Bit addrSz)))
             {retK} (readF: nat -> Expr var (SyntaxKind VictimK) -> ActionT var retK)
             (cont: ActionT var retK): ActionT var retK :=
    victimIterAFix victims addr readF cont numVictims.

  Fixpoint getVictimSlotFix (var: Kind -> Type)
           (victims: Expr var (SyntaxKind (Array VictimK numVictims)))
           (n: nat): Expr var (SyntaxKind (Maybe (Bit victimIdxSz))) :=
    (match n with
     | O => MaybeNone
     | S n' =>
       (IF (victims#[$v$n']!Victim@."victim_valid")
        then getVictimSlotFix victims n'
        else MaybeSome $n')
     end)%kami_expr.

  Definition getVictimSlot (var: Kind -> Type)
             (victims: Expr var (SyntaxKind (Array VictimK numVictims)))
    : Expr var (SyntaxKind (Maybe (Bit victimIdxSz))) :=
    getVictimSlotFix victims numVictims.

  Fixpoint getFirstVictimFix (var: Kind -> Type)
           (victims: Expr var (SyntaxKind (Array VictimK numVictims)))
           (n: nat): Expr var (SyntaxKind (Maybe VictimK)) :=
    (match n with
     | O => MaybeNone
     | S n' =>
       (IF ((victims#[$v$n']!Victim@."victim_valid") &&
            (!(victims#[$v$n']!Victim@."victim_req")))
        then MaybeSome (victims#[$v$n'])
        else getFirstVictimFix victims n')
     end)%kami_expr.

  Definition getFirstVictimF (var: Kind -> Type)
             (victims: Expr var (SyntaxKind (Array VictimK numVictims)))
    : Expr var (SyntaxKind (Maybe VictimK)) :=
    getFirstVictimFix victims numVictims.

  Fixpoint hasVictimFix (var: Kind -> Type)
           (victims: Expr var (SyntaxKind (Array VictimK numVictims)))
           (n: nat): Expr var (SyntaxKind Bool) :=
    (match n with
     | O => $$false
     | S n' =>
       (IF ((victims#[$v$n']!Victim@."victim_valid") &&
            (!(victims#[$v$n']!Victim@."victim_req")))
        then $$true
        else hasVictimFix victims n')
     end)%kami_expr.

  Definition hasVictimF (var: Kind -> Type)
             (victims: Expr var (SyntaxKind (Array VictimK numVictims)))
    : Expr var (SyntaxKind Bool) :=
    hasVictimFix victims numVictims.

  Fixpoint setVictimRqFix (var: Kind -> Type)
           (addr: Expr var (SyntaxKind (Bit addrSz)))
           (victims: Expr var (SyntaxKind (Array VictimK numVictims)))
           (cont: ActionT var Void)
           (n: nat): ActionT var Void :=
    (match n with
     | O => cont
     | S n' =>
       (LET victim <- victims#[$v$n'];
       If ((#victim!Victim@."victim_valid") &&
           (#victim!Victim@."victim_addr" == addr))
        then (LET nvictim: VictimK <- STRUCT { "victim_valid" ::= #victim!Victim@."victim_valid";
                                               "victim_addr" ::= #victim!Victim@."victim_addr";
                                               "victim_info" ::= #victim!Victim@."victim_info";
                                               "victim_value" ::= #victim!Victim@."victim_value";
                                               "victim_req" ::= $$true };
             Write victimRegsN <- victims#[$v$n' <- #nvictim];
             Retv)
        else (setVictimRqFix addr victims cont n'); Retv)
     end)%kami_action.

  Definition setVictimRqF (var: Kind -> Type)
             (addr: Expr var (SyntaxKind (Bit addrSz)))
             (victims: Expr var (SyntaxKind (Array VictimK numVictims)))
             (cont: ActionT var Void): ActionT var Void :=
    setVictimRqFix addr victims cont numVictims.

  Definition victimsIfc :=
    MODULE {
      Register victimRegsN: Array VictimK numVictims <- Default

      with Method findVictimN (addr: Bit addrSz): MviK :=
        Read victims <- victimRegsN;
        victimIterA
          (#victims)%kami_expr (#addr)%kami_expr
          (fun i _ => Ret (MaybeSome ($i)))
          (Ret MaybeNone)

      with Method getVictimN (vidx: Bit victimIdxSz): VictimK :=
        Read victims: Array VictimK numVictims <- victimRegsN;
        Ret #victims#[#vidx]

      with Method setVictimN (sv: SetVictimK): Void :=
        Read victims: Array VictimK numVictims <- victimRegsN;
        LET pvictim <- #victims#[#sv!SetVictim@."victim_idx"];
        LET nvictim <- STRUCT { "victim_valid" ::= $$true;
                                "victim_addr" ::= #pvictim!Victim@."victim_addr";
                                "victim_info" ::= #sv!SetVictim@."victim_info";
                                "victim_value" ::= #sv!SetVictim@."victim_value";
                                "victim_req" ::= #pvictim!Victim@."victim_req" };
        Write victimRegsN <- #victims#[#sv!SetVictim@."victim_idx" <- #nvictim];
        Retv

      with Method registerVictimN (v: VictimK): Void :=
        Read victims <- victimRegsN;
        LET mvi <- getVictimSlot #victims;
        Assert (#mvi!(MaybeStr (Bit victimIdxSz))@."valid");
        LET vi <- #mvi!(MaybeStr (Bit victimIdxSz))@."data";
        Write victimRegsN <- #victims#[#vi <- #v];
        Retv

      with Method getFirstVictimN (): VictimK :=
        Read victims <- victimRegsN;
        LET mvictim <- getFirstVictimF #victims;
        Assert (#mvictim!(MaybeStr VictimK)@."valid");
        Ret #mvictim!(MaybeStr VictimK)@."data"

      with Method hasVictimN (): Bool :=
        Read victims <- victimRegsN;
        LET hv <- hasVictimF #victims;
        Ret #hv

      with Method setVictimRqN (addr: Bit addrSz): Void :=
        Read victims <- victimRegsN;
        setVictimRqF (#addr)%kami_expr (#victims)%kami_expr Retv

      with Method releaseVictimN (addr: Bit addrSz): Void :=
        Read victims <- victimRegsN;
        victimIterA
          (#victims)%kami_expr (#addr)%kami_expr
          (fun i victim => (Write victimRegsN <- #victims#[$v$i <- $$Default];
                           Retv))
          Retv
    }.

End Victims.

Section Cache.
  Variables (oidx: IdxT)
            (* Common *)
            (infoK: Kind)
            (edirK: Kind)
            (valueK: Kind)
            (* D$ + info cache + "Traditional" directory *)
            (tagSz indexSz offsetSz addrSz lgWay: nat)
            (* "Extended" directory *)
            (edirLgWay: nat).

  Local Notation "s '+o'" := (s ++ "__" ++ idx_to_string oidx)%string (at level 60).
  Local Notation "s1 _++ s2" := (s1 ++ "__" ++ s2)%string (at level 60).

  (*! Private cache interfaces *)

  Definition TagValue (valueK: Kind) :=
    STRUCT { "tag" :: Bit tagSz; "value" :: valueK }.

  (** Information cache *)

  Let TagInfo := TagValue infoK.
  Let TagInfoK := Struct TagInfo.

  Definition infoRamN (way: nat): string := "infoRam"+o _++ nat_to_string way.

  Variable (infoInitVal: ConstT infoK).
  Definition infoRam (way: nat) :=
    bram2 (dType:= TagInfoK) (infoRamN way) indexSz
          (* (CSTRUCT { "tag" ::= ConstBit $way; *)
          (CSTRUCT { "tag" ::= ConstBit $(way + Nat.pow 2 lgWay);
                     "value" ::= infoInitVal })%init.
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
  Variable (edirInitVal: ConstT edirK).
  (** NOTE: initial tags of the extended directory should be disjoint to the ones
   * in the conventional directory. In order for it [Nat.pow 2 lgWay] is added to
   * each way.
   *)
  Definition edirRam (way: nat) :=
    bram2 (dType:= TagEDirK) (edirRamN way) indexSz
          (* (CSTRUCT { "tag" ::= ConstBit $(way + Nat.pow 2 lgWay); *)
          (CSTRUCT { "tag" ::= ConstBit $(way + Nat.pow 2 (S lgWay));
                     "value" ::= edirInitVal })%init.
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
  Definition dataRam :=
    bram2 dataRamN dataIndexSz (getDefaultConst valueK).
  Definition dataRdReq := MethodSig (dataRamN -- "rdReq") (Bit dataIndexSz): Void.
  Definition dataRdResp := MethodSig (dataRamN -- "rdResp") (): valueK.
  Definition dataWrReq :=
    MethodSig (dataRamN -- "wrReq") (Struct (BramWriteReq dataIndexSz valueK)): Void.

  (** Replacement cache *)

  Definition repCntSz := 8.
  Definition RepCntK := Bit repCntSz.
  Definition repRamN := "repRam"+o.
  Let repK := Vector RepCntK lgWay.
  Let repInit: ConstT repK := ConstVector (replicate (ConstBit $1) _).
  Definition repRam := bram2 repRamN indexSz repInit.
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
        else (LET nreps <- #ireps@[#acc!AccessRec@."acc_way" <- $0];
             Ret #nreps)
        as nreps;
        LET app <- STRUCT { "addr" ::= #acc!AccessRec@."acc_index";
                            "datain" ::= #nreps };
        Call repWrReq(#app);
        Retv
    }.

  Definition rep := (repLRU ++ repRam)%kami.

  (*! Public interface for the info/value caches *)

  Definition MayVictim :=
    STRUCT { "mv_addr" :: Bit addrSz;
             "mv_info" :: infoK }.
  Let MayVictimK := Struct MayVictim.

  Definition InfoRead :=
    STRUCT { "info_index" :: Bit indexSz;
             "info_hit" :: Bool;
             "info_way" :: Bit lgWay; (* a replaceable way, if miss *)
             "edir_hit" :: Bool;
             "edir_way" :: Bit edirLgWay;
             "edir_slot" :: Maybe (Bit edirLgWay);
             "info" :: infoK;
             "may_victim" :: MayVictimK;
             "reps" :: repK
           }.
  Let InfoReadK := Struct InfoRead.

  Definition cacheN: string := "cache"+o.

  (** Stage 1: request to read information *)
  Definition infoRqN: string := cacheN _++ "infoRq".
  Definition infoRq := MethodSig infoRqN (Bit addrSz): Void.

  (** Stage 2: get the information response and request to read the value *)
  Definition infoRsValueRqN: string := cacheN _++ "infoRsValueRq".
  Definition infoRsValueRq := MethodSig infoRsValueRqN (Bit addrSz): InfoReadK.

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
             "value" :: valueK;
             "may_victim" :: MayVictimK;
             "reps" :: repK
           }.
  Let LineWriteK := Struct LineWrite.

  (* NOTE: this design implies that there is no case of read-and-modify for values. *)
  Definition valueRsLineRqN: string := cacheN _++ "valueRsLineRq".
  Definition valueRsLineRq := MethodSig valueRsLineRqN (LineWriteK): valueK.

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
            (edirFromInfo: forall ty, fullType ty (SyntaxKind infoK) -> Expr ty (SyntaxKind edirK))
            (isJustDir: forall ty, fullType ty (SyntaxKind infoK) -> Expr ty (SyntaxKind Bool))
            (isDirInvalid: forall ty, fullType ty (SyntaxKind infoK) -> Expr ty (SyntaxKind Bool))
            (edirEmptySlot: forall ty, Expr ty (SyntaxKind edirK) -> Expr ty (SyntaxKind Bool)).

  Arguments getIndex {_}.
  Arguments getTag {_}.
  Arguments buildAddr {_}.
  Arguments edirToInfo {_}.
  Arguments edirFromInfo {_}.
  Arguments isJustDir {_}.
  Arguments isDirInvalid {_}.
  Arguments edirEmptySlot {_}.

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

  Variable (mshrSlotSz: nat).
  Local Notation registerVictim := (registerVictim oidx addrSz infoK valueK).

  Definition cacheIfc :=
    MODULE {
      Method infoRqN (addr: Bit addrSz): Void :=
        LET index <- getIndex addr;
        NCall makeInfoRdReqs index;
        Call repGetRq(#index);
        Retv

      with Method infoRsValueRqN (addr: Bit addrSz): InfoReadK :=
        LET tag <- getTag addr;
        LET index <- getIndex addr;
        LET tis: Vector TagInfoK lgWay <- $$Default;
        NCall ntis <- makeInfoRdResps tis;
        LET itm <- doTagMatch _ tag ntis (Nat.pow 2 lgWay);

        Call reps <- repGetRs();
        LET maxWay: Bit lgWay <- $$Default;
        LET maxAge: RepCntK <- $$Default;
        NCall2 repWay, repAge <- getRepWay maxWay maxAge reps;
        Assert (#repAge != $0);

        LET repTagInfo <- #ntis@[#repWay];
        LET repTag <- #repTagInfo!(TagValue infoK)@."tag";
        LET repInfo <- #repTagInfo!(TagValue infoK)@."value";

        (** On cache hit, the way is determined; otherwise, it is the one from the victim. *)
        LET nway <- (IF (#itm!(TagMatch infoK lgWay)@."tm_hit")
                     then (#itm!(TagMatch infoK lgWay)@."tm_way")
                     else #repWay);

        LET linfo: InfoReadK <-
                   STRUCT { "info_index" ::= #index;
                            "info_hit" ::= #itm!(TagMatch infoK lgWay)@."tm_hit";
                            "info_way" ::= #nway;
                            "edir_hit" ::= $$Default;
                            "edir_way" ::= $$Default;
                            "edir_slot" ::= $$Default;
                            "info" ::= #itm!(TagMatch infoK lgWay)@."tm_value";
                            "may_victim" ::=
                              STRUCT { "mv_addr" ::= buildAddr repTag index;
                                       "mv_info" ::= #repInfo };
                            "reps" ::= #reps };
        Call dataRdReq({#nway, #index});
        Ret #linfo

      with Method valueRsLineRqN (lw: LineWriteK): valueK :=
        Call value <- dataRdResp();
        LET addr <- #lw!LineWrite@."addr";
        LET index <- getIndex addr;
        LET info_way <- #lw!LineWrite@."info_way";
        LET ninfo <- #lw!LineWrite@."info";

        If (#lw!LineWrite@."info_write")
        then (LET irq <- STRUCT { "addr" ::= #index;
                                  "datain" ::=
                                    STRUCT { "tag" ::= getTag addr;
                                             "value" ::= #ninfo } };
             NCall makeInfoWrReqs info_way irq;

             (** Should register a new victim line if not hit *)
             If (!(#lw!LineWrite@."info_hit"))
              then (LET mv <- #lw!LineWrite@."may_victim";
                   LET nv <- STRUCT { "victim_valid" ::= $$true;
                                      "victim_addr" ::= #mv!MayVictim@."mv_addr";
                                      "victim_info" ::= #mv!MayVictim@."mv_info";
                                      "victim_value" ::= #value;
                                      "victim_req" ::= $$false };
                   Call registerVictim(#nv);
                   Retv);

              (** Update replacement information *)
              Call repAccess(STRUCT { "acc_type" ::=
                                        (IF (isDirInvalid ninfo)
                                         then accTouch else accInvalid);
                                      "acc_reps" ::= #lw!LineWrite@."reps";
                                      "acc_index" ::= #index;
                                      "acc_way" ::= #info_way });
              Retv);

        (** Update the value if necessary *)
        If (#lw!LineWrite@."value_write")
        then (LET drq <- STRUCT { "addr" ::= {#info_way, getIndex addr};
                                  "datain" ::= #lw!LineWrite@."value" };
             Call dataWrReq(#drq); Retv);
        Ret #value
    }.

  Definition ncidIfc :=
    MODULE {
      Method infoRqN (addr: Bit addrSz): Void :=
        LET index <- getIndex addr;
        NCall makeInfoRdReqs index;
        NCall makeEDirRdReqs index;
        Call repGetRq(#index);
        Retv

      with Method infoRsValueRqN (addr: Bit addrSz): InfoReadK :=
        LET tag <- getTag addr;
        LET index <- getIndex addr;
        LET tis: Vector TagInfoK lgWay <- $$Default;
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
        NCall2 repWay, repAge <- getRepWay maxWay maxAge reps;
        Assert (#repAge != $0);

        LET repTagInfo <- #ntis@[#repWay];
        LET repTag <- #repTagInfo!(TagValue infoK)@."tag";
        LET repInfo <- #repTagInfo!(TagValue infoK)@."value";

        (** On cache hit, the way is determined; otherwise, it is the one from the victim. *)
        LET nway <- (IF (#itm!(TagMatch infoK lgWay)@."tm_hit")
                     then (#itm!(TagMatch infoK lgWay)@."tm_way")
                     else #repWay);
        LET linfo: InfoReadK <-
                   STRUCT { "info_index" ::= #index;
                            "info_hit" ::= #itm!(TagMatch infoK lgWay)@."tm_hit";
                            "info_way" ::= #nway;
                            "edir_hit" ::= #etm!(TagMatch edirK edirLgWay)@."tm_hit";
                            "edir_way" ::= #etm!(TagMatch edirK edirLgWay)@."tm_way";
                            "edir_slot" ::= #ees;
                            "info" ::=
                              (IF (#itm!(TagMatch infoK lgWay)@."tm_hit")
                               then (#itm!(TagMatch infoK lgWay)@."tm_value")
                               else (edirToInfo edirV));
                            "may_victim" ::=
                              STRUCT { "mv_addr" ::= buildAddr repTag index;
                                       "mv_info" ::= #repInfo };
                            "reps" ::= #reps };

        (** On cache hit, request the line value; otherwise, request the victim line value. *)
        Call dataRdReq({#nway, #index});
        Ret #linfo

      (** Cache-write cases:
       * 1) info-hit and info-write: trivial. Write to the appropriate info line.
       * 2) info-miss and edir-hit
       * 2-1) info write (!justDir): write to info (the victim line is already fetched)
       *      and invalidate the edir line.
       * 2-2) edir write (justDir): write to edir (this case may never happen).
       * 3) info miss and edir miss
       * 3-1) info write: write to info
       * 3-2) edir write: write to edir if there's an empty slot, otherwise to the info cache.
       *)
      with Method valueRsLineRqN (lw: LineWriteK): valueK :=
        Call value <- dataRdResp();
        LET addr <- #lw!LineWrite@."addr";
        LET index <- getIndex addr;
        LET info_way <- #lw!LineWrite@."info_way";
        LET ninfo <- #lw!LineWrite@."info";
        LET justDir <- isJustDir ninfo;
        LET mes <- #lw!LineWrite@."edir_slot";
        LET hasEDirSlot <- #mes!(MaybeStr (Bit edirLgWay))@."valid";
        LET edirSlot <- #mes!(MaybeStr (Bit edirLgWay))@."data";

        If (#lw!LineWrite@."info_write")
        then
          ((** 1) Cases (according to the above note) that directly write to the info cache *)
           If ((#lw!LineWrite@."info_hit") ||
               (!#justDir) ||
               ((!(#lw!LineWrite@."edir_hit")) && #justDir && !#hasEDirSlot))
           then (LET irq <- STRUCT { "addr" ::= #index;
                                     "datain" ::= STRUCT { "tag" ::= getTag addr;
                                                           "value" ::= #ninfo } };
                NCall makeInfoWrReqs info_way irq;

                (** Should register a new victim line if not hit *)
                If (!(#lw!LineWrite@."info_hit"))
                 then (LET mv <- #lw!LineWrite@."may_victim";
                      LET nv <- STRUCT { "victim_valid" ::= $$true;
                                         "victim_addr" ::= #mv!MayVictim@."mv_addr";
                                         "victim_info" ::= #mv!MayVictim@."mv_info";
                                         "victim_value" ::= #value;
                                         "victim_req" ::= $$false };
                      Call registerVictim(#nv);
                      Retv);

                 (** Update replacement information *)
                 Call repAccess(STRUCT { "acc_type" ::=
                                           (IF (isDirInvalid ninfo)
                                            then accTouch else accInvalid);
                                         "acc_reps" ::= #lw!LineWrite@."reps";
                                         "acc_index" ::= #index;
                                         "acc_way" ::= #info_way });
                 Retv);

           (** 2) Cases that write to the edir cache, either an update or an invalidation *)
           If ((!(#lw!LineWrite@."info_hit")) &&
               #justDir &&
               ((#lw!LineWrite@."edir_hit") || #hasEDirSlot))
           then (LET edir_way <- (IF (#lw!LineWrite@."edir_hit")
                                  then #lw!LineWrite@."edir_way" else #edirSlot);
                LET erq <- STRUCT { "addr" ::= getIndex addr;
                                    "datain" ::= STRUCT { "tag" ::= getTag addr;
                                                          "value" ::= edirFromInfo ninfo } };
                NCall makeEDirWrReqs edir_way erq;
                Retv)
           else (If (#lw!LineWrite@."edir_hit")
                 then (LET edir_way <- #lw!LineWrite@."edir_way";
                      LET erq <- STRUCT { "addr" ::= getIndex addr;
                                          "datain" ::= STRUCT { "tag" ::= getTag addr;
                                                                "value" ::= edirFromInfo ninfo } };
                      NCall makeEDirWrReqs edir_way erq;
                      Retv);
                 Retv);
           Retv);

        (** Update the value if necessary *)
        If (#lw!LineWrite@."value_write")
        then (LET drq <- STRUCT { "addr" ::= {#info_way, getIndex addr};
                                  "datain" ::= #lw!LineWrite@."value" };
             Call dataWrReq(#drq); Retv);
        Ret #value
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

  Variable predNumVictims: nat.
  Local Notation victimsIfc :=
    (victimsIfc oidx addrSz predNumVictims infoK valueK).

  Definition cache :=
    (cacheIfc
       ++ victimsIfc
       ++ infoRams (Nat.pow 2 lgWay - 1)
       ++ dataRam
       ++ rep)%kami.

  Definition ncid :=
    (ncidIfc
       ++ victimsIfc
       ++ infoRams (Nat.pow 2 lgWay - 1)
       ++ edirRams (Nat.pow 2 edirLgWay - 1)
       ++ dataRam
       ++ rep)%kami.

End Cache.
