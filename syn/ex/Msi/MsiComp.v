Require Import String List.
Import ListNotations.

Require Import Kami.Kami.
Require Import Hemiola.Index.
Require Import Compiler.HemiolaDeep Compiler.CompileK.
Require Import MsiDeep.

Set Implicit Arguments.

Definition KMsi: Kind := Bit 3.
Definition msiM {var}: Expr var (SyntaxKind KMsi) := ($3)%kami_expr.
Definition msiS {var}: Expr var (SyntaxKind KMsi) := ($2)%kami_expr.
Definition msiI {var}: Expr var (SyntaxKind KMsi) := ($1)%kami_expr.
Definition msiNP {var}: Expr var (SyntaxKind KMsi) := ($0)%kami_expr.

Section Directory.
  Context `{ReifyConfig} `{TopoConfig}.

  Definition KDir :=
    STRUCT { "dir_st" :: KMsi;
             "dir_excl" :: KCIdx;
             "dir_sharers" :: KCBv }.

  Definition compile_dir_get {var}
             (oidx: KCIdx @ var) (dir: (Struct KDir) @ var): KMsi @ var :=
    (let dir_st := dir!KDir@."dir_st" in
     let dir_excl := dir!KDir@."dir_excl" in
     let dir_sharers := dir!KDir@."dir_sharers" in
     IF (dir_st == msiM && dir_excl == oidx) then msiM
     else IF (dir_st == msiS && bvTest dir_sharers oidx) then msiS
     else msiI)%kami_expr.

End Directory.

Section Instances.
  Context `{TopoConfig}.
  Variable lgWay: nat.

  Instance MsiCompExtType: CompExtType :=
    {| kind_of_hetype :=
         fun het => match het with
                    | HDir => Struct KDir
                    end
    |}.

  Fixpoint compile_dir_exp
           (var: Kind -> Type) {het}
           (msgIn: var (Struct KMsg))
           (ul: var (Struct UL)) (dl: var (Struct DL))
           (ostvars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
           (he: heexp (hvar_of var) het): Expr var (SyntaxKind (kind_of het)) :=
    (match he in (hexp_dir _ h) return (Expr var (SyntaxKind (kind_of h))) with
     | HDirC _ => #(HVector.hvec_ith ostvars Msi.dir)
     | HDirGetSt dir => ((compile_dir_exp msgIn ul dl ostvars dir)!KDir@."dir_st")
     | HDirGetExcl dir => ((compile_dir_exp msgIn ul dl ostvars dir)!KDir@."dir_excl")
     | HDirGetStO oidx dir => compile_dir_get (compile_bexp ostvars msgIn ul dl oidx)
                                              (compile_dir_exp msgIn ul dl ostvars dir)
     | HDirGetSh dir => ((compile_dir_exp msgIn ul dl ostvars dir)!KDir@."dir_sharers")
     | HDirRemoveSh sh cidx =>
       bvUnset (compile_dir_exp msgIn ul dl ostvars sh) (compile_bexp ostvars msgIn ul dl cidx)
     | HDirAddSharer oidx dir =>
       (let kdir := compile_dir_exp msgIn ul dl ostvars dir in
        STRUCT { "dir_st" ::= msiS;
                 "dir_excl" ::= kdir!KDir@."dir_excl";
                 "dir_sharers" ::=
                   IF (kdir!KDir@."dir_st" == msiS)
                 then (bvSet (kdir!KDir@."dir_sharers") (compile_bexp ostvars msgIn ul dl oidx))
                 else (bvSingleton _ (compile_bexp ostvars msgIn ul dl oidx)) })
     | HDirRemoveSharer oidx dir =>
       (let kdir := compile_dir_exp msgIn ul dl ostvars dir in
        STRUCT { "dir_st" ::= msiS;
                 "dir_excl" ::= kdir!KDir@."dir_excl";
                 "dir_sharers" ::= bvUnset (kdir!KDir@."dir_sharers")
                                           (compile_bexp ostvars msgIn ul dl oidx) })

     | HDirSetM oidx => (STRUCT { "dir_st" ::= msiM;
                                  "dir_excl" ::= compile_bexp ostvars msgIn ul dl oidx;
                                  "dir_sharers" ::= $$Default })
     | HDirSetS oinds => (STRUCT { "dir_st" ::= msiS;
                                   "dir_excl" ::= $$Default;
                                   "dir_sharers" ::=
                                     List.fold_left
                                       (fun bv i => bvSet bv i)
                                       (map (compile_bexp ostvars msgIn ul dl) oinds)
                                       $$Default })
     | HDirSetI _ => (STRUCT { "dir_st" ::= msiI;
                               "dir_excl" ::= $$Default;
                               "dir_sharers" ::= $$Default })

     | HRqUpFrom oidx => {$TopoTemplate.rqUpIdx, compile_dir_exp msgIn ul dl ostvars oidx}
     | HRsUpFrom oidx => {$TopoTemplate.rsUpIdx, compile_dir_exp msgIn ul dl ostvars oidx}
     | HDownTo oidx => {$TopoTemplate.downIdx, compile_dir_exp msgIn ul dl ostvars oidx}
     | HRqUpFromM oinds => compile_dir_exp msgIn ul dl ostvars oinds
     | HRsUpFromM oinds => compile_dir_exp msgIn ul dl ostvars oinds
     | HDownToM oinds => compile_dir_exp msgIn ul dl ostvars oinds
     | HSingleton se => bvSet $$Default (_truncate_ (compile_dir_exp msgIn ul dl ostvars se))
     | HInvalidate se => msiI
     end)%kami_expr.

  Definition compile_dir_OPrec
             (var: Kind -> Type)
             (msgIn: var (Struct KMsg))
             (ul: var (Struct UL)) (dl: var (Struct DL))
             (ostvars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
             (pd: heoprec (hvar_of var)): Expr var (SyntaxKind Bool) :=
    (match pd with
     | DirLastSharer cidx =>
       bvIsSingleton (#(HVector.hvec_ith ostvars Msi.dir)!KDir@."dir_sharers")
                     (compile_bexp ostvars msgIn ul dl cidx)
     | DirNotLastSharer _ =>
       bvCount (#(HVector.hvec_ith ostvars Msi.dir)!KDir@."dir_sharers") > $1
     | DirOtherSharerExists cidx =>
       bvUnset (#(HVector.hvec_ith ostvars Msi.dir)!KDir@."dir_sharers")
               (compile_bexp ostvars msgIn ul dl cidx) != $0
     end)%kami_expr.

  Instance MsiCompExtExp: CompExtExp :=
    {| compile_eexp := compile_dir_exp;
       compile_eoprec := compile_dir_OPrec
    |}.

  Definition MsiInfo :=
    STRUCT { "msi_owned" :: Bool;
             "msi_status" :: KMsi;
             "msi_dir_st" :: KMsi;
             "msi_dir_sharers" :: Bit hcfg_children_max }.

  Definition MsiCacheLine := CacheLine hcfg_addr_sz lgWay (Struct MsiInfo) KValue.
  Definition MsiCacheLineK := CacheLineK hcfg_addr_sz lgWay (Struct MsiInfo) KValue.

  Definition msi_compile_info_read
             (var: Kind -> Type) (pinfo: Expr var (SyntaxKind (Struct MsiInfo)))
    : Expr var (SyntaxKind (Vector.nth
                              (Vector.map (Struct.attrType (A:=Kind))
                                          (CacheLine hcfg_addr_sz lgWay (Struct MsiInfo) KValue))
                              (MsiCacheLine !! "info"))) :=
    (STRUCT { "msi_owned" ::= pinfo!MsiInfo@."msi_owned";
              "msi_status" ::=
                IF (pinfo!MsiInfo@."msi_status" == msiNP)
              then msiI else pinfo!MsiInfo@."msi_status";
              "msi_dir_st" ::=
                IF (pinfo!MsiInfo@."msi_dir_st" == msiNP)
              then msiI else pinfo!MsiInfo@."msi_dir_st";
              "msi_dir_sharers" ::= pinfo!MsiInfo@."msi_dir_sharers" })%kami_expr.

  Definition msi_compile_line_read
             (var: Kind -> Type) (line: var MsiCacheLineK)
    : Expr var (SyntaxKind MsiCacheLineK) :=
    (updStruct (#line) (MsiCacheLine !! "info")
               (msi_compile_info_read (#line!MsiCacheLine@."info")))%kami_expr.

  Definition msi_compile_line_to_ostVars
             (var: Kind -> Type) (line: var MsiCacheLineK)
             (cont: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty) ->
                    ActionT var Void): ActionT var Void :=
    (LET value <- #line!MsiCacheLine@."value";
    LET pinfo <- #line!MsiCacheLine@."info";
    LET owned <- #pinfo!MsiInfo@."msi_owned";
    LET status: KMsi <- #pinfo!MsiInfo@."msi_status";
    LET dir <- STRUCT { "dir_st" ::= #pinfo!MsiInfo@."msi_dir_st";
                        "dir_excl" ::= bvFirstSet (#pinfo!MsiInfo@."msi_dir_sharers");
                        "dir_sharers" ::= #pinfo!MsiInfo@."msi_dir_sharers" };
    cont (value, (owned, (status, (dir, tt)))))%kami_action.

  Definition msi_compile_line_update
             (var: Kind -> Type) (line: var MsiCacheLineK)
             i ht (Heq: Vector.nth hostf_ty i = ht)
             (ve: Expr var (SyntaxKind (kind_of ht))): Expr var (SyntaxKind MsiCacheLineK).
  Proof.
    subst ht.
    refine (if Fin.eq_dec i Msi.val then _
            else if Fin.eq_dec i Msi.owned then _
                 else if Fin.eq_dec i Msi.status then _
                      else if Fin.eq_dec i Msi.dir then _
                           else ($$Default)%kami_expr); subst i.
    - exact (STRUCT { "addr" ::= #line!MsiCacheLine@."addr";
                      "info_hit" ::= #line!MsiCacheLine@."info_hit";
                      "info_way" ::= #line!MsiCacheLine@."info_way";
                      "info_write" ::= #line!MsiCacheLine@."info_write";
                      "info" ::= #line!MsiCacheLine@."info";
                      "value_write" ::= $$true;
                      "value" ::= ve })%kami_expr.
    - exact (STRUCT { "addr" ::= #line!MsiCacheLine@."addr";
                      "info_hit" ::= #line!MsiCacheLine@."info_hit";
                      "info_way" ::= #line!MsiCacheLine@."info_way";
                      "info_write" ::= $$true;
                      "info" ::= updStruct (#line!MsiCacheLine@."info")%kami_expr
                                           (MsiInfo!!"msi_owned")
                                           ve;
                      "value_write" ::= #line!MsiCacheLine@."value_write";
                      "value" ::= #line!MsiCacheLine@."value" })%kami_expr.
    - exact (STRUCT { "addr" ::= #line!MsiCacheLine@."addr";
                      "info_hit" ::= #line!MsiCacheLine@."info_hit";
                      "info_way" ::= #line!MsiCacheLine@."info_way";
                      "info_write" ::= $$true;
                      "info" ::= updStruct (#line!MsiCacheLine@."info")%kami_expr
                                           (MsiInfo!!"msi_status")
                                           ve;
                      "value_write" ::= #line!MsiCacheLine@."value_write";
                      "value" ::= #line!MsiCacheLine@."value" })%kami_expr.
    - exact (STRUCT { "addr" ::= #line!MsiCacheLine@."addr";
                      "info_hit" ::= #line!MsiCacheLine@."info_hit";
                      "info_way" ::= #line!MsiCacheLine@."info_way";
                      "info_write" ::= $$true;
                      "info" ::=
                        STRUCT { "msi_owned" ::= #line!MsiCacheLine@."info"!MsiInfo@."msi_owned";
                                 "msi_status" ::= #line!MsiCacheLine@."info"!MsiInfo@."msi_status";
                                 "msi_dir_st" ::= ve!KDir@."dir_st";
                                 "msi_dir_sharers" ::=
                                   (IF (ve!KDir@."dir_st" == msiS)
                                    then (ve!KDir@."dir_sharers")
                                    else (bvSingleton _ (ve!KDir@."dir_excl"))) };
                      "value_write" ::= #line!MsiCacheLine@."value_write";
                      "value" ::= #line!MsiCacheLine@."value" })%kami_expr.
  Defined.

  Definition msi_check_inv_response (i: Fin.t Syntax.ost_sz) (st: nat): bool :=
    if Fin.eq_dec i Msi.status
    then (if Peano_dec.eq_nat_dec st Msi.msiNP
          then true else false)
    else false.

  Instance MsiCompLineRW: CompLineRW :=
    {| lineK := MsiCacheLineK;
       get_line_addr := fun _ line => (#line!MsiCacheLine@."addr")%kami_expr;
       set_line_addr := fun _ line naddr => updStruct line (MsiCacheLine!!"addr") naddr;
       compile_line_read := msi_compile_line_read;
       compile_line_to_ostVars := msi_compile_line_to_ostVars;
       compile_line_update := msi_compile_line_update;
       check_inv_response := msi_check_inv_response |}.

End Instances.

Require Import Hemiola.Ex.TopoTemplate.

Section Cache.
  Context `{TopoConfig}.
  Variables (oidx: IdxT)
            (indexSz lgWay lgNumVictim: nat).

  Definition BitsPerByte := 8.
  Definition offsetSz := Nat.log2 (Nat.div hcfg_addr_sz BitsPerByte).
  Definition tagSz := hcfg_addr_sz - indexSz - offsetSz.

  Definition getIndex (var: Kind -> Type)
             (addr: fullType var (SyntaxKind (Bit (offsetSz + indexSz + tagSz))))
    : Expr var (SyntaxKind (Bit indexSz)) :=
    (UniBit (ConstExtract _ _ _) #addr)%kami_expr.

  Definition getTag (var: Kind -> Type)
             (addr: fullType var (SyntaxKind (Bit (offsetSz + indexSz + tagSz))))
    : Expr var (SyntaxKind (Bit tagSz)) :=
    (_truncLsb_ #addr)%kami_expr.

  Definition buildAddr (var: Kind -> Type)
             (tag: fullType var (SyntaxKind (Bit tagSz)))
             (index: fullType var (SyntaxKind (Bit indexSz)))
    : Expr var (SyntaxKind (Bit (offsetSz + indexSz + tagSz))) :=
    {#tag, {#index, $0}}%kami_expr.

  Definition evictF (var: Kind -> Type)
             (minfo: Expr var (SyntaxKind (Struct MsiInfo))): Expr var (SyntaxKind Bool) :=
    (minfo!MsiInfo@."msi_dir_st" == msiI)%kami_expr.

  Definition msiCache :=
    cache oidx lgWay lgNumVictim KValue getIndex getTag buildAddr evictF.

End Cache.
