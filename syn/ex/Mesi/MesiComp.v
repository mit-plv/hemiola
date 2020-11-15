Require Import String List.
Import ListNotations.

Require Import Kami.Kami.
Require Import Hemiola.Index.
Require Import Compiler.HemiolaDeep Compiler.CompileK.
Require Import MesiDeep.

Set Implicit Arguments.

Definition KMesi: Kind := Bit 3.
Definition mesiM {var}: Expr var (SyntaxKind KMesi) := ($4)%kami_expr.
Definition mesiE {var}: Expr var (SyntaxKind KMesi) := ($3)%kami_expr.
Definition mesiS {var}: Expr var (SyntaxKind KMesi) := ($2)%kami_expr.
Definition mesiI {var}: Expr var (SyntaxKind KMesi) := ($1)%kami_expr.
Definition mesiNP {var}: Expr var (SyntaxKind KMesi) := ($0)%kami_expr.

Section Directory.
  Context `{ReifyConfig} `{TopoConfig}.

  Definition KDir :=
    STRUCT { "dir_st" :: KMesi;
             "dir_excl" :: KCIdx;
             "dir_sharers" :: KCBv }.

  Definition compile_dir_get {var}
             (oidx: KCIdx @ var) (dir: (Struct KDir) @ var): Expr var (SyntaxKind KMesi) :=
    (let dir_st := dir!KDir@."dir_st" in
     let dir_excl := dir!KDir@."dir_excl" in
     let dir_sharers := dir!KDir@."dir_sharers" in
     IF (dir_st == mesiM && dir_excl == oidx) then mesiM
     else IF (dir_st == mesiE && dir_excl == oidx) then mesiE
     else IF (dir_st == mesiS && bvTest dir_sharers oidx) then mesiS
     else mesiI)%kami_expr.

End Directory.

Section Instances.
  Context `{TopoConfig}.
  Variables mshrNumPRqs mshrNumCRqs: nat.

  Instance MesiCompExtType: CompExtType :=
    {| kind_of_hetype := fun het => match het with
                                    | HDir => Struct KDir
                                    end
    |}.

  Arguments compile_bexp {_ _ _ _ _ _ _ _ _ _ _} _ _ _ {_}.
  Fixpoint compile_dir_exp
           (var: Kind -> Type) {het}
           (msgIn: var (Struct KMsg))
           (mshr: var (Struct (MSHRRq mshrNumPRqs mshrNumCRqs)))
           (ostvars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
           (he: heexp (hvar_of var) het): Expr var (SyntaxKind (kind_of het)) :=
    (match he in (hexp_dir _ h) return (Expr var (SyntaxKind (kind_of h))) with
     | HDirC _ => #(HVector.hvec_ith ostvars Mesi.dir)
     | HDirGetSt dir => ((compile_dir_exp msgIn mshr ostvars dir)!KDir@."dir_st")
     | HDirGetExcl dir => ((compile_dir_exp msgIn mshr ostvars dir)!KDir@."dir_excl")
     | HDirGetStO oidx dir => compile_dir_get (compile_bexp msgIn mshr ostvars oidx)
                                              (compile_dir_exp msgIn mshr ostvars dir)
     | HDirGetSh dir => ((compile_dir_exp msgIn mshr ostvars dir)!KDir@."dir_sharers")
     | HDirRemoveSh sh cidx =>
       bvUnset (compile_dir_exp msgIn mshr ostvars sh) (compile_bexp msgIn mshr ostvars cidx)
     | HDirAddSharer oidx dir =>
       (let kdir := compile_dir_exp msgIn mshr ostvars dir in
        STRUCT { "dir_st" ::= mesiS;
                 "dir_excl" ::= kdir!KDir@."dir_excl";
                 "dir_sharers" ::=
                   IF (kdir!KDir@."dir_st" == mesiS)
                 then (bvSet (kdir!KDir@."dir_sharers") (compile_bexp msgIn mshr ostvars oidx))
                 else (bvSingleton _ (compile_bexp msgIn mshr ostvars oidx)) })
     | HDirRemoveSharer oidx dir =>
       (let kdir := compile_dir_exp msgIn mshr ostvars dir in
        STRUCT { "dir_st" ::= mesiS;
                 "dir_excl" ::= kdir!KDir@."dir_excl";
                 "dir_sharers" ::= bvUnset (kdir!KDir@."dir_sharers")
                                           (compile_bexp msgIn mshr ostvars oidx) })

     | HDirSetM oidx => (STRUCT { "dir_st" ::= mesiM;
                                  "dir_excl" ::= compile_bexp msgIn mshr ostvars oidx;
                                  "dir_sharers" ::= $$Default })
     | HDirSetE oidx => (STRUCT { "dir_st" ::= mesiE;
                                  "dir_excl" ::= compile_bexp msgIn mshr ostvars oidx;
                                  "dir_sharers" ::= $$Default })
     | HDirSetS oinds => (STRUCT { "dir_st" ::= mesiS;
                                   "dir_excl" ::= $$Default;
                                   "dir_sharers" ::=
                                     List.fold_left
                                       (fun bv i => bvSet bv i)
                                       (map (compile_bexp msgIn mshr ostvars) oinds)
                                       $$Default })
     | HDirSetI _ => (STRUCT { "dir_st" ::= mesiI;
                               "dir_excl" ::= $$Default;
                               "dir_sharers" ::= $$Default })

     | HRqUpFrom oidx => {$TopoTemplate.rqUpIdx, compile_dir_exp msgIn mshr ostvars oidx}
     | HRsUpFrom oidx => {$TopoTemplate.rsUpIdx, compile_dir_exp msgIn mshr ostvars oidx}
     | HDownTo oidx => {$TopoTemplate.downIdx, compile_dir_exp msgIn mshr ostvars oidx}
     | HRqUpFromM oinds => compile_dir_exp msgIn mshr ostvars oinds
     | HRsUpFromM oinds => compile_dir_exp msgIn mshr ostvars oinds
     | HDownToM oinds => compile_dir_exp msgIn mshr ostvars oinds
     | HSingleton se => bvSet $$Default (_truncate_ (compile_dir_exp msgIn mshr ostvars se))
     | HInvalidate se =>
       (* (IF ((compile_bexp msgIn mshr ostvars se) == mesiNP) then mesiNP else mesiI) *)
       mesiI
     end)%kami_expr.

  Definition compile_dir_OPrec
             (var: Kind -> Type)
             (msgIn: var (Struct KMsg))
             (mshr: var (Struct (MSHRRq mshrNumPRqs mshrNumCRqs)))
             (ostvars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
             (pd: heoprec (hvar_of var)): Expr var (SyntaxKind Bool) :=
    (match pd with
     | DirLastSharer cidx =>
       bvIsSingleton (#(HVector.hvec_ith ostvars Mesi.dir)!KDir@."dir_sharers")
                     (compile_bexp msgIn mshr ostvars cidx)
     | DirNotLastSharer _ =>
       bvCount (#(HVector.hvec_ith ostvars Mesi.dir)!KDir@."dir_sharers") > $1
     | DirOtherSharerExists cidx =>
       bvUnset (#(HVector.hvec_ith ostvars Mesi.dir)!KDir@."dir_sharers")
               (compile_bexp msgIn mshr ostvars cidx) != $0
     end)%kami_expr.

  Instance MesiCompExtExp: CompExtExp mshrNumPRqs mshrNumCRqs :=
    {| compile_eexp := compile_dir_exp;
       compile_eoprec := compile_dir_OPrec
    |}.

  Definition MesiInfo :=
    STRUCT { "mesi_owned" :: Bool;
             "mesi_status" :: KMesi;
             "mesi_dir_st" :: KMesi;
             "mesi_dir_sharers" :: Bit hcfg_children_max }.
  Let MesiInfoK := Struct MesiInfo.

  Variables indexSz lgWay edirLgWay: nat.

  Definition MesiInfoRead := InfoRead MesiInfoK indexSz hcfg_addr_sz lgWay edirLgWay.
  Let MesiInfoReadK := Struct MesiInfoRead.

  Definition mesi_compile_info_to_ostVars
             (var: Kind -> Type) (pinfo: var MesiInfoK)
             (cont: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty) ->
                    ActionT var Void): ActionT var Void :=
    (LET value <- $$Default;
    LET owned <- #pinfo!MesiInfo@."mesi_owned";
    LET status: KMesi <- #pinfo!MesiInfo@."mesi_status";
    LET dir <- STRUCT { "dir_st" ::=
                          (IF (#pinfo!MesiInfo@."mesi_dir_st" == mesiNP)
                           then mesiI else #pinfo!MesiInfo@."mesi_dir_st");
                        "dir_excl" ::= bvFirstSet (#pinfo!MesiInfo@."mesi_dir_sharers");
                        "dir_sharers" ::= #pinfo!MesiInfo@."mesi_dir_sharers" };
    cont (value, (owned, (status, (dir, tt)))))%kami_action.

  Definition mesi_compile_value_read_to_ostVars
             (var: Kind -> Type)
             (ostVars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
             (rval: var KValue)
    : HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty) :=
    HVector.hvec_upd ostVars Mesi.val rval.

  Definition MesiLineWrite := LineWrite lgWay edirLgWay MesiInfoK.
  Let MesiLineWriteK := Struct MesiLineWrite.

  Definition mesi_compile_line_update
             (var: Kind -> Type) (line: var MesiLineWriteK)
             i ht (Heq: Vector.nth hostf_ty i = ht)
             (ve: Expr var (SyntaxKind (kind_of ht))): Expr var (SyntaxKind MesiLineWriteK).
  Proof.
    subst ht.
    refine (if Fin.eq_dec i Mesi.val then _
            else if Fin.eq_dec i Mesi.owned then _
                 else if Fin.eq_dec i Mesi.status then _
                      else if Fin.eq_dec i Mesi.dir then _
                           else ($$Default)%kami_expr); subst i.
    - exact (STRUCT { "addr" ::= #line!MesiLineWrite@."addr";
                      "info_write" ::= #line!MesiLineWrite@."info_write";
                      "info_hit" ::= #line!MesiLineWrite@."info_hit";
                      "info_way" ::= #line!MesiLineWrite@."info_way";
                      "edir_hit" ::= #line!MesiLineWrite@."edir_hit";
                      "edir_way" ::= #line!MesiLineWrite@."edir_way";
                      "edir_slot" ::= #line!MesiLineWrite@."edir_slot";
                      "info" ::= #line!MesiLineWrite@."info";
                      "value_write" ::= $$true;
                      "value" ::= ve;
                      "may_victim" ::= #line!MesiLineWrite@."may_victim";
                      "reps" ::= #line!MesiLineWrite@."reps" })%kami_expr.
    - exact (STRUCT { "addr" ::= #line!MesiLineWrite@."addr";
                      "info_write" ::= $$true;
                      "info_hit" ::= #line!MesiLineWrite@."info_hit";
                      "info_way" ::= #line!MesiLineWrite@."info_way";
                      "edir_hit" ::= #line!MesiLineWrite@."edir_hit";
                      "edir_way" ::= #line!MesiLineWrite@."edir_way";
                      "edir_slot" ::= #line!MesiLineWrite@."edir_slot";
                      "info" ::= updStruct (#line!MesiLineWrite@."info")%kami_expr
                                           (MesiInfo!!"mesi_owned")
                                           ve;
                      "value_write" ::= #line!MesiLineWrite@."value_write";
                      "value" ::= #line!MesiLineWrite@."value";
                      "may_victim" ::= #line!MesiLineWrite@."may_victim";
                      "reps" ::= #line!MesiLineWrite@."reps" })%kami_expr.
    - exact (STRUCT { "addr" ::= #line!MesiLineWrite@."addr";
                      "info_write" ::= $$true;
                      "info_hit" ::= #line!MesiLineWrite@."info_hit";
                      "info_way" ::= #line!MesiLineWrite@."info_way";
                      "edir_hit" ::= #line!MesiLineWrite@."edir_hit";
                      "edir_way" ::= #line!MesiLineWrite@."edir_way";
                      "edir_slot" ::= #line!MesiLineWrite@."edir_slot";
                      "info" ::= updStruct (#line!MesiLineWrite@."info")%kami_expr
                                           (MesiInfo!!"mesi_status")
                                           ve;
                      "value_write" ::= #line!MesiLineWrite@."value_write";
                      "value" ::= #line!MesiLineWrite@."value";
                      "may_victim" ::= #line!MesiLineWrite@."may_victim";
                      "reps" ::= #line!MesiLineWrite@."reps" })%kami_expr.
    - exact (STRUCT { "addr" ::= #line!MesiLineWrite@."addr";
                      "info_write" ::= $$true;
                      "info_hit" ::= #line!MesiLineWrite@."info_hit";
                      "info_way" ::= #line!MesiLineWrite@."info_way";
                      "edir_hit" ::= #line!MesiLineWrite@."edir_hit";
                      "edir_way" ::= #line!MesiLineWrite@."edir_way";
                      "edir_slot" ::= #line!MesiLineWrite@."edir_slot";
                      "info" ::=
                        STRUCT { "mesi_owned" ::= #line!MesiLineWrite@."info"!MesiInfo@."mesi_owned";
                                 "mesi_status" ::= #line!MesiLineWrite@."info"!MesiInfo@."mesi_status";
                                 "mesi_dir_st" ::= ve!KDir@."dir_st";
                                 "mesi_dir_sharers" ::=
                                   (IF (ve!KDir@."dir_st" == mesiS)
                                    then (ve!KDir@."dir_sharers")
                                    else (bvSingleton _ (ve!KDir@."dir_excl"))) };
                      "value_write" ::= #line!MesiLineWrite@."value_write";
                      "value" ::= #line!MesiLineWrite@."value";
                      "may_victim" ::= #line!MesiLineWrite@."may_victim";
                      "reps" ::= #line!MesiLineWrite@."reps" })%kami_expr.
  Defined.

  Instance MesiCompLineRW: CompLineRW lgWay edirLgWay :=
    {| infoK := MesiInfoK;
       invRsId := idx_to_word hcfg_msg_id_sz Mesi.mesiInvRs;
       compile_info_to_ostVars := mesi_compile_info_to_ostVars;
       compile_value_read_to_ostVars := mesi_compile_value_read_to_ostVars;
       compile_line_update := mesi_compile_line_update |}.

End Instances.

Require Import Hemiola.Ex.TopoTemplate.

Section Cache.
  Context `{TopoConfig}.
  Variables (oidx: IdxT)
            (indexSz lgWay edirLgWay predNumVictims mshrSlotSz: nat).

  Definition BitsPerByte := 8.
  Definition offsetSz := Nat.log2 (Nat.div hcfg_addr_sz BitsPerByte) + hcfg_line_values_lg.
  Definition tagSz := hcfg_addr_sz - indexSz - offsetSz.

  Definition getIndexE (var: Kind -> Type)
             (addr: Expr var (SyntaxKind (Bit (offsetSz + indexSz + tagSz))))
    : Expr var (SyntaxKind (Bit indexSz)) :=
    (UniBit (ConstExtract _ _ _) addr)%kami_expr.

  Definition getIndex (var: Kind -> Type)
             (addr: fullType var (SyntaxKind (Bit (offsetSz + indexSz + tagSz))))
    : Expr var (SyntaxKind (Bit indexSz)) :=
    getIndexE (#addr)%kami_expr.

  Definition getTag (var: Kind -> Type)
             (addr: fullType var (SyntaxKind (Bit (offsetSz + indexSz + tagSz))))
    : Expr var (SyntaxKind (Bit tagSz)) :=
    (_truncLsb_ #addr)%kami_expr.

  Definition buildAddr (var: Kind -> Type)
             (tag: fullType var (SyntaxKind (Bit tagSz)))
             (index: fullType var (SyntaxKind (Bit indexSz)))
    : Expr var (SyntaxKind (Bit (offsetSz + indexSz + tagSz))) :=
    {#tag, {#index, $0}}%kami_expr.

  Definition mshrConflictF (var: Kind -> Type)
             (addr1 addr2: Expr var (SyntaxKind (Bit (offsetSz + indexSz + tagSz))))
    : Expr var (SyntaxKind Bool) :=
    (addr1 != addr2 && getIndexE addr1 == getIndexE addr2)%kami_expr.

  Definition MesiEDir :=
    STRUCT { "mesi_edir_owned" :: Bool;
             "mesi_edir_st" :: KMesi;
             "mesi_edir_sharers" :: Bit hcfg_children_max }.
  Let MesiEDirK := Struct MesiEDir.

  Definition edirToInfo (var: Kind -> Type)
             (edir: fullType var (SyntaxKind MesiEDirK))
    : Expr var (SyntaxKind (Struct MesiInfo)) :=
    (STRUCT { "mesi_owned" ::= #edir!MesiEDir@."mesi_edir_owned";
              "mesi_status" ::= mesiI;
              "mesi_dir_st" ::= #edir!MesiEDir@."mesi_edir_st";
              "mesi_dir_sharers" ::= #edir!MesiEDir@."mesi_edir_status" })%kami_expr.

  Definition edirFromInfo (var: Kind -> Type)
             (pinfo: fullType var (SyntaxKind (Struct MesiInfo)))
    : Expr var (SyntaxKind MesiEDirK) :=
    (STRUCT { "mesi_edir_owned" ::= #pinfo!MesiInfo@."mesi_owned";
              "mesi_edir_st" ::= #pinfo!MesiInfo@."mesi_dir_st";
              "mesi_edir_sharers" ::= #pinfo!MesiInfo@."mesi_dir_sharers" })%kami_expr.

  Definition isJustDir (var: Kind -> Type)
             (pinfo: fullType var (SyntaxKind (Struct MesiInfo)))
    : Expr var (SyntaxKind Bool) :=
    ((#pinfo!MesiInfo@."mesi_status" <= mesiI) &&
     (#pinfo!MesiInfo@."mesi_dir_st" != mesiE))%kami_expr.

  Definition isDirInvalid (var: Kind -> Type)
             (pinfo: fullType var (SyntaxKind (Struct MesiInfo)))
    : Expr var (SyntaxKind Bool) :=
    (#pinfo!MesiInfo@."mesi_dir_st" <= mesiI)%kami_expr.

  Definition edirEmptySlot (var: Kind -> Type)
             (edir: Expr var (SyntaxKind MesiEDirK))
    : Expr var (SyntaxKind Bool) :=
    (edir!MesiEDir@."mesi_edir_st" <= mesiI)%kami_expr.

  Definition mesiInfoInit: ConstT (Struct MesiInfo) :=
    (CSTRUCT { "mesi_owned" ::= ConstBool false;
               "mesi_status" ::= ConstBit $1;
               "mesi_dir_st" ::= ConstBit $1;
               "mesi_dir_sharers" ::= ConstBit $0 })%init.

  Definition mesiEDirInit: ConstT MesiEDirK :=
    (CSTRUCT { "mesi_edir_owned" ::= ConstBool false;
               "mesi_edir_st" ::= ConstBit $1;
               "mesi_edir_sharers" ::= ConstBit $0 })%init.

  Definition mesiL1: Modules :=
    cache oidx KValue lgWay 0
          mesiInfoInit getIndex getTag buildAddr isDirInvalid predNumVictims.

  Definition mesiLi: Modules :=
    ncid oidx KValue lgWay edirLgWay
         mesiInfoInit mesiEDirInit
         getIndex getTag buildAddr edirToInfo edirFromInfo isJustDir isDirInvalid edirEmptySlot
         predNumVictims.

End Cache.
