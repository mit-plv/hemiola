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
  Context `{hconfig}.

  Definition KDir :=
    STRUCT { "dir_st" :: KMesi;
             "dir_excl" :: KCIdx;
             "dir_sharers" :: KCBv }.

  Definition compile_dir_get {var}
             (oidx: KCIdx @ var) (dir: (Struct KDir) @ var): KMesi @ var :=
    (let dir_st := dir!KDir@."dir_st" in
     let dir_excl := dir!KDir@."dir_excl" in
     let dir_sharers := dir!KDir@."dir_sharers" in
     IF (dir_st == mesiM && dir_excl == oidx) then mesiM
     else IF (dir_st == mesiE && dir_excl == oidx) then mesiE
     else IF (dir_st == mesiS && bvTest dir_sharers oidx) then mesiS
     else mesiI)%kami_expr.

End Directory.

Existing Instance MesiHOStateIfcFull.

Section Instances.
  Variable lgWay: nat.

  Instance MesiCompExtType: CompExtType :=
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
     | HDirC _ => #(HVector.hvec_ith ostvars Mesi.dir)
     | HDirGetSt dir => ((compile_dir_exp msgIn ul dl ostvars dir)!KDir@."dir_st")
     | HDirGetExcl dir => ((compile_dir_exp msgIn ul dl ostvars dir)!KDir@."dir_excl")
     | HDirGetStO oidx dir => compile_dir_get (compile_bexp ostvars msgIn ul dl oidx)
                                              (compile_dir_exp msgIn ul dl ostvars dir)
     | HDirGetSh dir => ((compile_dir_exp msgIn ul dl ostvars dir)!KDir@."dir_sharers")
     | HDirRemoveSh sh cidx =>
       bvUnset (compile_dir_exp msgIn ul dl ostvars sh) (compile_bexp ostvars msgIn ul dl cidx)
     | HDirAddSharer oidx dir =>
       (let kdir := compile_dir_exp msgIn ul dl ostvars dir in
        STRUCT { "dir_st" ::= mesiS;
                 "dir_excl" ::= kdir!KDir@."dir_excl";
                 "dir_sharers" ::=
                   IF (kdir!KDir@."dir_st" == mesiS)
                 then (bvSet (kdir!KDir@."dir_sharers") (compile_bexp ostvars msgIn ul dl oidx))
                 else (bvSingleton _ (compile_bexp ostvars msgIn ul dl oidx)) })
     | HDirRemoveSharer oidx dir =>
       (let kdir := compile_dir_exp msgIn ul dl ostvars dir in
        STRUCT { "dir_st" ::= mesiS;
                 "dir_excl" ::= kdir!KDir@."dir_excl";
                 "dir_sharers" ::= bvUnset (kdir!KDir@."dir_sharers")
                                           (compile_bexp ostvars msgIn ul dl oidx) })

     | HDirSetM oidx => (STRUCT { "dir_st" ::= mesiM;
                                  "dir_excl" ::= compile_bexp ostvars msgIn ul dl oidx;
                                  "dir_sharers" ::= $$Default })
     | HDirSetE oidx => (STRUCT { "dir_st" ::= mesiE;
                                  "dir_excl" ::= compile_bexp ostvars msgIn ul dl oidx;
                                  "dir_sharers" ::= $$Default })
     | HDirSetS oinds => (STRUCT { "dir_st" ::= mesiS;
                                   "dir_excl" ::= $$Default;
                                   "dir_sharers" ::=
                                     List.fold_left
                                       (fun bv i => bvSet bv i)
                                       (map (compile_bexp ostvars msgIn ul dl) oinds)
                                       $$Default })
     | HDirSetI _ => (STRUCT { "dir_st" ::= mesiI;
                               "dir_excl" ::= $$Default;
                               "dir_sharers" ::= $$Default })

     | HRqUpFrom oidx => {$TopoTemplate.rqUpIdx, compile_dir_exp msgIn ul dl ostvars oidx}
     | HRsUpFrom oidx => {$TopoTemplate.rsUpIdx, compile_dir_exp msgIn ul dl ostvars oidx}
     | HDownTo oidx => {$TopoTemplate.downIdx, compile_dir_exp msgIn ul dl ostvars oidx}
     | HRqUpFromM oinds => compile_dir_exp msgIn ul dl ostvars oinds
     | HRsUpFromM oinds => compile_dir_exp msgIn ul dl ostvars oinds
     | HDownToM oinds => compile_dir_exp msgIn ul dl ostvars oinds
     | HSingleton se => bvSet $$Default (_truncate_ (compile_dir_exp msgIn ul dl ostvars se))
     | HInvalidate se =>
       (* (IF ((compile_bexp ostvars msgIn ul dl se) == mesiNP) then mesiNP else mesiI) *)
       mesiI
     end)%kami_expr.

  Definition compile_dir_OPrec
             (var: Kind -> Type)
             (msgIn: var (Struct KMsg))
             (ul: var (Struct UL)) (dl: var (Struct DL))
             (ostvars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
             (pd: heoprec (hvar_of var)): Expr var (SyntaxKind Bool) :=
    (match pd with
     | DirLastSharer cidx =>
       bvIsSingleton (#(HVector.hvec_ith ostvars Mesi.dir)!KDir@."dir_sharers")
                     (compile_bexp ostvars msgIn ul dl cidx)
     | DirNotLastSharer _ =>
       bvCount (#(HVector.hvec_ith ostvars Mesi.dir)!KDir@."dir_sharers") > $1
     | DirOtherSharerExists cidx =>
       bvUnset (#(HVector.hvec_ith ostvars Mesi.dir)!KDir@."dir_sharers")
               (compile_bexp ostvars msgIn ul dl cidx) != $0
     end)%kami_expr.

  Instance MesiCompExtExp: CompExtExp :=
    {| compile_eexp := compile_dir_exp;
       compile_eoprec := compile_dir_OPrec
    |}.

  Definition MesiInfo :=
    STRUCT { "mesi_owned" :: Bool;
             "mesi_status" :: KMesi;
             "mesi_dir_st" :: KMesi;
             "mesi_dir_sharers" :: Bit hcfg_children_max }.

  Definition MesiCacheLine := CacheLine hcfg_addr_sz lgWay (Struct MesiInfo) KValue.
  Definition MesiCacheLineK := CacheLineK hcfg_addr_sz lgWay (Struct MesiInfo) KValue.

  Definition mesi_compile_info_read
             (var: Kind -> Type) (pinfo: Expr var (SyntaxKind (Struct MesiInfo)))
    : Expr var (SyntaxKind (Vector.nth
                              (Vector.map (Struct.attrType (A:=Kind))
                                          (CacheLine hcfg_addr_sz lgWay (Struct MesiInfo) KValue))
                              (MesiCacheLine !! "info"))) :=
    (STRUCT { "mesi_owned" ::= pinfo!MesiInfo@."mesi_owned";
              "mesi_status" ::=
                IF (pinfo!MesiInfo@."mesi_status" == mesiNP)
              then mesiI else pinfo!MesiInfo@."mesi_status";
              "mesi_dir_st" ::=
                IF (pinfo!MesiInfo@."mesi_dir_st" == mesiNP)
              then mesiI else pinfo!MesiInfo@."mesi_dir_st";
              "mesi_dir_sharers" ::= pinfo!MesiInfo@."mesi_dir_sharers" })%kami_expr.

  Definition mesi_compile_line_read
             (var: Kind -> Type) (line: var MesiCacheLineK)
    : Expr var (SyntaxKind MesiCacheLineK) :=
    (updStruct (#line) (MesiCacheLine !! "info")
               (mesi_compile_info_read (#line!MesiCacheLine@."info")))%kami_expr.

  Definition mesi_compile_line_to_ostVars
             (var: Kind -> Type) (line: var MesiCacheLineK)
             (cont: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty) ->
                    ActionT var Void): ActionT var Void :=
    (LET value <- #line!MesiCacheLine@."value";
    LET pinfo <- #line!MesiCacheLine@."info";
    LET owned <- #pinfo!MesiInfo@."mesi_owned";
    LET status: KMesi <- #pinfo!MesiInfo@."mesi_status";
    LET dir <- STRUCT { "dir_st" ::= #pinfo!MesiInfo@."mesi_dir_st";
                        "dir_excl" ::= bvFirstSet (#pinfo!MesiInfo@."mesi_dir_sharers");
                        "dir_sharers" ::= #pinfo!MesiInfo@."mesi_dir_sharers" };
    cont (value, (owned, (status, (dir, tt)))))%kami_action.

  Definition mesi_compile_line_update
             (var: Kind -> Type) (line: var MesiCacheLineK)
             i ht (Heq: Vector.nth hostf_ty i = ht)
             (ve: Expr var (SyntaxKind (kind_of ht))): Expr var (SyntaxKind MesiCacheLineK).
  Proof.
    subst ht.
    refine (if Fin.eq_dec i Mesi.val then _
            else if Fin.eq_dec i Mesi.owned then _
                 else if Fin.eq_dec i Mesi.status then _
                      else if Fin.eq_dec i Mesi.dir then _
                           else ($$Default)%kami_expr); subst i.
    - exact (STRUCT { "addr" ::= #line!MesiCacheLine@."addr";
                      "info_hit" ::= #line!MesiCacheLine@."info_hit";
                      "info_way" ::= #line!MesiCacheLine@."info_way";
                      "info_write" ::= #line!MesiCacheLine@."info_write";
                      "info" ::= #line!MesiCacheLine@."info";
                      "value_write" ::= $$true;
                      "value" ::= ve })%kami_expr.
    - exact (STRUCT { "addr" ::= #line!MesiCacheLine@."addr";
                      "info_hit" ::= #line!MesiCacheLine@."info_hit";
                      "info_way" ::= #line!MesiCacheLine@."info_way";
                      "info_write" ::= $$true;
                      "info" ::= updStruct (#line!MesiCacheLine@."info")%kami_expr
                                           (VectorFacts.Vector_find (fieldAccessor "mesi_owned") MesiInfo)
                                           ve;
                      "value_write" ::= #line!MesiCacheLine@."value_write";
                      "value" ::= #line!MesiCacheLine@."value" })%kami_expr.
    - exact (STRUCT { "addr" ::= #line!MesiCacheLine@."addr";
                      "info_hit" ::= #line!MesiCacheLine@."info_hit";
                      "info_way" ::= #line!MesiCacheLine@."info_way";
                      "info_write" ::= $$true;
                      "info" ::= updStruct (#line!MesiCacheLine@."info")%kami_expr
                                           (VectorFacts.Vector_find (fieldAccessor "mesi_status") MesiInfo)
                                           ve;
                      "value_write" ::= #line!MesiCacheLine@."value_write";
                      "value" ::= #line!MesiCacheLine@."value" })%kami_expr.
    - exact (STRUCT { "addr" ::= #line!MesiCacheLine@."addr";
                      "info_hit" ::= #line!MesiCacheLine@."info_hit";
                      "info_way" ::= #line!MesiCacheLine@."info_way";
                      "info_write" ::= $$true;
                      "info" ::=
                        STRUCT { "mesi_owned" ::= #line!MesiCacheLine@."info"!MesiInfo@."mesi_owned";
                                 "mesi_status" ::= #line!MesiCacheLine@."info"!MesiInfo@."mesi_status";
                                 "mesi_dir_st" ::= ve!KDir@."dir_st";
                                 "mesi_dir_sharers" ::=
                                   (IF (ve!KDir@."dir_st" == mesiS)
                                    then (ve!KDir@."dir_sharers")
                                    else (bvSingleton _ (ve!KDir@."dir_excl"))) };
                      "value_write" ::= #line!MesiCacheLine@."value_write";
                      "value" ::= #line!MesiCacheLine@."value" })%kami_expr.
  Defined.

  Definition mesi_check_inv_response (i: Fin.t Syntax.ost_sz) (st: nat): bool :=
    if Fin.eq_dec i Mesi.status
    then (if Peano_dec.eq_nat_dec st Mesi.mesiNP
          then true else false)
    else false.

  Instance MesiCompLineRW: CompLineRW :=
    {| lineK := MesiCacheLineK;
       get_line_addr := fun _ line => (#line!MesiCacheLine@."addr")%kami_expr;
       compile_line_read := mesi_compile_line_read;
       compile_line_to_ostVars := mesi_compile_line_to_ostVars;
       compile_line_update := mesi_compile_line_update;
       check_inv_response := mesi_check_inv_response |}.

End Instances.

Existing Instance MesiCompExtType.
Existing Instance MesiCompExtExp.

Require Import Hemiola.Ex.TopoTemplate.

(** TODO: move to somewhere else *)
Section Cache.
  Variables (oidx: IdxT)
            (tagSz indexSz offsetSz lgWay: nat).

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
             (minfo: Expr var (SyntaxKind (Struct MesiInfo))): Expr var (SyntaxKind Bool) :=
    (* ((minfo!MesiInfo@."mesi_dir_st" == mesiNP) *)
    (*  || minfo!MesiInfo@."mesi_dir_st" == mesiI)%kami_expr. *)
    (minfo!MesiInfo@."mesi_dir_st" == mesiI)%kami_expr.

  Definition mesiCache :=
    cache oidx lgWay KValue getIndex getTag buildAddr evictF.

End Cache.

(*********************
 *        Mem        *
 *         |         *
 *      LLC(Li)      *
 *       /   \       *
 *  L2(Li)   L2(Li)  *
 *   /  \     /  \   *
 * L1    L1 L1    L1 *
 **********************)
Definition topo: tree :=
  Node [Node [Node [Node nil; Node nil]; Node [Node nil; Node nil]]].
Definition dtr :=
  Eval vm_compute in (fst (tree2Topo topo 0)).

Definition l1LgWay: nat := 1.
Definition l2LgWay: nat := 2.  (* [l2LgWay] should be >=3 for liveness *)
Definition llLgWay: nat := 3.  (* [llcLgWay] should be >=5 for liveness *)

Definition kl1c (oidx: IdxT): Modules :=
  ((compile_Object (H0 := MesiCompLineRW l1LgWay) dtr (existT _ _ (hl1 oidx)))
     ++ mesiCache oidx 24 6 2 l1LgWay
     ++ mshrs oidx 1 1
     ++ build_int_fifos oidx
     ++ build_down_forward oidx
     ++ build_ext_fifos oidx)%kami.

Definition kl2c (oidx: IdxT): Modules :=
  ((compile_Object (H0 := MesiCompLineRW l2LgWay) dtr (existT _ _ (hli topo oidx)))
     ++ mesiCache oidx 24 6 2 l2LgWay
     ++ mshrs oidx 1 1
     ++ build_int_fifos oidx
     ++ build_broadcaster oidx)%kami.

Definition kllc (oidx: IdxT): Modules :=
  ((compile_Object (H0 := MesiCompLineRW llLgWay) dtr (existT _ _ (hli topo oidx)))
     ++ mesiCache oidx 24 6 2 llLgWay
     ++ mshrs oidx 1 1
     ++ build_int_fifos oidx
     ++ build_broadcaster oidx)%kami.

Definition kmemc (oidx: IdxT): Modules :=
  ((compile_Object (H0 := MesiCompLineRW 1) dtr (existT _ _ (hmem topo oidx)))
     ++ mesiCache oidx 20 10 2 1
     ++ mshrs oidx 1 1
     ++ build_broadcaster oidx)%kami.

Definition k: Modules :=
  ((kmemc 0)
     ++ (kllc 0~>0)
     ++ (kl2c 0~>0~>0 ++ (kl1c 0~>0~>0~>0 ++ kl1c 0~>0~>0~>1))
     ++ (kl2c 0~>0~>1 ++ (kl1c 0~>0~>1~>0 ++ kl1c 0~>0~>1~>1)))%kami.
