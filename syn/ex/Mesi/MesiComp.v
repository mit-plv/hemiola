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

  Instance MesiCompExtType: CompExtType :=
    {| kind_of_hetype :=
         fun het => match het with
                    | HDir => Struct KDir
                    end
    |}.

  Fixpoint compile_dir_exp
           (var: Kind -> Type) {het}
           (ul: var (Struct UL)) (dl: var (Struct DL))
           (ostvars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
           (he: heexp (hvar_of var) het): Expr var (SyntaxKind (kind_of het)) :=
    (match he in (hexp_dir _ h) return (Expr var (SyntaxKind (kind_of h))) with
     | HDirC _ => #(HVector.hvec_ith ostvars Mesi.dir)
     | HDirGetSt dir => ((compile_dir_exp ul dl ostvars dir)!KDir@."dir_st")
     | HDirGetExcl dir => ((compile_dir_exp ul dl ostvars dir)!KDir@."dir_excl")
     | HDirGetStO oidx dir => compile_dir_get (compile_bexp ostvars ul dl oidx)
                                              (compile_dir_exp ul dl ostvars dir)
     | HDirGetSh dir => ((compile_dir_exp ul dl ostvars dir)!KDir@."dir_sharers")
     | HDirRemoveSh sh cidx =>
       bvUnset (compile_dir_exp ul dl ostvars sh) (compile_bexp ostvars ul dl cidx)
     | HDirAddSharer oidx dir =>
       (let kdir := compile_dir_exp ul dl ostvars dir in
        STRUCT { "dir_st" ::= mesiS;
                 "dir_excl" ::= kdir!KDir@."dir_excl";
                 "dir_sharers" ::= bvSet (kdir!KDir@."dir_sharers")
                                         (compile_bexp ostvars ul dl oidx) })
     | HDirRemoveSharer oidx dir =>
       (let kdir := compile_dir_exp ul dl ostvars dir in
        STRUCT { "dir_st" ::= mesiS;
                 "dir_excl" ::= kdir!KDir@."dir_excl";
                 "dir_sharers" ::= bvUnset (kdir!KDir@."dir_sharers")
                                           (compile_bexp ostvars ul dl oidx) })

     | HDirSetM oidx => (STRUCT { "dir_st" ::= mesiM;
                                  "dir_excl" ::= compile_bexp ostvars ul dl oidx;
                                  "dir_sharers" ::= $$Default })
     | HDirSetE oidx => (STRUCT { "dir_st" ::= mesiE;
                                  "dir_excl" ::= compile_bexp ostvars ul dl oidx;
                                  "dir_sharers" ::= $$Default })
     | HDirSetS oinds => (STRUCT { "dir_st" ::= mesiS;
                                   "dir_excl" ::= $$Default;
                                   "dir_sharers" ::=
                                     List.fold_left
                                       (fun bv i => bvSet bv i)
                                       (map (compile_bexp ostvars ul dl) oinds)
                                       $$Default })
     | HDirSetI _ => (STRUCT { "dir_st" ::= mesiI;
                               "dir_excl" ::= $$Default;
                               "dir_sharers" ::= $$Default })

     | HRqUpFrom oidx => {$TopoTemplate.rqUpIdx, compile_dir_exp ul dl ostvars oidx}
     | HRsUpFrom oidx => {$TopoTemplate.rsUpIdx, compile_dir_exp ul dl ostvars oidx}
     | HDownTo oidx => {$TopoTemplate.downIdx, compile_dir_exp ul dl ostvars oidx}
     | HRqUpFromM oinds => compile_dir_exp ul dl ostvars oinds
     | HRsUpFromM oinds => compile_dir_exp ul dl ostvars oinds
     | HDownToM oinds => compile_dir_exp ul dl ostvars oinds
     | HSingleton se => bvSet $$Default (_truncate_ (compile_dir_exp ul dl ostvars se))
     | HInvalidate se =>
       (IF ((compile_bexp ostvars ul dl se) == mesiNP) then mesiNP else mesiI)
     end)%kami_expr.

  Definition compile_dir_OPrec
             (var: Kind -> Type)
             (ul: var (Struct UL)) (dl: var (Struct DL))
             (ostvars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
             (pd: heoprec (hvar_of var)): Expr var (SyntaxKind Bool) :=
    (match pd with
     | DirLastSharer cidx =>
       bvSingleton (#(HVector.hvec_ith ostvars Mesi.dir)!KDir@."dir_sharers")
                   (compile_bexp ostvars ul dl cidx)
     | DirNotLastSharer _ =>
       bvCount (#(HVector.hvec_ith ostvars Mesi.dir)!KDir@."dir_sharers") > $1
     | DirOtherSharerExists cidx =>
       bvUnset (#(HVector.hvec_ith ostvars Mesi.dir)!KDir@."dir_sharers")
               (compile_bexp ostvars ul dl cidx) != $0
     end)%kami_expr.

  Instance MesiCompExtExp: CompExtExp :=
    {| compile_eexp := compile_dir_exp;
       compile_eoprec := compile_dir_OPrec
    |}.

  Definition MesiInfo :=
    STRUCT { "mesi_owned" :: Bool;
             "mesi_status" :: Bit 2;
             "mesi_dir_st" :: Bit 2;
             "mesi_dir_sharers" :: Bit hcfg_children_max }.

  Definition compile_mesi_info_update
             (var: Kind -> Type) (pinfo: var (Struct MesiInfo))
             ht i (Heq: Vector.nth hostf_ty i = ht)
             (ve: Expr var (SyntaxKind (kind_of ht))): Expr var (SyntaxKind (Struct MesiInfo)).
  Proof.
    subst ht.
    generalize dependent i; intros i.
    refine (match i with | Fin.F1 => _ | Fin.FS _ => _ end).
    1: { repeat (destruct n; [exact idProp|]).
         destruct n; [|exact idProp].
         simpl; intros.
         exact (#pinfo)%kami_expr.
    }

    repeat (destruct n; [exact idProp|]); destruct n; [|exact idProp].
    refine (match t with | Fin.F1 => _ | Fin.FS _ => _ end).
    1: { repeat (destruct n; [exact idProp|]); destruct n; [|exact idProp].
         simpl; intros.
         exact (STRUCT { "mesi_owned" ::= ve;
                         "mesi_status" ::= #pinfo!MesiInfo@."mesi_status";
                         "mesi_dir_st" ::= #pinfo!MesiInfo@."mesi_dir_st";
                         "mesi_dir_sharers" ::= #pinfo!MesiInfo@."mesi_dir_sharers" })%kami_expr.
    }

    repeat (destruct n; [exact idProp|]); destruct n; [|exact idProp].
    refine (match t0 with | Fin.F1 => _ | Fin.FS _ => _ end).
    1: { repeat (destruct n; [exact idProp|]); destruct n; [|exact idProp].
         simpl; intros.
         exact (STRUCT { "mesi_owned" ::= #pinfo!MesiInfo@."mesi_owned";
                         "mesi_status" ::= UniBit (Trunc 2 _) (ve - $1);
                         "mesi_dir_st" ::= #pinfo!MesiInfo@."mesi_dir_st";
                         "mesi_dir_sharers" ::= #pinfo!MesiInfo@."mesi_dir_sharers" })%kami_expr.
    }

    repeat (destruct n; [exact idProp|]); destruct n; [|exact idProp].
    refine (match t1 with | Fin.F1 => _ | Fin.FS _ => _ end).
    1: { repeat (destruct n; [exact idProp|]); destruct n; [|exact idProp].
         simpl; intros.
         exact (STRUCT { "mesi_owned" ::= #pinfo!MesiInfo@."mesi_owned";
                         "mesi_status" ::= #pinfo!MesiInfo@."mesi_status";
                         "mesi_dir_st" ::= UniBit (Trunc 2 _) (ve!KDir@."dir_st" - $1);
                         "mesi_dir_sharers" ::= ve!KDir@."dir_sharers" })%kami_expr.
    }

    repeat (destruct n; [exact idProp|]); destruct n; [|exact idProp].
    apply Fin.case0; assumption.
  Defined.

  Definition compile_mesi_ost_to_value
             (var: Kind -> Type) ht (Heq: Vector.nth hostf_ty Mesi.val = ht)
             (ve: Expr var (SyntaxKind (kind_of ht))): Expr var (SyntaxKind (Bit hcfg_value_sz)).
  Proof.
    subst ht; exact ve.
  Defined.

  Instance MesiCacheInfo: CacheInfo :=
    {| info_kind := Struct MesiInfo;
       comp_info_to_ostVars :=
         fun var pinfo cont =>
           (LET value <- $$Default; (* don't care *)
           LET owned <- #pinfo!MesiInfo@."mesi_owned";
           LET status: KMesi <- ({$0, #pinfo!MesiInfo@."mesi_status"} + $1);
           LET dir <- STRUCT { "dir_st" ::= {$0, #pinfo!MesiInfo@."mesi_dir_st"} + $1;
                               "dir_excl" ::= bvFirstSet (#pinfo!MesiInfo@."mesi_dir_sharers");
                               "dir_sharers" ::= #pinfo!MesiInfo@."mesi_dir_sharers" };
           cont (value, (owned, (status, (dir, tt)))))%kami_action;
       comp_info_update := compile_mesi_info_update;
       value_ost_idx := Mesi.val;
       value_ost_to_value := compile_mesi_ost_to_value |}.

End Instances.

Existing Instance MesiCompExtType.
Existing Instance MesiCompExtExp.
Existing Instance MesiCacheInfo.

Require Import Hemiola.Ex.TopoTemplate.

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

(* Time Definition k: Modules := *)
(*   Eval vm_compute in (compile_System (existT _ _ (@himpl topo ltac:(discriminate)))). *)

Definition kl1c (oidx: IdxT): Modules :=
  ((compile_Object dtr (existT _ _ (hl1 oidx)))
     ++ mshrs oidx 1 1
     ++ build_int_fifos oidx
     ++ build_down_forward oidx
     ++ build_ext_fifos oidx)%kami.

Definition klic (oidx: IdxT): Modules :=
  ((compile_Object dtr (existT _ _ (hli topo oidx)))
     ++ mshrs oidx 1 1
     ++ build_int_fifos oidx
     ++ build_broadcaster oidx)%kami.

Definition kmemc (oidx: IdxT): Modules :=
  ((compile_Object dtr (existT _ _ (hmem topo oidx)))
     ++ mshrs oidx 1 1
     ++ build_broadcaster oidx)%kami.

(* Time Definition kl1c0: Modules := *)
(*   Eval vm_compute in (kl1c 0~>0~>0). *)

(* Eval compute in (tree2Topo topo 0). *)
Time Definition k: Modules :=
  Eval vm_compute in
    ((kmemc 0)
       ++ (klic 0~>0)
       ++ (klic 0~>0~>0 ++ (kl1c 0~>0~>0~>0 ++ kl1c 0~>0~>0~>1))
       ++ (klic 0~>0~>1 ++ (kl1c 0~>0~>1~>0 ++ kl1c 0~>0~>1~>1)))%kami.

(* Time Definition k: Modules := *)
(*   Eval vm_compute in *)
(*     (kmemc ++ (kl1c 0~>0 ++ kl1c 0~>1))%kami. *)
