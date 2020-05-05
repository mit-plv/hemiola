Require Import String List.
Import ListNotations.

Require Import Kami.Kami.
Require Import Compiler.Compiler.
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

Section DirComp.

  Instance MesiCompExtType: CompExtType :=
    {| kind_of_hetype :=
         fun het => match het with
                    | HDir => Struct KDir
                    end
    |}.

  Fixpoint compile_dir_exp
           (var: Kind -> Type) {het}
           (ul: var (Struct UpLock)) (dl: var (Struct DownLock))
           (ostvars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
           (he: heexp (hvar_of var) het): Expr var (SyntaxKind (kind_of het)) :=
    (match he in (hexp_dir _ h) return (Expr var (SyntaxKind (kind_of h))) with
     | HDirC _ => #(HVector.hvec_ith ostvars Mesi.dir)
     | HDirGetSt dir => ((compile_dir_exp ul dl ostvars dir)!KDir@."dir_st")
     | HDirGetExcl dir => ((compile_dir_exp ul dl ostvars dir)!KDir@."dir_excl")
     | HDirGetStO oidx dir => compile_dir_get (compile_bexp ul dl ostvars oidx)
                                              (compile_dir_exp ul dl ostvars dir)
     | HDirGetSh dir => ((compile_dir_exp ul dl ostvars dir)!KDir@."dir_sharers")
     | HDirRemoveSh sh cidx =>
       bvUnset (compile_dir_exp ul dl ostvars sh) (compile_bexp ul dl ostvars cidx)
     | HDirAddSharer oidx dir =>
       (let kdir := compile_dir_exp ul dl ostvars dir in
        STRUCT { "dir_st" ::= mesiS;
                 "dir_excl" ::= kdir!KDir@."dir_excl";
                 "dir_sharers" ::= bvSet (kdir!KDir@."dir_sharers")
                                         (compile_bexp ul dl ostvars oidx) })
     | HDirRemoveSharer oidx dir =>
       (let kdir := compile_dir_exp ul dl ostvars dir in
        STRUCT { "dir_st" ::= mesiS;
                 "dir_excl" ::= kdir!KDir@."dir_excl";
                 "dir_sharers" ::= bvUnset (kdir!KDir@."dir_sharers")
                                           (compile_bexp ul dl ostvars oidx) })

     | HDirSetM oidx => (STRUCT { "dir_st" ::= mesiM;
                                  "dir_excl" ::= compile_bexp ul dl ostvars oidx;
                                  "dir_sharers" ::= $$Default })
     | HDirSetE oidx => (STRUCT { "dir_st" ::= mesiE;
                                  "dir_excl" ::= compile_bexp ul dl ostvars oidx;
                                  "dir_sharers" ::= $$Default })
     | HDirSetS oinds => (STRUCT { "dir_st" ::= mesiS;
                                   "dir_excl" ::= $$Default;
                                   "dir_sharers" ::=
                                     List.fold_left
                                       (fun bv i => bvSet bv i)
                                       (map (compile_bexp ul dl ostvars) oinds)
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
       (IF ((compile_bexp ul dl ostvars se) == mesiNP) then mesiNP else mesiI)
     end)%kami_expr.

  Definition compile_dir_OPrec
             (var: Kind -> Type)
             (ul: var (Struct UpLock)) (dl: var (Struct DownLock))
             (ostvars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
             (pd: heoprec (hvar_of var)): Expr var (SyntaxKind Bool) :=
    (match pd with
     | DirLastSharer cidx =>
       bvSingleton (#(HVector.hvec_ith ostvars Mesi.dir)!KDir@."dir_sharers")
                   (compile_bexp ul dl ostvars cidx)
     | DirNotLastSharer _ =>
       bvCount (#(HVector.hvec_ith ostvars Mesi.dir)!KDir@."dir_sharers") > $1
     | DirOtherSharerExists cidx =>
       bvUnset (#(HVector.hvec_ith ostvars Mesi.dir)!KDir@."dir_sharers")
               (compile_bexp ul dl ostvars cidx) != $0
     end)%kami_expr.

  Instance MesiCompExtExp: CompExtExp :=
    {| compile_eexp := compile_dir_exp;
       compile_eoprec := compile_dir_OPrec
    |}.

End DirComp.

Existing Instance MesiCompExtType.
Existing Instance MesiCompExtExp.

Require Import Hemiola.Ex.TopoTemplate.

Definition topo: tree :=
  Node [Node [Node nil; Node nil]; Node [Node nil; Node nil]].

(* Time Definition k: Modules := *)
(*   Eval vm_compute in (compile_System (existT _ _ (@himpl topo ltac:(discriminate)))). *)

Definition kl1c (oidx: IdxT): Modules :=
  ((compile_Object (existT _ _ (hl1 oidx)))
     ++ build_int_fifos oidx
     ++ build_down_forward oidx
     ++ build_ext_fifos oidx)%kami.

Definition klic (oidx: IdxT): Modules :=
  ((compile_Object (existT _ _ (hli topo oidx)))
     ++ build_int_fifos oidx
     ++ build_broadcaster oidx)%kami.

Definition kmemc :=
  (compile_Object (existT _ _ (hmem topo [0]%list)) ++ build_broadcaster [0]%list)%kami.

(* Time Definition kl1c0: Modules := *)
(*   Eval vm_compute in (kl1c 0~>0~>0). *)

(* Eval compute in (tree2Topo topo 0). *)
Time Definition k: Modules :=
  Eval vm_compute in
    (kmemc ++ (klic 0~>0 ++ (kl1c 0~>0~>0 ++ kl1c 0~>0~>1))
           ++ (klic 0~>1 ++ (kl1c 0~>1~>0 ++ kl1c 0~>1~>1)))%kami.

(* Time Definition k: Modules := *)
(*   Eval vm_compute in *)
(*     (kmemc ++ (kl1c 0~>0 ++ kl1c 0~>1))%kami. *)
