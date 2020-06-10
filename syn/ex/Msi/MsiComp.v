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
  Context `{hconfig}.

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

Existing Instance MsiHOStateIfcFull.

Section DirComp.

  Instance MsiCompExtType: CompExtType :=
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
     | HDirC _ => #(HVector.hvec_ith ostvars Msi.dir)
     | HDirGetSt dir => ((compile_dir_exp ul dl ostvars dir)!KDir@."dir_st")
     | HDirGetExcl dir => ((compile_dir_exp ul dl ostvars dir)!KDir@."dir_excl")
     | HDirGetStO oidx dir => compile_dir_get (compile_bexp ul dl ostvars oidx)
                                              (compile_dir_exp ul dl ostvars dir)
     | HDirGetSh dir => ((compile_dir_exp ul dl ostvars dir)!KDir@."dir_sharers")
     | HDirRemoveSh sh cidx =>
       bvUnset (compile_dir_exp ul dl ostvars sh) (compile_bexp ul dl ostvars cidx)
     | HDirAddSharer oidx dir =>
       (let kdir := compile_dir_exp ul dl ostvars dir in
        STRUCT { "dir_st" ::= msiS;
                 "dir_excl" ::= kdir!KDir@."dir_excl";
                 "dir_sharers" ::= bvSet (kdir!KDir@."dir_sharers")
                                         (compile_bexp ul dl ostvars oidx) })
     | HDirRemoveSharer oidx dir =>
       (let kdir := compile_dir_exp ul dl ostvars dir in
        STRUCT { "dir_st" ::= msiS;
                 "dir_excl" ::= kdir!KDir@."dir_excl";
                 "dir_sharers" ::= bvUnset (kdir!KDir@."dir_sharers")
                                           (compile_bexp ul dl ostvars oidx) })

     | HDirSetM oidx => (STRUCT { "dir_st" ::= msiM;
                                  "dir_excl" ::= compile_bexp ul dl ostvars oidx;
                                  "dir_sharers" ::= $$Default })
     | HDirSetS oinds => (STRUCT { "dir_st" ::= msiS;
                                   "dir_excl" ::= $$Default;
                                   "dir_sharers" ::=
                                     List.fold_left
                                       (fun bv i => bvSet bv i)
                                       (map (compile_bexp ul dl ostvars) oinds)
                                       $$Default })
     | HDirSetI _ => (STRUCT { "dir_st" ::= msiI;
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
       (IF ((compile_bexp ul dl ostvars se) == msiNP) then msiNP else msiI)
     end)%kami_expr.

  Definition compile_dir_OPrec
             (var: Kind -> Type)
             (ul: var (Struct UL)) (dl: var (Struct DL))
             (ostvars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
             (pd: heoprec (hvar_of var)): Expr var (SyntaxKind Bool) :=
    (match pd with
     | DirLastSharer cidx =>
       bvIsSingleton (#(HVector.hvec_ith ostvars Msi.dir)!KDir@."dir_sharers")
                     (compile_bexp ul dl ostvars cidx)
     | DirNotLastSharer _ =>
       bvCount (#(HVector.hvec_ith ostvars Msi.dir)!KDir@."dir_sharers") > $1
     | DirOtherSharerExists cidx =>
       bvUnset (#(HVector.hvec_ith ostvars Msi.dir)!KDir@."dir_sharers")
               (compile_bexp ul dl ostvars cidx) != $0
     end)%kami_expr.

  Instance MsiCompExtExp: CompExtExp :=
    {| compile_eexp := compile_dir_exp;
       compile_eoprec := compile_dir_OPrec
    |}.

End DirComp.

Existing Instance MsiCompExtType.
Existing Instance MsiCompExtExp.

Require Import Hemiola.Ex.TopoTemplate.
(** TODO: instantiate a protocol (cf. ../Mesi/MesiComp.v *)
