Require Import String List.
Import ListNotations.

Require Import Kami.Kami.
Require Import Compiler.Compiler.
Require Import MesiDeep.

Set Implicit Arguments.

Section Directory.
  Context `{hconfig}.
  
  Definition KMesi: Kind := Bit 3.
  Definition mesiM {var}: Expr var (SyntaxKind KMesi) := ($3)%kami_expr.
  Definition mesiE {var}: Expr var (SyntaxKind KMesi) := ($2)%kami_expr.
  Definition mesiS {var}: Expr var (SyntaxKind KMesi) := ($1)%kami_expr.
  Definition mesiI {var}: Expr var (SyntaxKind KMesi) := ($0)%kami_expr.

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

Section DirComp.

  Instance MesiCompExtType: CompExtType :=
    {| kind_of_hetype :=
         fun het => match het with
                    | HDir => Struct KDir
                    end
    |}.

  Fixpoint compile_dir_exp
           (var: Kind -> Type) {het}
           (ostvars: HVector.hvec (Vector.map (fun hty => var (kind_of hty)) hostf_ty))
           (he: heexp (hvar_of var) het): Expr var (SyntaxKind (kind_of het)) :=
    (match he in (hexp_dir _ h) return (Expr var (SyntaxKind (kind_of h))) with
     | HDirC _ => #(HVector.hvec_ith ostvars (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
     | HDirGetSt dir => ((compile_dir_exp ostvars dir)!KDir@."dir_st")
     | HDirGetExcl dir => ((compile_dir_exp ostvars dir)!KDir@."dir_excl")
     | HDirGetStO oidx dir => compile_dir_get (compile_bexp ostvars oidx)
                                              (compile_dir_exp ostvars dir)
     | HDirGetSh dir => ((compile_dir_exp ostvars dir)!KDir@."dir_sharers")
     | HDirAddSharer oidx dir =>
       (let kdir := compile_dir_exp ostvars dir in
        STRUCT { "dir_st" ::= mesiS;
                 "dir_excl" ::= kdir!KDir@."dir_excl";
                 "dir_sharers" ::= bvSet (kdir!KDir@."dir_sharers")
                                         (compile_bexp ostvars oidx) })
     | HDirRemoveSharer oidx dir =>
       (let kdir := compile_dir_exp ostvars dir in
        STRUCT { "dir_st" ::= mesiS;
                 "dir_excl" ::= kdir!KDir@."dir_excl";
                 "dir_sharers" ::= bvUnset (kdir!KDir@."dir_sharers")
                                           (compile_bexp ostvars oidx) })

     | HDirSetM oidx => (STRUCT { "dir_st" ::= mesiM;
                                  "dir_excl" ::= compile_bexp ostvars oidx;
                                  "dir_sharers" ::= $$Default })
     | HDirSetE oidx => (STRUCT { "dir_st" ::= mesiE;
                                  "dir_excl" ::= compile_bexp ostvars oidx;
                                  "dir_sharers" ::= $$Default })
     | HDirSetS oinds => (STRUCT { "dir_st" ::= mesiS;
                                   "dir_excl" ::= $$Default;
                                   "dir_sharers" ::=
                                     List.fold_left
                                       (fun bv i => bvSet bv i)
                                       (map (compile_bexp ostvars) oinds)
                                       $$Default })
     | HDirSetI _ => (STRUCT { "dir_st" ::= mesiI;
                               "dir_excl" ::= $$Default;
                               "dir_sharers" ::= $$Default })

     | HRqUpFrom oidx => compile_dir_exp ostvars oidx
     | HRsUpFrom oidx => compile_dir_exp ostvars oidx
     | HDownTo oidx => compile_dir_exp ostvars oidx
     | HRqUpFromM oinds => compile_dir_exp ostvars oinds
     | HRsUpFromM oinds => compile_dir_exp ostvars oinds
     | HDownToM oinds => compile_dir_exp ostvars oinds
     | HSingleton se => bvSet $$Default (compile_dir_exp ostvars se)
     end)%kami_expr.

  Instance MesiCompExtExp: CompExtExp :=
    {| compile_eexp := compile_dir_exp |}.

End DirComp.

Existing Instance MesiHOStateIfcFull.
Existing Instance MesiCompExtType.
Existing Instance MesiCompExtExp.

Require Import Hemiola.Ex.TopoTemplate.

Local Definition oidx: IdxT := 0~>1~>2.

Definition kl1: Modules :=
  Eval vm_compute in (compile_Object (existT _ _ (hl1 oidx))).

Definition kl1c: Modules :=
  Eval vm_compute in
    (kl1 ++ build_int_fifos oidx ++ build_down_forward oidx ++ build_ext_fifos oidx)%kami.

(* Definition topo: tree := *)
(*   Node [Node [Node nil; Node nil]; Node [Node nil; Node nil]]. *)

(* Definition okli := *)
(*   Eval vm_compute in (compile_Object (existT _ _ (hli topo oidx))). *)

(* Definition kli: Modules := *)
(*   Eval simpl in (match okli with *)
(*                  | Some m => m *)
(*                  | None => Mod nil nil nil *)
(*                  end). *)

(* Definition okmem := *)
(*   Eval vm_compute in (compile_Object (existT _ _ (hmem topo oidx))). *)

(* Definition kmem: Modules := *)
(*   Eval simpl in (match okmem with *)
(*                  | Some m => m *)
(*                  | None => Mod nil nil nil *)
(*                  end). *)

(* Time Definition ok: option Modules := *)
(*   Eval vm_compute in (compile_System (existT _ _ (@himpl topo ltac:(discriminate)))). *)

(* Time Definition k: Modules := *)
(*   Eval simpl in (match ok with *)
(*                  | Some m => m *)
(*                  | None => Mod nil nil nil *)
(*                  end). *)

