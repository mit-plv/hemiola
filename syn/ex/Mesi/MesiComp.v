Require Import String.

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

End Directory.

Section Tests.

  Definition oidx: IdxT := 1.
  Definition uln: string := "UpLock". 
  Definition dln: string := "DownLock".
  Definition ostin: string := "ost".

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
     | HDirGetStO oidx dir => TODO _
     | HDirGetSh dir => ((compile_dir_exp ostvars dir)!KDir@."dir_sharers")
     | HDirAddSharer oidx dir => TODO _
     | HDirRemoveSharer oidx dir => TODO _
     | HDirSetM oidx => (STRUCT { "dir_st" ::= mesiM;
                                  "dir_excl" ::= compile_bexp ostvars oidx;
                                  "dir_sharers" ::= $$Default })
     | HDirSetE oidx => (STRUCT { "dir_st" ::= mesiE;
                                  "dir_excl" ::= compile_bexp ostvars oidx;
                                  "dir_sharers" ::= $$Default })
     | HDirSetS oinds => TODO _
     | HDirSetI _ => (STRUCT { "dir_st" ::= mesiI;
                               "dir_excl" ::= $$Default;
                               "dir_sharers" ::= $$Default })
     | HRqUpFrom oidx => TODO _
     | HRsUpFrom oidx => TODO _
     | HDownTo oidx => TODO _
     | HRqUpFromM oinds => TODO _
     | HRsUpFromM oinds => TODO _
     | HDownToM oinds => TODO _
     | HSingleton se => TODO _
     end)%kami_expr.

  Instance MesiCompExtExp: CompExtExp :=
    {| compile_eexp := compile_dir_exp |}.

  (* Opaque icons'. *)
  Existing Instance MesiHOStateIfcFull.

  Definition hrule: HRule (Mesi.l1InvRqUpUp oidx).
  Proof.
    ⇑rule.
  Defined.
  Definition crule :=
    Eval vm_compute in (compile_Rule oidx uln dln ostin (existT _ _ hrule)).
  
  Definition okl1 :=
    Eval vm_compute in (compile_Object (existT _ _ (hl1 oidx))).
  Definition kl1: Modules :=
    Eval simpl in (match okl1 with
                   | Some m => m
                   | None => Mod nil nil nil
                   end).

End Tests.
