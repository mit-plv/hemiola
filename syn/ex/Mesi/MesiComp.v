Require Import String.

Require Import Kami.Kami.
Require Import Compiler.Compiler.
Require Import MesiDeep.

Set Implicit Arguments.

Section Tests.

  Definition oidx: IdxT := 1.
  Definition uln: string := "UpLock". 
  Definition dln: string := "DownLock".
  Definition ostin: string := "ost".

  Definition KMesi: Kind := Bit 3.
  Definition KDir :=
    STRUCT { "dir_st" :: KMesi;
             "dir_excl" :: KIdxQ;
             "dir_sharers" :: Array KIdxQ (Nat.pow 2 hcfg_children_max_lg) }.

  Instance MesiCompExtType: CompExtType :=
    {| kind_of_hetype :=
         fun het => match het with
                    | HDir => Struct KDir
                    end
    |}.

  Instance MesiCompExtExp: CompExtExp :=
    {| compile_eexp :=
         fun var het ostVars he =>
           match he in (hexp_dir _ h) return (kind_of h) @ (var) with
           | HDirC _ =>
             #(HVector.hvec_ith ostVars (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
           | _ => TODO _
           end%kami_expr
    |}.

  (* Opaque icons'. *)
  Existing Instance MesiHOStateIfcFull.

End Tests.
