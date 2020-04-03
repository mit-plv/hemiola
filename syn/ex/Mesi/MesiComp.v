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

  Context `{cet: @CompExtType DirExtType}
          `{@CompExtExp SpecInds.NatDecValue
                        Mesi.ImplOStateIfc
                        MesiHConfig
                        DirExtType
                        DirExtExp
                        cet}.

  Existing Instance MesiHOStateIfcFull.
  Definition cl1GetSImm := compile_Rule oidx uln dln ostin (existT _ _ (hl1GetSImm oidx)).
  Goal True.
    pose cl1GetSImm as r.
    compute in r.
  Abort.

End Tests.
