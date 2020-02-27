Require Import Hemiola.Common Hemiola.Syntax HemiolaDeep.

Require Import Kami.

Set Implicit Arguments.

Import MonadNotations.
Module H := Hemiola.Syntax.
Module K := Kami.Syntax.

Section I.
  Context `{DecValue} `{oifc: OStateIfc}.

  Definition compile_OState_init: list K.RegInitT :=
    nil. (** TODO *)

  Definition compile_Rule (rule: {sr: H.Rule & HRule sr}):
    Struct.Attribute (K.Action K.Void) :=
    cheat _. (** TODO *)
  
  Definition compile_Rules (rules: list {sr: H.Rule & HRule sr}):
    list (Struct.Attribute (K.Action K.Void)) :=
    map compile_Rule rules.
  
  Definition compile_Object (obj: HObject): option K.Modules :=
    let cregs := compile_OState_init in
    let crules := compile_Rules (hobj_rules obj) in
    Some (K.Mod cregs crules nil).
  
  Fixpoint compile_Objects (objs: list HObject): option Kami.Syntax.Modules :=
    match objs with
    | nil => None
    | obj :: objs' =>
      (cmod <-- compile_Object obj;
      cmods <-- compile_Objects objs';
      Some (ConcatMod cmod cmods))
    end.
  
  Definition compile_System (sys: HSystem): option Kami.Syntax.Modules :=
    compile_Objects sys.(hsys_objs).

End I.

