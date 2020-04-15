(** TODO: better to have a file in Kami that "exports" such modules *)
Require Import Kami.Synthesize.
Require Import Kami.Ext.BSyntax.
Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
Extraction Language OCaml.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

Require Import MesiComp.

Definition targetM: Kami.Syntax.Modules := k.
Definition targetS := getModuleS targetM.
Definition targetB := ModulesSToBModules targetS.

(* Time Extraction "./Target.ml" targetB. *)

