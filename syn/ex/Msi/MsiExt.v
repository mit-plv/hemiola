Require Import Kami.Kami.
Require Import Kami.Ext.Extraction.

Require Import MsiComp.

Definition targetM: Kami.Syntax.Modules := k.
Definition targetS := getModuleS targetM.
Definition targetB := ModulesSToBModules targetS.

Time Extraction "./Target.ml" targetB.

