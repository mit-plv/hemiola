Require Import String List.
Import ListNotations.

Require Import Hemiola.Index Hemiola.Ex.TopoTemplate.
Require Import Kami.Kami.
Require Import Kami.Ext.Extraction.

Require Import Compiler.HemiolaDeep Compiler.Components Compiler.CompileK.
Require Import MesiDeep MesiComp.

Existing Instance MesiHOStateIfcFull.
Instance MesiTopoConfig: TopoConfig :=
  {| hcfg_value_sz := 64;
     hcfg_line_values_lg := 2; (* 32B line *)
     hcfg_children_max_pred := 3 (* max(#children) = 4 *) |}.
Existing Instance MesiCompExtType.
Existing Instance MesiCompExtExp.

(***************
 *     Mem     *
 *      |      *
 * --LLC(L2)-- *
 * |  |   |  | *
 * L1 L1 L1 L1 *
 ***************)
Definition topo: tree :=
  Node [Node [Node nil; Node nil; Node nil; Node nil]].
Definition dtr := fst (tree2Topo topo 0).

(** Cache size: 2^(IndexSz) * 2^(LgWay) * (LineSz = 32B) *)
(* 32KB L1: 2^8 * 2^2 * 32B *)
Definition l1IndexSz: nat := 8.
Definition l1LgWay: nat := 2.
Definition l1LgULs: nat := 2.
Definition l1LgDLs: nat := 1.
Definition l1LgNumVictim: nat := l1LgULs.
Definition l1Cache oidx := mesiCache oidx l1IndexSz l1LgWay l1LgNumVictim.
Definition l1Mshrs oidx := mshrs oidx l1LgULs l1LgDLs.

(* 512KB LL: 2^10 * 2^4 * 32B *)
Definition llIndexSz: nat := 10.
Definition llLgWay: nat := 4.
Definition llLgULs: nat := 2.
Definition llLgDLs: nat := 2.
Definition llLgNumVictim: nat := llLgULs.
Definition llCache oidx := mesiCache oidx llIndexSz llLgWay llLgNumVictim.
Definition llMshrs oidx := mshrs oidx llLgULs llLgDLs.

Definition kl1c (oidx: IdxT): Modules :=
  ((compile_Object (H0 := MesiCompLineRW l1LgWay) dtr (existT _ _ (hl1 oidx)))
     ++ l1Cache oidx ++ l1Mshrs oidx
     ++ build_msg_outs_l1 oidx
     ++ build_int_fifos oidx
     ++ build_ext_fifos oidx)%kami.

Definition kllc (oidx: IdxT): Modules :=
  ((compile_Object (H0 := MesiCompLineRW llLgWay) dtr (existT _ _ (hli topo oidx)))
     ++ llCache oidx ++ llMshrs oidx
     ++ build_msg_outs_li oidx)%kami.
(* ++ build_int_fifos oidx)%kami. *)

Definition kmemc (oidx: IdxT): Modules :=
  ((compile_Object (H0 := MesiCompLineRW 1) dtr (existT _ _ (hmem topo oidx)))
     ++ mesiCache oidx 10 1 1 ++ mshrs oidx 1 1
     ++ build_msg_outs_mem oidx)%kami.

Definition k: Modules :=
  (* ((kmemc 0) ++ *)
  ((kllc 0~>0)
     ++ (kl1c 0~>0~>0 ++ kl1c 0~>0~>1 ++ kl1c 0~>0~>2 ++ kl1c 0~>0~>3))%kami.

(** Extraction of a compiled Kami design *)

Definition targetM: Kami.Syntax.Modules := k.
Definition targetS := getModuleS targetM.
Definition targetB := ModulesSToBModules targetS.

Time Extraction "./Target.ml" targetB.
