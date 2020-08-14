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
Definition l1NumPRqs: nat := 2.
Definition l1NumCRqs: nat := 4.
Definition l1PredNumVictim: nat := Nat.pred l1NumCRqs.
Definition l1MshrSlotSz: nat := S (Nat.log2 (l1NumPRqs + l1NumCRqs - 1)).
Definition l1Cache (oidx: IdxT): Modules :=
  mesiL1 oidx l1IndexSz l1LgWay l1PredNumVictim l1MshrSlotSz.
Definition l1Mshrs (oidx: IdxT): Modules := mshrs oidx l1NumPRqs l1NumCRqs.

(* 512KB LL: 2^10 * 2^4 * 32B *)
Definition llIndexSz: nat := 10.
Definition llLgWay: nat := 4.
Definition llEDirLgWay: nat := 3.
Definition llNumPRqs: nat := 16.
Definition llNumCRqs: nat := 0.
Definition llPredNumVictim: nat := Nat.pred llNumCRqs.
Definition llMshrSlotSz: nat := S (Nat.log2 (llNumPRqs + llNumCRqs - 1)).
Definition llCache (oidx: IdxT): Modules :=
  mesiLi oidx llIndexSz llLgWay llEDirLgWay llPredNumVictim llMshrSlotSz.
Definition llMshrs (oidx: IdxT): Modules := mshrs oidx llNumPRqs llNumCRqs.

Definition kl1c (oidx: IdxT): Modules :=
  ((build_controller_l1
      (H2 := MesiCompLineRW l1LgWay 0) (mshrNumPRqs := l1NumPRqs) (mshrNumCRqs := l1NumCRqs)
      l1IndexSz l1PredNumVictim (existT _ _ (hl1 oidx)))
     ++ l1Cache oidx ++ l1Mshrs oidx)%kami.

Definition kllc (oidx: IdxT): Modules :=
  ((build_controller_li_2
      (H2 := MesiCompLineRW llLgWay 0) (mshrNumPRqs := llNumPRqs) (mshrNumCRqs := llNumCRqs)
      llIndexSz llPredNumVictim (existT _ _ (hli topo oidx)))
     ++ llCache oidx ++ llMshrs oidx)%kami.

Definition k: Modules :=
  ((kllc 0~>0)
     ++ (kl1c 0~>0~>0 ++ kl1c 0~>0~>1 ++ kl1c 0~>0~>2 ++ kl1c 0~>0~>3))%kami.

(** Extraction of a compiled Kami design *)

Definition targetM: Kami.Syntax.Modules := k.
Definition targetS := getModuleS targetM.
Definition targetB := ModulesSToBModules targetS.

Time Extraction "./Target.ml" targetB.
