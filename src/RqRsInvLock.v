Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvMsg.

Require Export RqRsInvUpLock RqRsInvDownLock.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Ltac good_locking_get obj :=
  match goal with
  | [Hlock: UpLockInv _ ?sys _, Ho: In obj (sys_objs ?sys) |- _] =>
    let H := fresh "H" in
    pose proof Hlock as H;
    specialize (H (obj_idx obj)); simpl in H;
    specialize (H (in_map _ _ _ Ho)); dest
  | [Hlock: DownLockInv _ ?sys _, Ho: In obj (sys_objs ?sys) |- _] =>
    let H := fresh "H" in
    pose proof Hlock as H;
    specialize (H (obj_idx obj)); simpl in H;
    specialize (H (in_map _ _ _ Ho)); dest
  end.

Ltac disc_lock_conds :=
  match goal with
  | [H: OLockedTo _ _ _ |- _] => red in H
  | [H: UpLockInvORq _ _ _ _ _ |- _] => red in H; mred; simpl in H; mred
  | [H: UpLockedInv _ _ _ _ |- _] =>
    let rqUp := fresh "rqUp" in
    let down := fresh "down" in
    let pidx := fresh "pidx" in
    destruct H as [rqUp [down [pidx ?]]]; dest
  end.

Close Scope list.
Close Scope fmap.
