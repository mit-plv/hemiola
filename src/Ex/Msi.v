Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport.

Require Import Ex.Spec.

Set Implicit Arguments.

(** Message Ids *)

Definition msiRqS: IdxT := specNumMsgIds + 0.
Definition msiRsS: IdxT := specNumMsgIds + 1.
Definition msiDownRqS: IdxT := specNumMsgIds + 2.
Definition msiDownRsS: IdxT := specNumMsgIds + 3.

Definition msiRqM: IdxT := specNumMsgIds + 4.
Definition msiRsM: IdxT := specNumMsgIds + 5.
Definition msiDownRqI: IdxT := specNumMsgIds + 6.
Definition msiDownRsI: IdxT := specNumMsgIds + 7.

Definition msiRqI: IdxT := specNumMsgIds + 8.
Definition msiRsI: IdxT := specNumMsgIds + 9.

(** Cache Status *)

Notation MSI := nat (only parsing).
Definition msiM: MSI := 2.
Definition msiS: MSI := 1.
Definition msiI: MSI := 0.

