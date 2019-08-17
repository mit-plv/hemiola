Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector IndexSupport.

Require Import Ex.Spec.

Set Implicit Arguments.

(** Message Ids *)

Definition msiRqS: IdxT := 0~>2.
Definition msiRsS: IdxT := 0~>3.
Definition msiDownRqS: IdxT := 0~>4.
Definition msiDownRsS: IdxT := 0~>5.

Definition msiRqM: IdxT := 1~>2.
Definition msiRsM: IdxT := 1~>3.
Definition msiDownRqI: IdxT := 1~>4.
Definition msiDownRsI: IdxT := 1~>5.

Definition msiRqI: IdxT := 2~>2.
Definition msiRsI: IdxT := 2~>3.

(** Cache Status *)

Notation MSI := nat (only parsing).
Definition msiM: MSI := 2.
Definition msiS: MSI := 1.
Definition msiI: MSI := 0.

