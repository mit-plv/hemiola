Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport.

Require Import Ex.Spec.

Set Implicit Arguments.

(** Message Ids *)

Definition msiRqS: IdxT := 0~>2.
Definition msiRsS: IdxT := 0~>3.
Definition msiDownRqS: IdxT := 0~>5.
Definition msiDownRsS: IdxT := 0~>6.

Definition msiRqM: IdxT := 1~>2.
Definition msiRsM: IdxT := 1~>3.
Definition msiDownRqI: IdxT := 1~>4.
Definition msiDownRsI: IdxT := 1~>5.

Definition msiInvRq: IdxT := 2~>4.
Definition msiInvWRq: IdxT := 2~>5.
Definition msiInvRs: IdxT := 2~>6.

(** Cache Status *)

Notation MSI := nat (only parsing).
Definition msiM: MSI := 3.
Definition msiS: MSI := 2.
Definition msiI: MSI := 1.
Definition msiNP: MSI := 0. (* Not Present *)

