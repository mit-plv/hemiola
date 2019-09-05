Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport.

Require Import Ex.Spec.

Set Implicit Arguments.

(** Message Ids *)

Definition mesiRqS: IdxT := 0~>2.
Definition mesiRsS: IdxT := 0~>3.
Definition mesiRsE: IdxT := 0~>4.
Definition mesiDownRqS: IdxT := 0~>5.
Definition mesiDownRsS: IdxT := 0~>6.

Definition mesiRqM: IdxT := 1~>2.
Definition mesiRsM: IdxT := 1~>3.
Definition mesiDownRqI: IdxT := 1~>4.
Definition mesiDownRsI: IdxT := 1~>5.

Definition mesiPushRq: IdxT := 2~>2.
Definition mesiPushWRq: IdxT := 2~>3.
Definition mesiInvRq: IdxT := 2~>4.
Definition mesiInvWRq: IdxT := 2~>5.
Definition mesiInvRs: IdxT := 2~>6.

(** Cache Status *)

Notation MESI := nat (only parsing).
Definition mesiM: MESI := 4.
Definition mesiE: MESI := 3.
Definition mesiS: MESI := 2.
Definition mesiI: MESI := 1.
Definition mesiNP: MESI := 0. (* Not Present *)

