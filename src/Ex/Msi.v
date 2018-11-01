Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

(** Message Ids *)

Definition msiGetRq: IdxT := 0.
Definition msiGetRs: IdxT := 1.
Definition msiRqS: IdxT := 2.
Definition msiRsS: IdxT := 3.
Definition msiDownRqS: IdxT := 4.
Definition msiDownRsS: IdxT := 5.

Definition msiSetRq: IdxT := 6.
Definition msiSetRs: IdxT := 7.
Definition msiRqM: IdxT := 8.
Definition msiRsM: IdxT := 9.
Definition msiDownRqM: IdxT := 10.
Definition msiDownRsM: IdxT := 11.

Definition msiEvictRq: IdxT := 12.
Definition msiEvictRs: IdxT := 13.
Definition msiRqI: IdxT := 14.
Definition msiRsI: IdxT := 15.

(** Cache Status *)

Definition msiM := 2.
Definition msiS := 1.
Definition msiI := 0.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

