Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector ListSupport.

Require Import Ex.Spec.

Set Implicit Arguments.

(** Message Ids *)

Definition mosiRqS: IdxT := 0~>0.
Definition mosiRsS: IdxT := 0~>1.
Definition mosiDownRqS: IdxT := 0~>3.
Definition mosiDownRsS: IdxT := 0~>4.

Local Definition mosiRqS_getRq_eq: mosiRqS = getRq := eq_refl.
Local Definition mosiRsS_getRs_eq: mosiRsS = getRs := eq_refl.

Definition mosiRqM: IdxT := 1~>0.
Definition mosiRsM: IdxT := 1~>1.
Definition mosiDownRqI: IdxT := 1~>2.
Definition mosiDownRsI: IdxT := 1~>3.

Local Definition mosiRqM_setRq_eq: mosiRqM = setRq := eq_refl.
Local Definition mosiRsM_setRs_eq: mosiRsM = setRs := eq_refl.

Definition mosiRqI: IdxT := 2~>0.
Definition mosiRsI: IdxT := 2~>1.

Local Definition mosiRqI_evictRq_eq: mosiRqI = evictRq := eq_refl.
Local Definition mosiRsI_evictRs_eq: mosiRsI = evictRs := eq_refl.

(** Cache Status *)

Notation MOSI := nat (only parsing).
Definition mosiM: MOSI := 3.
Definition mosiO: MOSI := 2.
Definition mosiS: MOSI := 1.
Definition mosiI: MOSI := 0.

