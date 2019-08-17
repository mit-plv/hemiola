Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector IndexSupport.

Set Implicit Arguments.

(** Message Ids *)

Definition getRq: IdxT := 0~>0.
Definition getRs: IdxT := 0~>1.
Definition setRq: IdxT := 1~>0.
Definition setRs: IdxT := 1~>1.
Definition evictRq: IdxT := 2~>0.
Definition evictRs: IdxT := 2~>1.

