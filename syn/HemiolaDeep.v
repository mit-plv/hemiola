Require Import Hemiola.Common Hemiola.Index Hemiola.HVector Hemiola.Syntax.
Require Import Hemiola.RqRsLangEx.
        
Set Implicit Arguments.

Section Reify.
  Context `{DecValue} `{oifc: OStateIfc}.

  Inductive HValue: forall {ty}, ty -> Type :=
  | HConst: forall {ty} (t: ty), HValue t
  | HOstVal: forall (ost: OState) idx, HValue (ost#[idx]%hvec).

  Inductive HProp: Prop -> Type :=
  | HAnd: forall P1 P2, HProp P1 -> HProp P2 -> HProp (P1 /\ P2)
  | HOr: forall P1 P2, HProp P1 -> HProp P2 -> HProp (P1 \/ P2)
  | HEq: forall t (e1 e2: t), HValue e1 -> HValue e2 -> HProp (e1 = e2)
  | HNe: forall t (e1 e2: t), HValue e1 -> HValue e2 -> HProp (e1 <> e2)
  | HLt: forall (e1 e2: nat), HValue e1 -> HValue e2 -> HProp (e1 < e2)
  | HLe: forall (e1 e2: nat), HValue e1 -> HValue e2 -> HProp (e1 <= e2)
  | HGt: forall (e1 e2: nat), HValue e1 -> HValue e2 -> HProp (e1 > e2)
  | HGe: forall (e1 e2: nat), HValue e1 -> HValue e2 -> HProp (e1 >= e2).

  Inductive HRqRsOPrec: OPrec -> Type :=
  | HRqAccepting: HRqRsOPrec RqAccepting
  | HRsAccepting: HRqRsOPrec RsAccepting
  | HUpLockFree: HRqRsOPrec UpLockFree
  | HDownLockFree: HRqRsOPrec DownLockFree
  | HFirstMsg: HRqRsOPrec FirstMsg
  | HUpLockMsgId: forall mty mid, HRqRsOPrec (UpLockMsgId mty mid)
  | HUpLockMsg: HRqRsOPrec UpLockMsg
  | HUpLockIdxBack: HRqRsOPrec UpLockIdxBack
  | HUpLockBackNone: HRqRsOPrec UpLockBackNone
  | HDownLockMsgId: forall mty mid, HRqRsOPrec (DownLockMsgId mty mid)
  | HDownLockMsg: HRqRsOPrec DownLockMsg
  | HDownLockIdxBack: HRqRsOPrec DownLockIdxBack
  | HMsgsFrom: forall froms, HRqRsOPrec (MsgsFrom froms)
  | HMsgIdsFrom: forall msgIds, HRqRsOPrec (MsgIdsFrom msgIds)
  | HMsgIdFromEach: forall msgId, HRqRsOPrec (MsgIdFromEach msgId)
  | HMsgsFromORq: forall rqty, HRqRsOPrec (MsgsFromORq rqty).

  Inductive HOPrec: OPrec -> Type :=
  | HOPrecAnd: forall {pr1 pr2}, HOPrec pr1 -> HOPrec pr2 -> HOPrec (OPrecAnd pr1 pr2)
  | HOPrecT: forall {pr}, HRqRsOPrec pr -> HOPrec pr
  | HOPrecP: forall {pr}, (forall ost orq mins, HProp (pr ost orq mins)) -> HOPrec pr.

  (** TODO: may need this [bvrep] *)
  (* Variable (bvrep: forall {V}, option V -> Type). *)
  Inductive HMonad {A}: option A -> Type :=
  | HBind:
      forall {V} (ov: option V),
      (* bvrep ov -> *)
      forall {cont}, (forall v, HMonad (cont v)) -> HMonad (bind ov cont)
  | HRet: forall v, HMonad (Some v).

  Section ReifyTrs.
    Variables (ost: OState) (orq: ORq Msg) (mins: list (Id Msg)).

    Inductive StateMTrsR: StateMTrs -> Type :=
    | HStateMTrs:
        forall mtrs,
          (forall stm, HMonad (mtrs stm)) ->
          StateMTrsR mtrs.

    Inductive OTrsR: OTrs -> Type :=
    | HTrsMTrs:
        forall mtrs,
          StateMTrsR mtrs ->
          OTrsR (TrsMTrs mtrs).

  End ReifyTrs.

End Reify.

Ltac reifyValue val :=
  match val with
  | hvec_ith ?ost ?idx => constr:(HOstVal ost idx)
  | _ => constr:(HConst val)
  end.

Ltac reifyProp p :=
  match p with
  | ?p1 /\ ?p2 => let pr1 := reifyProp p1 in
                  let pr2 := reifyProp p2 in
                  constr:(HAnd pr1 pr2)
  | ?p1 \/ ?p2 => let pr1 := reifyProp p1 in
                  let pr2 := reifyProp p2 in
                  constr:(HOr pr1 pr2)
  | ?e1 = ?e2 => let vr1 := reifyValue e1 in
                 let vr2 := reifyValue e2 in
                 constr:(HEq vr1 vr2)
  | ?e1 <> ?e2 => let vr1 := reifyValue e1 in
                  let vr2 := reifyValue e2 in
                  constr:(HNe vr1 vr2)
  | lt ?e1 ?e2 => let vr1 := reifyValue e1 in
                  let vr2 := reifyValue e2 in
                  constr:(HLt vr1 vr2)
  | le ?e1 ?e2 => let vr1 := reifyValue e1 in
                  let vr2 := reifyValue e2 in
                  constr:(HLe vr1 vr2)
  | gt ?e1 ?e2 => let vr1 := reifyValue e1 in
                  let vr2 := reifyValue e2 in
                  constr:(HGt vr1 vr2)
  | ge ?e1 ?e2 => let vr1 := reifyValue e1 in
                  let vr2 := reifyValue e2 in
                  constr:(HGe vr1 vr2)
  end.

Ltac reifyRqRsOPrec oprec :=
  match oprec with
  | RqAccepting => constr:(HRqAccepting)
  | RsAccepting => constr:(HRsAccepting)
  | UpLockFree => constr:(HUpLockFree)
  | DownLockFree => constr:(HDownLockFree)
  | FirstMsg => constr:(HFirstMsg)
  | UpLockMsgId ?mty ?mid => constr:(HUpLockMsgId mty mid)
  | UpLockMsg => constr:(HUpLockMsg)
  | UpLockIdxBack => constr:(HUpLockIdxBack)
  | UpLockBackNone => constr:(HUpLockBackNone)
  | DownLockMsgId ?mty ?mid => constr:(HDownLockMsgId mty mid)
  | DownLockMsg => constr:(HDownLockMsg)
  | DownLockIdxBack => constr:(HDownLockIdxBack)
  | MsgsFrom ?froms => constr:(HMsgsFrom froms)
  | MsgIdsFrom ?msgIds => constr:(HMsgIdsFrom msgIds)
  | MsgIdFromEach ?msgId => constr:(HMsgIdFromEach msgId)
  | MsgsFromORq ?rqty => constr:(HMsgsFromORq rqty)
  end.

Ltac reifyPropF p :=
  let ep := eval cbv beta in p in
  let rp := reifyProp ep in
  exact rp.
  
Ltac reifyOPrec oprec :=
  match oprec with
  | OPrecAnd ?op1 ?op2 =>
    let rop1 := reifyOPrec op1 in
    let rop2 := reifyOPrec op2 in
    constr:(HOPrecAnd rop1 rop2)
  | _ =>
    let rop := reifyRqRsOPrec oprec in
    constr:(HOPrecT rop)
  | _ => constr:(HOPrecP (fun ost orq mins =>
                            ltac:(reifyPropF (oprec ost orq mins))))
  end.

Section HemiolaDeep.
  Context `{DecValue} `{OStateIfc}.

  Record HRule (sr: Rule) :=
    { hrule_precond: HOPrec (rule_precond sr);
      hrule_trs: OTrsR (rule_trs sr)
    }.

  Record HObject :=
    { hobj_rules: list {sr: Rule & HRule sr} }.

  Record HSystem :=
    { hsys_objs: list HObject }.

End HemiolaDeep.

Arguments hvec_ith: simpl never.

(* Require Import Hemiola.Ex.Mesi.Mesi. *)
(* Existing Instance ImplOStateIfc. *)

(* Example hprec cidx: HOPrec (rule_precond (l1GetSImm cidx)). *)
(* Proof. *)
(*   simpl. *)
(*   match goal with *)
(*   | |- HOPrec ?oprec => *)
(*     let rop := reifyOPrec oprec in *)
(*     exact rop *)
(*   end. *)
(* Defined. *)

(* Example hr cidx: HRule (l1GetSImm cidx). *)
(* Proof. *)
(*   refine {| hrule_name := ""; hrule_precond := _; hrule_trs := _ |}. *)
(*   - simpl. *)
(*     match goal with *)
(*     | |- HOPrec ?oprec => *)
(*       let rop := reifyOPrec oprec in *)
(*       exact rop *)
(*     end. *)
(*   - simpl. *)
(*     repeat (intros; constructor). *)
(* Defined. *)

