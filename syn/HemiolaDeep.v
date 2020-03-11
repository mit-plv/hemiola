Require Import Hemiola.Common Hemiola.Index Hemiola.HVector.
Require Import Hemiola.Topology Hemiola.Syntax.
Require Import Hemiola.RqRsLang.
        
Set Implicit Arguments.

Import MonadNotations.

(* {| ost_ty := [nat:Type; bool:Type; MESI:Type; DirT:Type]%vector |}. *)

(* Inductive HTypes {t} (var: Type -> t): forall {sz}, Vector.t Type sz -> Type := *)
(* | HTyNil: HTypes var (Vector.nil _) *)
(* | HTyCons: *)
(*     forall {sz} {tys: Vector.t Type sz}, *)
(*       HTypes var tys -> *)
(*       forall {ty}, *)
(*         HType var ty -> *)
(*         HTypes var (ty :: tys). *)

(* Record HOStateIfc (oifc: OStateIfc) := *)
(*   { host_ty: HTypes (@ost_ty oifc); *)
(*     host_init: *)
(*   }. *)

Section Reify.
  Context `{DecValue} `{oifc: OStateIfc}.

  (** Reified syntax *)
  
  (* -- basis *)
  
  Inductive HValue: Type -> Type :=
  | HConst: forall {ty} (c: ty), HValue ty
  | HOstVal: forall idx, HValue (Vector.nth (@ost_ty oifc) idx).

  (* -- for precondition *)
  
  Inductive HOPrecP: Type :=
  | HAnd: HOPrecP -> HOPrecP -> HOPrecP
  | HOr: HOPrecP -> HOPrecP -> HOPrecP
  | HBoolT: HValue bool -> HOPrecP
  | HBoolF: HValue bool -> HOPrecP
  | HNatEq (sz: nat): HValue nat -> HValue nat -> HOPrecP
  | HNatNe (sz: nat): HValue nat -> HValue nat -> HOPrecP
  | HNatLt (sz: nat): HValue nat -> HValue nat -> HOPrecP
  | HNatLe (sz: nat): HValue nat -> HValue nat -> HOPrecP
  | HNatGt (sz: nat): HValue nat -> HValue nat -> HOPrecP
  | HNatGe (sz: nat): HValue nat -> HValue nat -> HOPrecP.

  Inductive HOPrecR: Type :=
  | HRqAccepting: HOPrecR
  | HRsAccepting: HOPrecR
  | HUpLockFree: HOPrecR
  | HDownLockFree: HOPrecR
  | HUpLockMsgId (mty: bool) (mid: IdxT): HOPrecR
  | HUpLockMsg: HOPrecR
  | HUpLockIdxBack: HOPrecR
  | HUpLockBackNone: HOPrecR
  | HDownLockMsgId (mty: bool) (mid: IdxT): HOPrecR
  | HDownLockMsg: HOPrecR
  | HDownLockIdxBack: HOPrecR
  | HMsgIdFrom (msgId: IdxT): HOPrecR.

  Inductive HMsgFrom: Type :=
  | HMsgFromParent: HMsgFrom
  | HMsgFromChild (cidx: IdxT): HMsgFrom.

  Inductive HOPrec: Type :=
  | HOPrecAnd: HOPrec -> HOPrec -> HOPrec
  | HOPrecRqRs: HOPrecR -> HOPrec
  | HOPrecProp: HOPrecP -> HOPrec.

  (* -- for transition *)

  Inductive HBindValue: Type -> Type :=
  | HNatGetFirstMsg: HBindValue Msg.

  Inductive HMonad: Type :=
  | HBind: forall {bt} (bv: HBindValue bt) (cont: bt -> HMonad), HMonad
  | HRet: forall (rst: StateM), HMonad.

  Inductive HStateMTrs: Type :=
  | HMTrs: HMonad -> HStateMTrs.

  Inductive HOTrs: Type :=
  | HTrsMTrs: HStateMTrs -> HOTrs.

  (** Interpretation *)
  
  Section Interp.
    Variables (ost: OState) (orq: ORq Msg) (mins: list (Id Msg)).

    Definition interpValue {ty} (hv: HValue ty): ty :=
      match hv with
      | HConst c => c
      | HOstVal idx => (ost#[idx])%hvec
      end.

    Fixpoint interpOPrecP (p: HOPrecP): Prop :=
      match p with
      | HAnd p1 p2 => interpOPrecP p1 /\ interpOPrecP p2
      | HOr p1 p2 => interpOPrecP p1 \/ interpOPrecP p2
      | HBoolT b => interpValue b = true
      | HBoolF b => interpValue b = false
      | HNatEq _ v1 v2 => interpValue v1 = interpValue v2
      | HNatNe _ v1 v2 => interpValue v1 <> interpValue v2
      | HNatLt _ v1 v2 => interpValue v1 < interpValue v2
      | HNatLe _ v1 v2 => interpValue v1 <= interpValue v2
      | HNatGt _ v1 v2 => interpValue v1 > interpValue v2
      | HNatGe _ v1 v2 => interpValue v1 >= interpValue v2
      end.

    Definition interpOPrecR (p: HOPrecR): Prop :=
      match p with
      | HRqAccepting => RqAccepting ost orq mins
      | HRsAccepting => RsAccepting ost orq mins
      | HUpLockFree => UpLockFree ost orq mins
      | HDownLockFree => DownLockFree ost orq mins
      | HUpLockMsgId mty mid => UpLockMsgId mty mid ost orq mins
      | HUpLockMsg => UpLockMsg ost orq mins
      | HUpLockIdxBack => UpLockIdxBack ost orq mins
      | HUpLockBackNone => UpLockBackNone ost orq mins
      | HDownLockMsgId mty mid => DownLockMsgId mty mid ost orq mins
      | HDownLockMsg => DownLockMsg ost orq mins
      | HDownLockIdxBack => DownLockIdxBack ost orq mins
      | HMsgIdFrom msgId => MsgIdsFrom [msgId] ost orq mins
      end.

    Definition interpMsgFrom (mf: HMsgFrom): Prop :=
      match mf with
      | HMsgFromParent => MsgsFromORq upRq ost orq mins
      | HMsgFromChild cidx => MsgsFrom [cidx] ost orq mins
      end.

    Definition interpBindValue {bt} (bv: HBindValue bt): option bt :=
      match bv with
      | HNatGetFirstMsg => getFirstMsg mins
      end.

  End Interp.

  Fixpoint interpOPrec (p: HOPrec): OPrec :=
    match p with
    | HOPrecAnd p1 p2 => interpOPrec p1 /\oprec interpOPrec p2
    | HOPrecRqRs rp => fun ost orq mins => interpOPrecR ost orq mins rp
    | HOPrecProp pp => fun ost _ _ => interpOPrecP ost pp
    end.

  Fixpoint interpMonad (hm: HMonad) (stm: StateM): option StateM :=
    match hm with
    | HBind bv cont =>
      (msg <-- interpBindValue (msgs stm) bv;
      interpMonad (cont msg) stm)
    | HRet rv => Some rv
    end.

  Definition interpMTrs (trs: HStateMTrs): StateMTrs :=
    match trs with
    | HMTrs hm => interpMonad hm
    end.

  Definition interpOTrs (trs: HOTrs): OTrs :=
    match trs with
    | HTrsMTrs mtrs => TrsMTrs (interpMTrs mtrs)
    end.
  
End Reify.

Section HemiolaDeep.
  Context `{DecValue} `{OStateIfc}.

  Record HRule (sr: Rule) :=
    { hrule_msg_from: HMsgFrom;
      hrule_precond: HOPrec;
      hrule_precond_ok:
        forall ost orq mins,
          (interpMsgFrom ost orq mins hrule_msg_from /\
           interpOPrec hrule_precond ost orq mins)
          <-> rule_precond sr ost orq mins;
      hrule_trs: HOTrs;
      hrule_trs_ok:
        forall ost orq mins,
          interpOTrs hrule_trs ost orq mins = rule_trs sr ost orq mins
    }.

  Record HObject :=
    { hobj_rules: list {sr: Rule & HRule sr} }.

  Record HSystem :=
    { hsys_objs: list HObject }.

End HemiolaDeep.

Arguments hvec_ith: simpl never.

