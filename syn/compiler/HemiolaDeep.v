Require Import List FunctionalExtensionality.

Require Import Hemiola.Common Hemiola.Index Hemiola.HVector.
Require Import Hemiola.Topology Hemiola.Syntax.
Require Import Hemiola.RqRsLang Hemiola.Ex.Template Hemiola.Ex.RuleTransform.

Set Implicit Arguments.

Import MonadNotations.

Lemma Vector_nth_map_comp {A B} (f: A -> B) {n} (v: Vector.t A n) (p: Fin.t n):
  Vector.nth (Vector.map f v) p = f (Vector.nth v p).
Proof.
  induction p.
  - revert n v; refine (@Vector.caseS _ _ _); now simpl.
  - revert n v p IHp; refine (@Vector.caseS _  _ _); now simpl.
Defined.

(** Configuration class *)

Class ReifyConfig :=
  { hcfg_msg_id_sz: nat (* log of degree *) * nat (* width *);
    hcfg_addr_sz: nat;
    hcfg_value_sz: nat;
  }.

Section Reify.
  Context `{DecValue} `{OStateIfc} `{ReifyConfig}.

  (** Reified syntax *)

  Inductive hbtype :=
  | HBool
  | HIdxO | HIdxQ | HIdxM
  | HAddr
  | HNat (width: nat)
  | HMsg
  | HIdm
  | HList: hbtype -> hbtype.

  Fixpoint hbtypeDenote (ht: hbtype): Type :=
    match ht with
    | HBool => bool
    | HIdxO
    | HIdxQ
    | HIdxM => IdxT
    | HAddr => unit
    | HNat _ => nat
    | HMsg => Msg
    | HIdm => IdxT * Msg
    | HList eht => list (hbtypeDenote eht)
    end.

  Class HDecValue :=
    { ht_value_ok: hbtypeDenote (HNat hcfg_value_sz) = t_type }.

  Class HOStateIfc :=
    { host_ty: Vector.t (option hbtype) ost_sz;
      host_ty_ok:
        forall i: Fin.t ost_sz,
          match Vector.nth host_ty i with
          | Some hbt => Vector.nth ost_ty i = hbtypeDenote hbt
          | None => True
          end
    }.
  Context `{HDecValue} `{HOStateIfc}.
  Definition hdv_type := HNat hcfg_value_sz.

  Section Basis.
    Variable var: hbtype -> Type.

    (* -- basic constants and expressions *)

    Inductive hbconst: hbtype -> Type :=
    | HBConstBool: forall b: bool, hbconst HBool
    | HBConstNat: forall w (n: nat), hbconst (HNat w)
    | HBConstIdxO: forall (i: IdxT), hbconst HIdxO
    | HBConstIdxQ: forall (i: IdxT), hbconst HIdxQ
    | HBConstIdxM: forall (i: IdxT), hbconst HIdxM.

    Inductive hbexp: hbtype -> Type :=
    | HBConst: forall ht (c: hbconst ht), hbexp ht
    | HVar: forall ht, var ht -> hbexp ht
    | HIdmId: hbexp HIdm -> hbexp HIdxQ
    | HIdmMsg: hbexp HIdm -> hbexp HMsg
    | HObjIdxOf: hbexp HIdxQ -> hbexp HIdxO
    | HAddrB: hbexp HAddr
    | HMsgB: hbexp HIdxM -> hbexp HBool -> hbexp HAddr -> hbexp hdv_type -> hbexp HMsg
    | HMsgId: hbexp HMsg -> hbexp HIdxM
    | HMsgType: hbexp HMsg -> hbexp HBool
    | HMsgAddr: hbexp HMsg -> hbexp HAddr
    | HMsgValue: hbexp HMsg -> hbexp hdv_type
    | HOstVal: forall i hbt, Vector.nth host_ty i = Some hbt -> hbexp hbt
    | HUpLockIdxBackI: hbexp HIdxQ
    | HDownLockIdxBackI: hbexp HIdxQ.

  End Basis.

  Class ExtType :=
    { hetype: Set;
      hetypeDenote: hetype -> Type
    }.

  Section TypeExtended.
    Context `{het: ExtType}.

    Inductive htype :=
    | HBType: hbtype -> htype
    | HEType: hetype -> htype.
    Coercion HBType: hbtype >-> htype.

    Fixpoint htypeDenote (ht: htype): Type :=
      match ht with
      | HBType hbt => hbtypeDenote hbt
      | HEType het => hetypeDenote het
      end.

    Class HOStateIfcFull :=
      { hostf_ty: Vector.t htype ost_sz;
        hostf_ty_ok: Vector.map htypeDenote hostf_ty = ost_ty;
        hostf_ty_compat:
          forall i hbt, host_ty[@i] = Some hbt -> hostf_ty[@i] = HBType hbt
      }.

    Class ExtExp :=
      { heexp: (htype -> Type) -> htype -> Type;
        interp_heexp:
          forall {ht} (e: heexp htypeDenote ht),
            OState -> ORq Msg -> list (Id Msg) ->
            htypeDenote ht;
        heoprec: (htype -> Type) -> Type;
        interp_heoprec:
          heoprec htypeDenote -> OState -> ORq Msg -> list (Id Msg) -> Prop
      }.

    Section ExpExtended.
      Context `{HOStateIfcFull} `{ExtExp}.

      Section ExtPhoas.
        Variables (var: htype -> Type).

        Definition bvar: hbtype -> Type :=
          fun hbt => var (HBType hbt).
        Definition evar: hetype -> Type :=
          fun het => var (HEType het).

        Inductive hexp: htype -> Type :=
        | HBExp: forall {hbt} (hbe: hbexp bvar hbt), hexp (HBType hbt)
        | HEExp: forall {ht} (hee: heexp var ht), hexp ht.

        (* -- precondition *)

        Inductive HOPrecP: Type :=
        | HTrue: HOPrecP
        | HAnd: HOPrecP -> HOPrecP -> HOPrecP
        | HOr: HOPrecP -> HOPrecP -> HOPrecP
        | HBoolT: hexp HBool -> HOPrecP
        | HBoolF: hexp HBool -> HOPrecP
        | HEq: forall {ht}, hexp ht -> hexp ht -> HOPrecP
        | HNe: forall {ht}, hexp ht -> hexp ht -> HOPrecP
        | HNatLt: forall {w}, hexp (HNat w) -> hexp (HNat w) -> HOPrecP
        | HNatLe: forall {w}, hexp (HNat w) -> hexp (HNat w) -> HOPrecP
        | HNatGt: forall {w}, hexp (HNat w) -> hexp (HNat w) -> HOPrecP
        | HNatGe: forall {w}, hexp (HNat w) -> hexp (HNat w) -> HOPrecP
        | HExtP: heoprec var -> HOPrecP
        | HNativeP: (OState -> ORq Msg -> list (Id Msg) -> Prop) -> HOPrecP.

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
        | HMsgIdFrom (msgId: IdxT): HOPrecR
        | HRssFull: HOPrecR.

        Inductive HMsgFrom: Type :=
        | HMsgFromNil: HMsgFrom
        | HMsgFromParent (pmidx: IdxT): HMsgFrom
        | HMsgFromChild (cmidx: IdxT): HMsgFrom
        | HMsgFromExt (emidx: IdxT): HMsgFrom
        | HMsgFromUpLock: HMsgFrom
        | HMsgFromDownLock (cidx: IdxT): HMsgFrom.

        Inductive HOPrecT: Type :=
        | HOPrecAnd: HOPrecT -> HOPrecT -> HOPrecT
        | HOPrecRqRs: HOPrecR -> HOPrecT
        | HOPrecProp: HOPrecP -> HOPrecT.

        (* -- transition *)

        Inductive hbval: hbtype -> Type :=
        | HGetFirstMsg: hbval HMsg
        | HGetUpLockMsg: hbval HMsg
        | HGetDownLockMsg: hbval HMsg
        | HGetUpLockIdxBack: hbval HIdxQ
        | HGetDownLockIdxBack: hbval HIdxQ
        | HGetDownLockFirstRs: hbval HIdm.

        Inductive HOState :=
        | HOStateI: HOState
        | HOstUpdate:
            forall (i: Fin.t ost_sz) {ht},
              Vector.nth hostf_ty i = ht ->
              hexp ht -> HOState -> HOState.

        Inductive HORq :=
        | HORqI: HORq
        | HUpdUpLock: hexp HMsg ->
                      hexp HIdxQ (* response-from *) ->
                      hexp HIdxQ (* response-back-to *) -> HORq
        | HUpdUpLockS: hexp HIdxQ (* response-from *) -> HORq
        | HRelUpLock: HORq
        | HUpdDownLock: hexp HMsg ->
                        hexp (HList HIdxQ) (* responses-from *) ->
                        hexp HIdxQ (* response-back-to *) -> HORq
        | HUpdDownLockS: hexp (HList HIdxQ) (* responses-from *) ->
                         HORq
        | HRelDownLock: HORq
        | HTrsfUpDown: hexp HMsg ->
                       hexp (HList HIdxQ) (* responses-from *) ->
                       hexp HIdxQ (* response-back-to *) -> HORq
        | HAddRs: hexp HIdxQ -> hexp HMsg -> HORq.

        Inductive HMsgsOut :=
        | HMsgOutNil: HMsgsOut
        | HMsgOutOne: hexp HIdxQ -> hexp HMsg -> HMsgsOut
        | HMsgsOutDown: hexp (HList HIdxQ) -> hexp HMsg -> HMsgsOut.

        Inductive HMonadT: Type :=
        | HBind: forall {ht} (bv: hbval ht) (cont: var ht -> HMonadT), HMonadT
        | HRet: HOState -> HORq -> HMsgsOut -> HMonadT.

      End ExtPhoas.

      Definition HOPrec := forall var, HOPrecT var.
      Definition HMonad := forall var, HMonadT var.

      Inductive HStateMTrs: Type :=
      | HMTrs: HMonad -> HStateMTrs.

      Inductive HOTrs: Type :=
      | HTrsMTrs: HStateMTrs -> HOTrs.

    End ExpExtended.

  End TypeExtended.

  Arguments HBConst {var}.
  Arguments HVar {var}.
  Arguments HIdmId {var}.
  Arguments HIdmMsg {var}.
  Arguments HObjIdxOf {var}.
  Arguments HAddrB {var}.
  Arguments HMsgB {var}.
  Arguments HMsgId {var}.
  Arguments HMsgType {var}.
  Arguments HMsgAddr {var}.
  Arguments HMsgValue {var}.
  Arguments HOstVal {var}.
  Arguments HUpLockIdxBackI {var}.
  Arguments HDownLockIdxBackI {var}.
  Arguments HBExp {_ _} {var} {hbt}.
  Arguments HEExp {_ _} {var} {ht}.
  Arguments HORqI {_ _} {var}.
  Arguments HUpdUpLock {_ _} {var}.
  Arguments HUpdUpLockS {_ _} {var}.
  Arguments HRelUpLock {_ _} {var}.
  Arguments HUpdDownLock {_ _} {var}.
  Arguments HUpdDownLockS {_ _} {var}.
  Arguments HRelDownLock {_ _} {var}.
  Arguments HTrsfUpDown {_ _} {var}.
  Arguments HAddRs {_ _} {var}.
  Arguments HMsgOutNil {_ _} {var}.
  Arguments HMsgOutOne {_ _} {var}.
  Arguments HMsgsOutDown {_ _} {var}.
  Arguments HOPrecRqRs {_ _} {var}.

  (** Interpretation *)

  Definition interpConst {ht} (c: hbconst ht): hbtypeDenote ht :=
    match c with
    | HBConstBool b => b
    | HBConstNat _ n => n
    | HBConstIdxO i => i
    | HBConstIdxQ i => i
    | HBConstIdxM i => i
    end.

  Section InterpExtended.
    Context `{het: ExtType} `{@HOStateIfcFull het} `{@ExtExp het}.

    Section WithPreState.
      Variables (ost: OState) (orq: ORq Msg) (mins: list (Id Msg)).

      Lemma host_ty_ok_i:
        forall (i: Fin.t ost_sz) hbt,
          Vector.nth host_ty i = Some hbt ->
          Vector.nth ost_ty i = hbtypeDenote hbt.
      Proof.
        intros.
        pose proof (host_ty_ok i).
        rewrite H6 in H7.
        assumption.
      Defined.

      Fixpoint interpBExp {ht} (e: hbexp hbtypeDenote ht): hbtypeDenote ht :=
        match e with
        | HBConst _ c => interpConst c
        | HVar _ hv => hv
        | HIdmId idm => idOf (interpBExp idm)
        | HIdmMsg idm => valOf (interpBExp idm)
        | HObjIdxOf midx => objIdxOf (interpBExp midx)
        | HAddrB => tt
        | HMsgB mid mty maddr mval =>
          {| msg_id := interpBExp mid;
             msg_type := interpBExp mty;
             msg_addr := interpBExp maddr;
             msg_value := match ht_value_ok in (_ = T) return T with
                          | eq_refl => interpBExp mval
                          end
          |}
        | HMsgId msg => msg_id (interpBExp msg)
        | HMsgType msg => msg_type (interpBExp msg)
        | HMsgAddr msg => msg_addr (interpBExp msg)
        | HMsgValue msg =>
          match eq_sym ht_value_ok in (_ = T) return T with
          | eq_refl => msg_value (interpBExp msg)
          end
        | HOstVal i hbt Heq =>
          match host_ty_ok_i _ Heq with
          | eq_refl => (ost#[i])%hvec
          end
        | HUpLockIdxBackI => getUpLockIdxBackI orq
        | HDownLockIdxBackI => getDownLockIdxBackI orq
        end.

      Definition interpExp {ht} (e: hexp htypeDenote ht): htypeDenote ht :=
        match e with
        | HBExp hbe => interpBExp hbe
        | HEExp hee => interp_heexp hee ost orq mins
        end.

      Fixpoint interpOPrecP (p: HOPrecP htypeDenote): Prop :=
        match p with
        | HTrue _ => True
        | HAnd p1 p2 => interpOPrecP p1 /\ interpOPrecP p2
        | HOr p1 p2 => interpOPrecP p1 \/ interpOPrecP p2
        | HBoolT b => interpExp b = true
        | HBoolF b => interpExp b = false
        | HEq v1 v2 => interpExp v1 = interpExp v2
        | HNe v1 v2 => interpExp v1 <> interpExp v2
        | HNatLt v1 v2 => interpExp v1 < interpExp v2
        | HNatLe v1 v2 => interpExp v1 <= interpExp v2
        | HNatGt v1 v2 => interpExp v1 > interpExp v2
        | HNatGe v1 v2 => interpExp v1 >= interpExp v2
        | HExtP _ ep => interp_heoprec ep ost orq mins
        | HNativeP _ p => p ost orq mins
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
        | HRssFull => RssFull ost orq mins
        end.

      Definition interpMsgFrom (mf: HMsgFrom): Prop :=
        match mf with
        | HMsgFromNil => MsgsFrom [] ost orq mins
        | HMsgFromParent pmidx => MsgsFrom [pmidx] ost orq mins
        | HMsgFromChild cmidx => MsgsFrom [cmidx] ost orq mins
        | HMsgFromExt emidx => MsgsFrom [emidx] ost orq mins
        | HMsgFromUpLock => MsgsFromORq upRq ost orq mins
        | HMsgFromDownLock cidx =>
          MsgsFrom [rqUpFrom cidx] ost orq mins /\
          RsWaiting cidx ost orq mins
        end.

      Definition interpBindValue {bt} (bv: hbval bt)
        : option (htypeDenote (HBType bt)) :=
        match bv with
        | HGetFirstMsg => getFirstMsg mins
        | HGetUpLockMsg => getUpLockMsg orq
        | HGetDownLockMsg => getDownLockMsg orq
        | HGetUpLockIdxBack => getUpLockIdxBack orq
        | HGetDownLockIdxBack => getDownLockIdxBack orq
        | HGetDownLockFirstRs => getFirstIdMsg (getRss orq)
        end.

      Lemma hostf_ty_ok_i:
        forall (i: Fin.t ost_sz) ht,
          Vector.nth hostf_ty i = ht ->
          htypeDenote ht = Vector.nth ost_ty i.
      Proof.
        intros; subst ht.
        rewrite <-hostf_ty_ok.
        apply eq_sym, Vector_nth_map_comp; reflexivity.
      Defined.

      Fixpoint interpOState (host: HOState htypeDenote): OState :=
        (match host with
         | HOStateI _ => ost
         | HOstUpdate i Heq hval host' =>
           (interpOState host') +#[i <- match hostf_ty_ok_i _ Heq with
                                        | eq_refl => interpExp hval
                                        end]
         end)%hvec.

      Definition interpORq (horq: HORq htypeDenote): ORq Msg :=
        match horq with
        | HORqI => orq
        | HUpdUpLock rq rsf rsb =>
          addRq orq upRq (interpExp rq) [interpExp rsf] (interpExp rsb)
        | HUpdUpLockS rsf => addRqS orq upRq [interpExp rsf]
        | HRelUpLock => removeRq orq upRq
        | HUpdDownLock rq rssf rsb =>
          addRq orq downRq (interpExp rq) (interpExp rssf) (interpExp rsb)
        | HUpdDownLockS rssf =>
          addRqS orq downRq (interpExp rssf)
        | HRelDownLock => removeRq orq downRq
        | HTrsfUpDown rq rssf rsb =>
          addRq (removeRq orq upRq)
                downRq (interpExp rq) (interpExp rssf) (interpExp rsb)
        | HAddRs midx msg => addRs orq (interpExp midx) (interpExp msg)
        end.

      Definition interpMsgOuts (houts: HMsgsOut htypeDenote): list (Id Msg) :=
        match houts with
        | HMsgOutNil => []
        | HMsgOutOne midx msg => [(interpExp midx, interpExp msg)]
        | HMsgsOutDown minds msg =>
          List.map (fun midx => (midx, interpExp msg)) (interpExp minds)
        end.

    End WithPreState.

    Fixpoint interpOPrec (p: HOPrecT htypeDenote): OPrec :=
      match p with
      | HOPrecAnd p1 p2 => interpOPrec p1 /\oprec interpOPrec p2
      | HOPrecRqRs rp => fun ost orq mins => interpOPrecR ost orq mins rp
      | HOPrecProp pp => fun ost orq mins => interpOPrecP ost orq mins pp
      end.

    Fixpoint interpMonad (hm: HMonadT htypeDenote) (stm: StateM): option StateM :=
      match hm with
      | HBind bv cont =>
        (msg <-- interpBindValue (orq stm) (msgs stm) bv;
        interpMonad (cont msg) stm)
      | HRet host horq houts =>
        Some {| ost := interpOState (ost stm) (orq stm) (msgs stm) host;
                orq := interpORq (ost stm) (orq stm) (msgs stm) horq;
                msgs := interpMsgOuts (ost stm) (orq stm) (msgs stm) houts |}
      end.

    Definition interpMTrs (trs: HStateMTrs): StateMTrs :=
      match trs with
      | HMTrs hm => interpMonad (hm htypeDenote)
      end.

    Definition interpOTrs (trs: HOTrs): OTrs :=
      match trs with
      | HTrsMTrs mtrs => TrsMTrs (interpMTrs mtrs)
      end.

  End InterpExtended.

End Reify.

Section HemiolaDeep.
  Context `{hcfg: ReifyConfig}
          `{dv: DecValue}
          `{hdv: @HDecValue dv hcfg}
          `{oifc: OStateIfc}
          `{het: ExtType}
          `{ee: @ExtExp dv oifc het}
          `{hoifc: @HOStateIfc dv oifc}
          `{hoifcf: @HOStateIfcFull dv oifc hoifc het}.

  Record HRule (sr: Rule) :=
    { hrule_msg_from: HMsgFrom;
      hrule_precond: HOPrec;
      hrule_precond_ok:
        forall ost orq mins,
          (interpMsgFrom ost orq mins hrule_msg_from /\
           interpOPrec (hrule_precond htypeDenote) ost orq mins)
          <-> rule_precond sr ost orq mins;
      hrule_trs: HOTrs;
      hrule_trs_ok:
        forall ost orq mins,
          interpOTrs hrule_trs ost orq mins = rule_trs sr ost orq mins
    }.

  Record HObject (sobj: Object) :=
    { hobj_rules: list {sr: Rule & HRule sr};
      hobj_rules_ok:
        List.map (@projT1 _ _) hobj_rules = obj_rules sobj
    }.

  Record HSystem (ssys: System) :=
    { hsys_objs: list {sobj: Object & HObject sobj};
      hsys_objs_ok:
        List.map (@projT1 _ _) hsys_objs = sys_objs ssys
    }.

End HemiolaDeep.

Arguments hvec_ith: simpl never.
Arguments hvec_upd: simpl never.

(*! Reification *)

(** * Utilities *)

Lemma and_iff_sep: forall A B C D, (A <-> B) -> (C <-> D) -> (A /\ C <-> B /\ D).
Proof. firstorder. Qed.
Lemma or_iff_sep: forall A B C D, (A <-> B) -> (C <-> D) -> (A \/ C <-> B \/ D).
Proof. firstorder. Qed.

Lemma eq_iff_sep: forall {t} (A B C D: t), A = B -> C = D -> (A = C <-> B = D).
Proof. intuition congruence. Qed.
Lemma ne_iff_sep: forall {t} (A B C D: t), A = B -> C = D -> (A <> C <-> B <> D).
Proof. intuition congruence. Qed.
Lemma lt_iff_sep: forall A B C D, A = B -> C = D -> (A < C <-> B < D).
Proof. firstorder. Qed.
Lemma le_iff_sep: forall A B C D, A = B -> C = D -> (A <= C <-> B <= D).
Proof. firstorder. Qed.
Lemma gt_iff_sep: forall A B C D, A = B -> C = D -> (A > C <-> B > D).
Proof. firstorder. Qed.
Lemma ge_iff_sep: forall A B C D, A = B -> C = D -> (A >= C <-> B >= D).
Proof. firstorder. Qed.

Lemma p_f_equal: forall {t} (f: t -> Prop) A B, A = B -> (f A <-> f B).
Proof. intuition congruence. Qed.

Lemma TrsMTrs_ext:
  forall `{DecValue} `{OStateIfc} (trs1 trs2: StateMTrs),
    (forall stm, trs1 stm = trs2 stm) ->
    forall ost orq mins,
      TrsMTrs trs1 ost orq mins = TrsMTrs trs2 ost orq mins.
Proof.
  cbv [TrsMTrs]; intros.
  rewrite H1; reflexivity.
Qed.

(** * Tactics *)

Ltac reify_OPrecR t :=
  match t with
  | RqAccepting _ _ _ => constr:(HRqAccepting)
  | RsAccepting _ _ _ => constr:(HRsAccepting)
  | UpLockFree _ _ _ => constr:(HUpLockFree)
  | DownLockFree _ _ _ => constr:(HDownLockFree)
  | UpLockMsgId ?mty ?mid _ _ _ => constr:(HUpLockMsgId mty mid)
  | UpLockMsg _ _ _ => constr:(HUpLockMsg)
  | UpLockIdxBack _ _ _ => constr:(HUpLockIdxBack)
  | UpLockBackNone _ _ _ => constr:(HUpLockBackNone)
  | DownLockMsgId ?mty ?mid _ _ _ => constr:(HDownLockMsgId mty mid)
  | DownLockMsg _ _ _ => constr:(HDownLockMsg)
  | DownLockIdxBack _ _ _ => constr:(HDownLockIdxBack)
  | MsgIdsFrom [?msgId] _ _ _ => constr:(HMsgIdFrom msgId)
  | RssFull _ _ _ => constr:(HRssFull)
  end.

Ltac renote_OPrecRqRs :=
  match goal with
  | |- interpOPrec _ _ _ _ <-> ?t =>
    let r := reify_OPrecR t in
    instantiate (1:= HOPrecRqRs _ r); apply iff_refl
  end.

Ltac renote_const :=
  match goal with
  | |- interpConst _ = ?t =>
    match type of t with
    | bool => instantiate (1:= HBConstBool _); reflexivity
    | nat => instantiate (1:= HBConstNat _ _); reflexivity
    | IdxT => instantiate (1:= HBConstIdxO _); reflexivity
    | IdxT => instantiate (1:= HBConstIdxQ _); reflexivity
    | IdxT => instantiate (1:= HBConstIdxM _); reflexivity
    end
  end.

Ltac renote_bexp :=
  repeat
    (cbv [rqMsg rsMsg miv_id miv_value];
     try match goal with
         | |- interpBExp _ _ _ = ?t =>
           match t with
           | hvec_ith _ ?i => instantiate (1:= HOstVal _ i eq_refl); reflexivity
           | getUpLockIdxBackI _ => instantiate (1:= HUpLockIdxBackI _); reflexivity
           | getDownLockIdxBackI _ => instantiate (1:= HDownLockIdxBackI _); reflexivity
           | idOf _ => instantiate (1:= HIdmId _); simpl; f_equal
           | valOf _ => instantiate (1:= HIdmMsg _); simpl; f_equal
           | objIdxOf _ => instantiate (1:= HObjIdxOf _); simpl; f_equal
           | tt => instantiate (1:= HAddrB _); reflexivity
           | {| msg_id := _ |} => instantiate (1:= HMsgB _ _ _ _); simpl; f_equal
           | msg_id _ => instantiate (1:= HMsgId _); simpl; f_equal
           | msg_type _ => instantiate (1:= HMsgType _); simpl; f_equal
           | msg_addr _ => instantiate (1:= HMsgAddr _); simpl; f_equal
           | msg_value _ => instantiate (1:= HMsgValue _); simpl; f_equal
           | _ =>
             tryif is_var t then fail
             else (instantiate (1:= HBConst _ _); simpl; renote_const)
           | _ => instantiate (1:= HVar _ _ _); reflexivity
           end
         end).

Ltac renote_list_bexp :=
  repeat
    match goal with
    | |- map (interpBExp _ _) _ = (_ :: _)%list =>
      instantiate (1:= (_ :: _)%list); simpl; f_equal
    | |- map (interpBExp _ _) _ = nil =>
      instantiate (1:= nil); reflexivity
    end; renote_bexp.

Ltac renote_eexp := idtac "Error: redefine [renote_eexp]".

Ltac renote_exp :=
  match goal with
  | |- interpExp _ _ _ _ = _ =>
    instantiate (1:= HBExp _); simpl; renote_bexp; fail
  | |- interpExp _ _ _ _ = _ =>
    instantiate (1:= HEExp _ _); simpl; renote_eexp
  end.

Ltac renote_OPrec_ext := idtac "Error: redefine [renote_OPrec_ext]".

Ltac renote_OPrecP :=
  repeat
    match goal with
    | |- interpOPrecP _ _ _ _ <-> ?t =>
      match t with
      | True => instantiate (1:= HTrue _); simpl; apply iff_refl
      | _ /\ _ => instantiate (1:= HAnd _ _); simpl; apply and_iff_sep
      | _ \/ _ => instantiate (1:= HOr _ _); simpl; apply or_iff_sep
      | _ = true => instantiate (1:= HBoolT _); simpl; apply eq_iff_sep;
                    [renote_exp|reflexivity]
      | _ = false => instantiate (1:= HBoolF _); simpl; apply eq_iff_sep;
                     [renote_exp|reflexivity]
      | @eq nat _ _ => instantiate (1:= HEq (ht:= HBType (HNat _)) _ _); simpl;
                       apply eq_iff_sep; renote_exp
      | not (@eq nat _ _) =>
        instantiate (1:= HNe (ht:= HBType (HNat _)) _ _); simpl;
        apply ne_iff_sep; renote_exp
      | _ < _ => instantiate (1:= HNatLt (w:= _) _ _); simpl;
                 apply lt_iff_sep; renote_exp
      | _ <= _ => instantiate (1:= HNatLe (w:= _) _ _); simpl;
                  apply le_iff_sep; renote_exp
      | _ > _ => instantiate (1:= HNatGt (w:= _) _ _); simpl;
                 apply gt_iff_sep; renote_exp
      | _ >= _ => instantiate (1:= HNatGe (w:= _) _ _); simpl;
                  apply ge_iff_sep; renote_exp
      | _ => instantiate (1:= HExtP _ _); simpl; renote_OPrec_ext
      | _ => instantiate (1:= HNativeP _ (fun ost orq mins => _));
             simpl; apply iff_refl
      end
    end.

Ltac renote_OPrecProp :=
  match goal with
  | |- interpOPrec _ _ _ _ <-> ?t =>
    instantiate (1:= HOPrecProp _); simpl;
    renote_OPrecP
  end.

Ltac renote_OPrec :=
  repeat
    match goal with
    | |- interpOPrec (?t htypeDenote) _ _ _ <-> _ =>
      is_evar t; instantiate (1:= fun var => _); simpl
    | |- interpOPrec _ _ _ _ <-> (_ /\oprec _) _ _ _ =>
      instantiate (1:= HOPrecAnd _ _); simpl; apply and_iff_sep
    | |- _ => renote_OPrecRqRs; fail
    | |- _ => renote_OPrecProp
    end.

Ltac reify_MsgFrom t :=
  match t with
  | MsgsFrom [] _ _ _ => constr:(HMsgFromNil)
  | MsgsFrom [?midx] _ _ _ =>
    match midx with
    | rqUpFrom (l1ExtOf _) => constr:(HMsgFromExt midx)
    | downTo _ => constr:(HMsgFromParent midx)
    | _ => constr:(HMsgFromChild midx)
    end
  | MsgsFromORq upRq _ _ _ => constr:(HMsgFromUpLock)
  end.

Ltac renote_MsgFrom :=
  match goal with
  | |- interpMsgFrom _ _ _ _ <-> ?t =>
    let r := reify_MsgFrom t in
    instantiate (1:= r); apply iff_refl
  end.

Ltac reify_bvalue bv :=
  match bv with
  | getFirstMsg _ => constr:(HGetFirstMsg)
  | getUpLockMsg _ => constr:(HGetUpLockMsg)
  | getDownLockMsg _ => constr:(HGetDownLockMsg)
  | getUpLockIdxBack _ => constr:(HGetUpLockIdxBack)
  | getDownLockIdxBack _ => constr:(HGetDownLockIdxBack)
  | getFirstIdMsg (getRss _) => constr:(HGetDownLockFirstRs)
  end.

Ltac renote_OState :=
  repeat
    match goal with
    | |- interpOState _ _ _ _ = ?t =>
      match t with
      | hvec_upd _ ?i _ =>
        instantiate (1 := HOstUpdate (ht:= hostf_ty[@i]) i eq_refl _ _);
        simpl; f_equal; [|renote_exp]
      | _ => instantiate (1:= HOStateI _); reflexivity
      end
    end.

Ltac renote_ORq :=
  repeat
    match goal with
    | |- interpORq _ _ _ _ = ?t =>
      match t with
      | addRq (removeRq _ upRq) downRq _ _ _ =>
        instantiate (1:= HTrsfUpDown _ _ _); simpl; repeat f_equal; renote_exp
      | addRq _ upRq _ _ _ =>
        instantiate (1:= HUpdUpLock _ _ _); simpl; repeat f_equal; renote_exp
      | addRqS _ upRq _ =>
        instantiate (1:= HUpdUpLockS _); simpl; repeat f_equal; renote_exp
      | removeRq _ upRq => instantiate (1:= HRelUpLock _); simpl; f_equal
      | addRq _ downRq _ _ _ =>
        instantiate (1:= HUpdDownLock _ _ _); simpl; repeat f_equal; renote_exp
      | addRqS _ downRq _ =>
        instantiate (1:= HUpdDownLockS _); simpl; repeat f_equal; renote_exp
      | removeRq _ downRq => instantiate (1:= HRelDownLock _); simpl; f_equal
      | addRs _ _ _ => instantiate (1:= HAddRs _ _); simpl; f_equal; renote_exp
      | _ => instantiate (1:= HORqI _); reflexivity
      end
    end.

Ltac renote_MsgOuts :=
  match goal with
  | |- interpMsgOuts _ _ _ _ = ?t =>
    match t with
    | []%list => instantiate (1:= HMsgOutNil _); reflexivity
    | [(?midx, _)]%list => instantiate (1:= HMsgOutOne _ _); simpl; repeat f_equal; renote_exp
    | map ?f _ =>
      match f with
      | (fun _ => (downTo _, _)) =>
        instantiate (1:= HMsgsOutDown _ _); simpl;
        instantiate (1:= HEExp _ _); simpl; renote_eexp
      end
    | _ => idtac "FIXME: [renote_MsgOuts]"
    end
  end.

Ltac renote_trs_monad :=
  repeat
    match goal with
    | |- interpMonad (?t _) _ = _ =>
      instantiate (1:= fun _ => _); simpl
    | |- (fun _ => _) = (fun _ => _) =>
      apply functional_extensionality; intros
    | |- interpMonad _ _ = ?bv >>= _ =>
      let rbv := reify_bvalue bv in
      instantiate (1:= HBind rbv _); simpl; f_equal
    | |- interpMonad _ _ = Some _ =>
      instantiate (1:= HRet _ _ _); simpl;
      repeat f_equal; [renote_OState|renote_ORq|renote_MsgOuts]
    end.

Ltac renote_OTrs :=
  match goal with
  | |- interpOTrs _ _ _ _ = TrsMTrs _ _ _ _ =>
    instantiate (1:= HTrsMTrs (HMTrs _)); simpl;
    apply TrsMTrs_ext; intros;
    renote_trs_monad
  end.

Ltac renote_rule_init :=
  refine {| hrule_msg_from := _ |};
  intros; repeat autounfold with MesiRules;
  cbv [immRule immDownRule immUpRule
               rqUpUpRule rqUpUpRuleS rqUpDownRule rqUpDownRuleS rqDownDownRule
               rsDownDownRule rsDownDownRuleS rsUpDownRule rsUpDownRuleOne
               rsUpUpRule rsUpUpRuleOne rsDownRqDownRule];
  cbv [rsTakeOne rsRelease rsReleaseOne];
  cbv [rule_precond rule_trs].

Ltac renote_rule :=
  renote_rule_init;
  [apply and_iff_sep; [renote_MsgFrom|renote_OPrec]
  |renote_OTrs].

Tactic Notation "⇑rule" := renote_rule.
