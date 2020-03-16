Require Import Hemiola.Common Hemiola.Index Hemiola.HVector.
Require Import Hemiola.Topology Hemiola.Syntax.
Require Import Hemiola.RqRsLang.
        
Set Implicit Arguments.

Definition TODO := cheat.

Import MonadNotations.

(** Configuration class *)

Class hconfig :=
  { hcfg_oidx_sz: nat;
    hcfg_oidx_deg: nat;
    hcfg_midx_sz: nat;
    hcfg_midx_deg: nat;
    hcfg_msg_id_sz: nat;
    hcfg_msg_id_deg: nat;
    hcfg_value_sz: nat }.

Section Reify.
  Context `{DecValue} `{oifc: OStateIfc}.
  Context `{hconfig}.

  (** Reified syntax *)

  Inductive htype :=
  | HBool
  | HIdx (width: nat)
  | HNat (width: nat)
  | HValue
  | HMsg
  | HPair: htype -> htype -> htype.

  Definition HIdxO := HIdx hcfg_oidx_sz.
  Definition HIdxQ := HIdx hcfg_midx_sz.
  Definition HIdxM := HIdx hcfg_msg_id_sz.

  Fixpoint htypeDenote (ht: htype): Type :=
    match ht with
    | HBool => bool
    | HIdx _ => IdxT
    | HNat _ => nat
    | HValue => t_type
    | HMsg => Msg
    | HPair ht1 ht2 => htypeDenote ht1 * htypeDenote ht2
    end.

  Section Phoas.
    Variable var: htype -> Type.
    
    (* -- constants and expressions *)

    Inductive hconst: htype -> Type :=
    | HConstBool: forall b: bool, hconst HBool
    | HConstNat: forall w (n: nat), hconst (HNat w)
    | HConstIdx: forall w (deg: nat) (i: IdxT), hconst (HIdx w).

    Inductive hexp: htype -> Type :=
    | HConst: forall ht (c: hconst ht), hexp ht
    | HVar: forall ht, var ht -> hexp ht
    | HMsgB: hexp HIdxM -> hexp HBool -> hexp HValue -> hexp HMsg
    | HIdm: hexp HIdxQ -> hexp HMsg -> hexp (HPair HIdxQ HMsg)
    | HOstVal: forall i ht,
        Vector.nth (@ost_ty oifc) i = htypeDenote ht -> hexp ht.

    (* -- precondition *)
    
    Inductive HOPrecP: Type :=
    | HAnd: HOPrecP -> HOPrecP -> HOPrecP
    | HOr: HOPrecP -> HOPrecP -> HOPrecP
    | HBoolT: hexp HBool -> HOPrecP
    | HBoolF: hexp HBool -> HOPrecP
    | HEq: forall {ht}, hexp ht -> hexp ht -> HOPrecP
    | HNe: forall {ht}, hexp ht -> hexp ht -> HOPrecP
    | HNatLt: forall {w}, hexp (HNat w) -> hexp (HNat w) -> HOPrecP
    | HNatLe: forall {w}, hexp (HNat w) -> hexp (HNat w) -> HOPrecP
    | HNatGt: forall {w}, hexp (HNat w) -> hexp (HNat w) -> HOPrecP
    | HNatGe: forall {w}, hexp (HNat w) -> hexp (HNat w) -> HOPrecP.

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

    Inductive HOPrecT: Type :=
    | HOPrecAnd: HOPrecT -> HOPrecT -> HOPrecT
    | HOPrecRqRs: HOPrecR -> HOPrecT
    | HOPrecProp: HOPrecP -> HOPrecT.

    (* -- transition *)

    Inductive hbval: htype -> Type :=
    | HGetFirstMsg: hbval HMsg
    | HGetUpLockMsg: hbval HMsg
    | HGetDownLockMsg: hbval HMsg
    | HGetUpLockIdxBack: hbval HIdxQ
    | HGetDownLockIdxBack: hbval HIdxQ.

    Inductive HOState :=
    | HOStateI: HOState.
      
    Inductive HORq :=
    | HORqI: HORq
    | HUpdUpLock: hexp HMsg ->
                  hexp HIdxQ (* response-from *) ->
                  hexp HIdxQ (* response-back-to *) -> HORq
    | HRelUpLock: HORq
    | HUpdDownLock: hexp HMsg ->
                    list (hexp HIdxQ) (* responses-from *) ->
                    hexp HIdxQ (* response-back-to *) -> HORq
    | HRelDownLock.
    
    Inductive HMsgsOut :=
    | HMsgsOutI: list (hexp (HPair HIdxQ HMsg)) -> HMsgsOut.

    Inductive HMonadT: Type :=
    | HBind: forall {ht} (bv: hbval ht) (cont: var ht -> HMonadT), HMonadT
    | HRet: HOState -> HORq -> HMsgsOut -> HMonadT.

  End Phoas.

  Arguments HConst {var}.
  Arguments HVar {var}.
  Arguments HMsgB {var}.
  Arguments HIdm {var}.
  Arguments HOstVal {var}.
  Arguments HORqI {var}.
  Arguments HUpdUpLock {var}.
  Arguments HRelUpLock {var}.
  Arguments HUpdDownLock {var}.
  Arguments HRelDownLock {var}.
  Arguments HMsgsOutI {var}.
  Arguments HOPrecRqRs {var}.

  Definition HOPrec := forall var, HOPrecT var.
  Definition HMonad := forall var, HMonadT var.

  Inductive HStateMTrs: Type :=
  | HMTrs: HMonad -> HStateMTrs.

  Inductive HOTrs: Type :=
  | HTrsMTrs: HStateMTrs -> HOTrs.

  (** Interpretation *)
  
  Section WithPreState.
    Variables (ost: OState) (orq: ORq Msg) (mins: list (Id Msg)).

    Definition interpConst {ht} (c: hconst ht): htypeDenote ht :=
      match c with
      | HConstBool b => b
      | HConstNat _ n => n
      | HConstIdx _ _ i => i
      end.

    Fixpoint interpExp {ht} (e: hexp htypeDenote ht): htypeDenote ht :=
      match e with
      | HConst _ c => interpConst c
      | HVar _ hv => hv
      | HMsgB mid mty mval =>
        {| msg_id := interpExp mid;
           msg_type := interpExp mty;
           msg_value := interpExp mval |}
      | HIdm midx msg => (interpExp midx, interpExp msg)
      | HOstVal i ht Heq =>
        match Heq with
        | eq_refl => (ost#[i])%hvec
        end
      end.

    Fixpoint interpOPrecP (p: HOPrecP htypeDenote): Prop :=
      match p with
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

    Definition interpBindValue {bt} (bv: hbval bt): option (htypeDenote bt) :=
      match bv with
      | HGetFirstMsg => getFirstMsg mins
      | HGetUpLockMsg => getUpLockMsg orq
      | HGetDownLockMsg => getDownLockMsg orq
      | HGetUpLockIdxBack => getUpLockIdxBack orq
      | HGetDownLockIdxBack => getDownLockIdxBack orq
      end.

    Definition interpOState (host: HOState): OState :=
      match host with
      | HOStateI => ost
      end.

    Definition interpORq (horq: HORq htypeDenote): ORq Msg :=
      match horq with
      | HORqI => orq
      | HUpdUpLock rq rsf rsb =>
        addRq orq upRq (interpExp rq) [interpExp rsf] (interpExp rsb)
      | HRelUpLock => removeRq orq upRq
      | HUpdDownLock rq rssf rsb =>
        addRq orq downRq (interpExp rq) (List.map interpExp rssf) (interpExp rsb)
      | HRelDownLock => removeRq orq downRq
      end.

    Definition interpMsgOuts (houts: HMsgsOut htypeDenote): list (Id Msg) :=
      match houts with
      | HMsgsOutI outs => List.map interpExp outs
      end.
    
  End WithPreState.

  Fixpoint interpOPrec (p: HOPrecT htypeDenote): OPrec :=
    match p with
    | HOPrecAnd p1 p2 => interpOPrec p1 /\oprec interpOPrec p2
    | HOPrecRqRs rp => fun ost orq mins => interpOPrecR ost orq mins rp
    | HOPrecProp pp => fun ost _ _ => interpOPrecP ost pp
    end.

  Fixpoint interpMonad (hm: HMonadT htypeDenote) (stm: StateM): option StateM :=
    match hm with
    | HBind bv cont =>
      (msg <-- interpBindValue (orq stm) (msgs stm) bv;
      interpMonad (cont msg) stm)
    | HRet host horq houts =>
      Some {| ost := interpOState (ost stm) host;
              orq := interpORq (ost stm) (orq stm) horq;
              msgs := interpMsgOuts (ost stm) houts |}
    end.

  Definition interpMTrs (trs: HStateMTrs): StateMTrs :=
    match trs with
    | HMTrs hm => interpMonad (hm htypeDenote)
    end.

  Definition interpOTrs (trs: HOTrs): OTrs :=
    match trs with
    | HTrsMTrs mtrs => TrsMTrs (interpMTrs mtrs)
    end.
  
End Reify.

Section HemiolaDeep.
  Context `{DecValue} `{OStateIfc} `{hconfig}.

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



(** * Temporary Testing Section *)
Require Import Hemiola.Ex.TopoTemplate Hemiola.Ex.RuleTemplate.
Require Import Hemiola.Ex.Mesi.Mesi.

Require Import FunctionalExtensionality.

Lemma abcd: forall A B C D, (A <-> B) -> (C <-> D) -> (A /\ C <-> B /\ D).
Proof. firstorder. Qed.

Section Tests.

  Lemma TrsMTrs_ext:
    forall `{DecValue} `{OStateIfc} (trs1 trs2: StateMTrs),
      (forall stm, trs1 stm = trs2 stm) ->
      forall ost orq mins,
        TrsMTrs trs1 ost orq mins = TrsMTrs trs2 ost orq mins.
  Proof.
    cbv [TrsMTrs]; intros.
    rewrite H1; reflexivity.
  Qed.

  Variable oidx: IdxT.

  Instance mesiHConfig: hconfig :=
    {| hcfg_oidx_sz := 8;
       hcfg_oidx_deg := 4;
       hcfg_midx_sz := 10;
       hcfg_midx_deg := 16;
       hcfg_msg_id_sz := 5;
       hcfg_msg_id_deg := 4;
       hcfg_value_sz := 32 |}.

  Existing Instance Mesi.ImplOStateIfc.

  Definition hl1GetSImm: HRule (l1GetSImm (l1ExtOf oidx)).
  Proof.
    refine {| hrule_msg_from := _ |}.

    - intros.
      repeat autounfold with MesiRules.
      cbv [immDownRule].
      cbv [rule_precond].

      apply abcd.

      + cbv [interpMsgFrom].
        instantiate (1:= HMsgFromChild _).
        apply iff_refl.

      + instantiate (1:= fun var => HOPrecAnd (var:= var) _ _); simpl; apply abcd.
        all: repeat
               match goal with
               | |- _ <-> (_ /\oprec _) _ _ _ =>
                 instantiate (1:= HOPrecAnd _ _); simpl; apply abcd
               end.

        1-4: instantiate (1:= HOPrecRqRs _ _); simpl.
        1-4: first [instantiate (1:= HRqAccepting); apply iff_refl; fail
                   |instantiate (1:= HRsAccepting); apply iff_refl; fail
                   |instantiate (1:= HUpLockFree); apply iff_refl; fail
                   |instantiate (1:= HDownLockFree); apply iff_refl; fail
                   |instantiate (1:= HUpLockMsgId _ _); apply iff_refl; fail
                   |instantiate (1:= HUpLockMsg); apply iff_refl; fail
                   |instantiate (1:= HUpLockIdxBack); apply iff_refl; fail
                   |instantiate (1:= HUpLockBackNone); apply iff_refl; fail
                   |instantiate (1:= HDownLockMsgId _ _); apply iff_refl; fail
                   |instantiate (1:= HDownLockMsg); apply iff_refl; fail
                   |instantiate (1:= HDownLockIdxBack); apply iff_refl; fail
                   |instantiate (1:= HMsgIdFrom _); apply iff_refl; fail].

        instantiate (1:= HOPrecProp _); simpl.
        instantiate (1:= HNatLe (w:= 2) _ _); simpl.
        instantiate (2:= HConst _ (HConstNat _ Mesi.mesiS)); simpl.
        instantiate (1:= HOstVal _ status (HNat _) eq_refl).
        apply iff_refl.

    - intros.
      repeat autounfold with MesiRules.
      cbv [immDownRule].
      cbv [rule_trs].

      instantiate (1:= HTrsMTrs (HMTrs _)); simpl.
      apply TrsMTrs_ext; intros.
      instantiate (1:= fun var => HBind (var:= var) _ _); simpl.
      instantiate (3:= HGetFirstMsg); simpl.
      instantiate (1:= fun msg => HRet _ _ _).
      simpl; repeat f_equal.
      apply functional_extensionality; intros msg.
      repeat f_equal.
      { instantiate (1:= HOStateI); reflexivity. }
      { instantiate (1:= HORqI _); reflexivity. }
      { instantiate (1:= HMsgsOutI [_]).
        simpl; repeat f_equal.
        instantiate (1:= HIdm _ _).
        simpl; repeat f_equal.
        { instantiate (1:= HConst _ (HConstIdx _ hcfg_midx_deg _)); reflexivity. }
        { cbv [rsMsg miv_id miv_value].
          instantiate (1:= HMsgB _ _ _).
          simpl; f_equal.
          { instantiate (1:= HConst _ (HConstIdx _ hcfg_msg_id_deg _)); reflexivity. }
          { instantiate (1:= HConst _ (HConstBool _)); reflexivity. }
          { instantiate (1:= HOstVal _ val HValue eq_refl); reflexivity. }
        }
      }
  Defined.

End Tests.

