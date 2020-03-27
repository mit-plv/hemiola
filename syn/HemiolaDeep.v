Require Import Hemiola.Common Hemiola.Index Hemiola.HVector.
Require Import Hemiola.Topology Hemiola.Syntax.
Require Import Hemiola.RqRsLang.
        
Set Implicit Arguments.

Definition TODO := cheat.

Import MonadNotations.

(** Configuration class *)

Class hconfig :=
  { hcfg_oidx_sz: nat;
    hcfg_midx_sz: nat;
    hcfg_msg_id_sz: nat;
    hcfg_value_sz: nat;
    hcfg_children_max_lg: nat
  }.

Section Reify.
  Context `{DecValue} `{OStateIfc} `{hconfig}.

  (** Reified syntax *)

  Inductive hbtype :=
  | HBool
  | HIdx (width: nat)
  | HNat (width: nat)
  | HValue
  | HMsg.

  Definition HIdxO := HIdx hcfg_oidx_sz.
  Definition HIdxQ := HIdx hcfg_midx_sz.
  Definition HIdxM := HIdx hcfg_msg_id_sz.

  Fixpoint hbtypeDenote (ht: hbtype): Type :=
    match ht with
    | HBool => bool
    | HIdx _ => IdxT
    | HNat _ => nat
    | HValue => t_type
    | HMsg => Msg
    end.

  Class HOStateIfc :=
    { host_ty: Vector.t (option hbtype) ost_sz;
      host_ty_ok:
        forall i: Fin.t ost_sz,
          match Vector.nth host_ty i with
          | Some hbt => Vector.nth ost_ty i = hbtypeDenote hbt
          | None => True
          end
    }.
  Context `{HOStateIfc}.

  Section Basis.
    Variable var: hbtype -> Type.

    (* -- basic constants and expressions *)

    Inductive hbconst: hbtype -> Type :=
    | HBConstBool: forall b: bool, hbconst HBool
    | HBConstNat: forall w (n: nat), hbconst (HNat w)
    | HBConstIdx: forall w (i: IdxT), hbconst (HIdx w).

    Inductive hbexp: hbtype -> Type :=
    | HBConst: forall ht (c: hbconst ht), hbexp ht
    | HVar: forall ht, var ht -> hbexp ht
    | HMsgB: hbexp HIdxM -> hbexp HBool -> hbexp HValue -> hbexp HMsg
    | HOstVal: forall i hbt, Vector.nth host_ty i = Some hbt -> hbexp hbt.

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

    Class ExtExp :=
      { heexp: (htype -> Type) -> htype -> Type;
        interp_heexp:
          OState -> ORq Msg -> list (Id Msg) ->
          forall {ht} (e: heexp htypeDenote ht), htypeDenote ht
      }.

    Section ExpExtended.
      Context `{ExtExp}.

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
        | HMsgFromChild (cmidx: IdxT): HMsgFrom
        | HMsgFromExt (emidx: IdxT): HMsgFrom.

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
        | HGetDownLockIdxBack: hbval HIdxQ.

        Inductive HOState :=
        | HOStateI: HOState
        | HOstUpdate:
            forall (i: Fin.t ost_sz) {ht},
              htypeDenote ht = Vector.nth ost_ty i ->
              hexp ht -> HOState -> HOState.
        
        Inductive HORq :=
        | HORqI: HORq
        | HUpdUpLock: hexp HMsg ->
                      hexp HIdxQ (* response-from *) ->
                      hexp HIdxQ (* response-back-to *) -> HORq
        | HUpdUpLockS: hexp HIdxQ (* response-from *) -> HORq
        | HRelUpLock: HORq
        | HUpdDownLock: hexp HMsg ->
                        list (hexp HIdxQ) (* responses-from *) ->
                        hexp HIdxQ (* response-back-to *) -> HORq
        | HUpdDownLockS: list (hexp HIdxQ) (* responses-from *) -> HORq
        | HRelDownLock.
        
        Inductive HMsgsOut :=
        | HMsgOutUp: IdxT (* midx *) -> hexp HMsg -> HMsgsOut
        | HMsgsOutDown: list (hexp HIdxQ) -> hexp HMsg -> HMsgsOut
        | HMsgOutExt: IdxT (* midx *) -> hexp HMsg -> HMsgsOut.

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
  Arguments HMsgB {var}.
  Arguments HOstVal {var}.
  Arguments HBExp {_ _} {var} {hbt}.
  Arguments HEExp {_ _} {var} {ht}.
  Arguments HORqI {_ _} {var}.
  Arguments HUpdUpLock {_ _} {var}.
  Arguments HUpdUpLockS {_ _} {var}.
  Arguments HRelUpLock {_ _} {var}.
  Arguments HUpdDownLock {_ _} {var}.
  Arguments HUpdDownLockS {_ _} {var}.
  Arguments HRelDownLock {_ _} {var}.
  Arguments HMsgOutUp {_ _} {var}.
  Arguments HMsgsOutDown {_ _} {var}.
  Arguments HMsgOutExt {_ _} {var}.
  Arguments HOPrecRqRs {_ _} {var}.

  (** Interpretation *)

  Definition interpConst {ht} (c: hbconst ht): hbtypeDenote ht :=
    match c with
    | HBConstBool b => b
    | HBConstNat _ n => n
    | HBConstIdx _ i => i
    end.

  Section InterpExtended.
    Context `{het: ExtType} `{@ExtExp het}.
    
    Section WithPreState.
      Variables (ost: OState) (orq: ORq Msg) (mins: list (Id Msg)).

      Lemma host_ty_ok_i:
        forall (i: Fin.t ost_sz) hbt,
          Vector.nth host_ty i = Some hbt ->
          Vector.nth ost_ty i = hbtypeDenote hbt.
      Proof.
        intros.
        pose proof (host_ty_ok i).
        rewrite H4 in H5.
        assumption.
      Qed.

      Fixpoint interpBExp {ht} (e: hbexp hbtypeDenote ht): hbtypeDenote ht :=
        match e with
        | HBConst _ c => interpConst c
        | HVar _ hv => hv
        | HMsgB mid mty mval =>
          {| msg_id := interpBExp mid;
             msg_type := interpBExp mty;
             msg_value := interpBExp mval |}
        | HOstVal i hbt Heq =>
          match host_ty_ok_i _ Heq with
          | eq_refl => (ost#[i])%hvec
          end
        end.

      Definition interpExp {ht} (e: hexp htypeDenote ht): htypeDenote ht :=
        match e with
        | HBExp hbe => interpBExp hbe
        | HEExp hee => interp_heexp ost orq mins hee
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
        | HMsgFromChild cmidx => MsgsFrom [cmidx] ost orq mins
        | HMsgFromExt emidx => MsgsFrom [emidx] ost orq mins
        end.

      Definition interpBindValue {bt} (bv: hbval bt)
        : option (htypeDenote (HBType bt)) :=
        match bv with
        | HGetFirstMsg => getFirstMsg mins
        | HGetUpLockMsg => getUpLockMsg orq
        | HGetDownLockMsg => getDownLockMsg orq
        | HGetUpLockIdxBack => getUpLockIdxBack orq
        | HGetDownLockIdxBack => getDownLockIdxBack orq
        end.

      Fixpoint interpOState (host: HOState htypeDenote): OState :=
        (match host with
         | HOStateI _ => ost
         | HOstUpdate i Heq hval host' =>
           (interpOState host') +#[i <- match Heq with
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
          addRq orq downRq (interpExp rq) (List.map interpExp rssf) (interpExp rsb)
        | HUpdDownLockS rssf => addRqS orq downRq (List.map interpExp rssf)
        | HRelDownLock => removeRq orq downRq
        end.

      Definition interpMsgOuts (houts: HMsgsOut htypeDenote): list (Id Msg) :=
        match houts with
        | HMsgOutUp midx msg => [(midx, interpExp msg)]
        | HMsgsOutDown minds msg =>
          List.map (fun midx => (interpExp midx, interpExp msg)) minds
        | HMsgOutExt midx msg => [(midx, interpExp msg)]
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
  Context `{dv: DecValue}
          `{oifc: OStateIfc}
          `{het: ExtType}
          `{ee: @ExtExp dv oifc het}
          `{hoifc: @HOStateIfc dv oifc}
          `{hconfig}.

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

Section Tests.

  Lemma abcd: forall A B C D, (A <-> B) -> (C <-> D) -> (A /\ C <-> B /\ D).
  Proof. firstorder. Qed.

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
    {| hcfg_oidx_sz := 5;
       hcfg_midx_sz := 8;
       hcfg_msg_id_sz := 5;
       hcfg_value_sz := 32;
       hcfg_children_max_lg := 2;
    |}.

  Existing Instance SpecInds.NatDecValue.
  Existing Instance Mesi.ImplOStateIfc.

  Definition HMesi := HNat 3.

  Instance MesiHOStateIfc: HOStateIfc :=
    {| host_ty := [Some HValue; Some HBool; Some HMesi; None]%vector;
       host_ty_ok := cheat _
    |}.

  Section DirExt.

    Inductive htype_dir: Set :=
    | HDir: htype_dir.

    Definition htypeDenote_dir (ht: htype_dir): Type :=
      match ht with
      | HDir => Mesi.DirT
      end.

    Instance DirExtType: ExtType :=
      {| hetype := htype_dir;
         hetypeDenote := htypeDenote_dir
      |}.

    Inductive hexp_dir (var: htype -> Type): htype -> Type :=
    | HDirC: hexp_dir var (HEType HDir)
    | HDirGet: hbexp (bvar var) HIdxO ->
               hexp_dir var (HEType HDir) ->
               hexp_dir var (HBType (HNat 3)).

    Fixpoint interp_hexp_dir (ost: OState) (orq: ORq Msg) (mins: list (Id Msg))
             {ht} (he: hexp_dir htypeDenote ht): htypeDenote ht :=
      match he in (hexp_dir _ h) return (htypeDenote h) with
      | HDirC _ => (ost#[dir])%hvec
      | HDirGet oidx dir => getDir (interpBExp ost oidx) (interp_hexp_dir ost orq mins dir)
      end.

    Instance DirExtExp: ExtExp :=
      {| heexp := hexp_dir;
         interp_heexp := interp_hexp_dir
      |}.

  End DirExt.

  Existing Instance DirExtType.
  Existing Instance DirExtExp.
  Definition hl1GetSImm: HRule (l1GetSImm (l1ExtOf oidx)).
  Proof.
    refine {| hrule_msg_from := _ |}.

    - intros.
      repeat autounfold with MesiRules.
      cbv [immDownRule].
      cbv [rule_precond].

      apply abcd.

      + cbv [interpMsgFrom].
        instantiate (1:= HMsgFromExt _).
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
        instantiate (1:= HNatLe (w:= 3) _ _); simpl.
        instantiate (2:= HBExp (HBConst _ (HBConstNat _ Mesi.mesiS))); simpl.
        instantiate (1:= HBExp (HOstVal _ status eq_refl)); simpl.
        setoid_rewrite <-eq_rect_eq.
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
      { instantiate (1:= HOStateI _); reflexivity. }
      { instantiate (1:= HORqI _); reflexivity. }
      { instantiate (1:= HMsgOutExt _ _).
        simpl; repeat f_equal.
        { cbv [rsMsg miv_id miv_value].
          instantiate (1:= HBExp (HMsgB _ _ _)).
          simpl; f_equal.
          { instantiate (1:= HBConst _ (HBConstIdx hcfg_msg_id_sz _)); reflexivity. }
          { instantiate (1:= HBConst _ (HBConstBool _)); reflexivity. }
          { instantiate (1:= HOstVal _ val eq_refl).
            simpl; setoid_rewrite <-eq_rect_eq.
            reflexivity.
          }
        }
      }
  Defined.

End Tests.

