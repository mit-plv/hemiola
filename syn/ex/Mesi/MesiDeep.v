Require Import List.

Require Import Compiler.Compiler.

Require Import Hemiola.Common Hemiola.Index Hemiola.HVector.
Require Import Hemiola.Ex.TopoTemplate Hemiola.Ex.RuleTemplate.
Require Import Hemiola.Ex.Mesi.Mesi.

Require Import FunctionalExtensionality.

Set Implicit Arguments.

(** * Utilities: move to somewhere else? *)

Lemma and_iff_sep: forall A B C D, (A <-> B) -> (C <-> D) -> (A /\ C <-> B /\ D).
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

(** * Configuration Instances *)
Existing Instance SpecInds.NatDecValue.
Existing Instance Mesi.ImplOStateIfc.

Definition HMesi := HNat 3.

Instance MesiHConfig: hconfig :=
  {| hcfg_oidx_sz := (2, 3);
     hcfg_midx_sz := (4, 4);
     hcfg_msg_id_sz := (3, 2);
     hcfg_value_sz := 32;
     hcfg_children_max_lg := 2;
  |}.

Instance HNatDecValue: HDecValue :=
  {| ht_value_ok := eq_refl |}.

Lemma MesiHOStateIfc_host_ty_ok:
  forall i: Fin.t ost_sz,
    match Vector.nth [Some hdv_type; Some HBool; Some HMesi; None]%vector i with
    | Some hbt => Vector.nth ost_ty i = hbtypeDenote hbt
    | None => True
    end.
Proof.
  intros.
  refine (match i with | Fin.F1 => _ | Fin.FS _ => _ end);
    [repeat (destruct n; [exact idProp|]);
     destruct n; [|exact idProp];
     reflexivity
    |repeat (destruct n; [exact idProp|]);
     destruct n; [|exact idProp]].
  refine (match t with | Fin.F1 => _ | Fin.FS _ => _ end);
    [repeat (destruct n; [exact idProp|]);
     destruct n; [|exact idProp];
     reflexivity
    |repeat (destruct n; [exact idProp|]);
     destruct n; [|exact idProp]].
  refine (match t0 with | Fin.F1 => _ | Fin.FS _ => _ end);
    [repeat (destruct n; [exact idProp|]);
     destruct n; [|exact idProp];
     reflexivity
    |repeat (destruct n; [exact idProp|]);
     destruct n; [|exact idProp]].
  refine (match t1 with | Fin.F1 => _ | Fin.FS _ => _ end);
    [repeat (destruct n; [exact idProp|]);
     destruct n; [|exact idProp];
     reflexivity
    |repeat (destruct n; [exact idProp|]);
     destruct n; [|exact idProp]].
  apply Fin.case0; assumption.
Defined.

Instance MesiHOStateIfc: HOStateIfc :=
  {| host_ty := [Some hdv_type; Some HBool; Some HMesi; None]%vector;
     host_ty_ok := MesiHOStateIfc_host_ty_ok;
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

Lemma MesiHOStateIfcFull_hostf_ty_compat:
  forall i hbt,
    host_ty[@i] = Some hbt ->
    [HBType hdv_type; HBType HBool; HBType HMesi; HEType HDir][@i] = HBType hbt.
Proof.
  intros i.
  refine (match i with | Fin.F1 => _ | Fin.FS _ => _ end);
    [repeat (destruct n; [exact idProp|]);
     destruct n; [|exact idProp];
     simpl; intros; congruence
    |repeat (destruct n; [exact idProp|]);
     destruct n; [|exact idProp]].
  refine (match t with | Fin.F1 => _ | Fin.FS _ => _ end);
    [repeat (destruct n; [exact idProp|]);
     destruct n; [|exact idProp];
     simpl; intros; congruence
    |repeat (destruct n; [exact idProp|]);
     destruct n; [|exact idProp]].
  refine (match t0 with | Fin.F1 => _ | Fin.FS _ => _ end);
    [repeat (destruct n; [exact idProp|]);
     destruct n; [|exact idProp];
     simpl; intros; congruence
    |repeat (destruct n; [exact idProp|]);
     destruct n; [|exact idProp]].
  refine (match t1 with | Fin.F1 => _ | Fin.FS _ => _ end);
    [repeat (destruct n; [exact idProp|]);
     destruct n; [|exact idProp];
     simpl; intros; congruence
    |repeat (destruct n; [exact idProp|]);
     destruct n; [|exact idProp]].
  apply Fin.case0; assumption.
Defined.

Instance MesiHOStateIfcFull: HOStateIfcFull :=
  {| hostf_ty := [HBType hdv_type; HBType HBool; HBType HMesi; HEType HDir];
     hostf_ty_ok := eq_refl;
     hostf_ty_compat := MesiHOStateIfcFull_hostf_ty_compat;
  |}.

(** * Reification *)

Section Deep.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Section L1Rules.
    Variable oidx: IdxT.
    
    Definition hl1GetSImm: HRule (l1GetSImm (l1ExtOf oidx)).
    Proof.
      refine {| hrule_msg_from := _ |}.

      - intros; repeat autounfold with MesiRules.
        cbv [immDownRule rule_precond].
        apply and_iff_sep.
        + cbv [interpMsgFrom].
          instantiate (1:= HMsgFromExt _).
          apply iff_refl.

        + instantiate (1:= fun var => HOPrecAnd (var:= var) _ _); simpl; apply and_iff_sep.
          all: repeat
                 match goal with
                 | |- _ <-> (_ /\oprec _) _ _ _ =>
                   instantiate (1:= HOPrecAnd _ _); simpl; apply and_iff_sep
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
          apply iff_refl.

      - intros.
        repeat autounfold with MesiRules.
        cbv [immDownRule rule_trs].

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
              reflexivity.
            }
          }
        }
    Defined.

    Definition hl1GetSRqUpUp: HRule (l1GetSRqUpUp oidx (l1ExtOf oidx)).
    Proof.
      refine {| hrule_msg_from := _ |}.

      - intros; repeat autounfold with MesiRules.
        cbv [rqUpUpRule rule_precond].
        apply and_iff_sep.
        + cbv [interpMsgFrom].
          instantiate (1:= HMsgFromExt _).
          apply iff_refl.

        + instantiate (1:= fun var => HOPrecAnd (var:= var) _ _); simpl; apply and_iff_sep.
          all: repeat
                 match goal with
                 | |- _ <-> (_ /\oprec _) _ _ _ =>
                   instantiate (1:= HOPrecAnd _ _); simpl; apply and_iff_sep
                 end.

          1-3: instantiate (1:= HOPrecRqRs _ _); simpl.
          1-3: first [instantiate (1:= HRqAccepting); apply iff_refl; fail
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
          instantiate (1:= HBExp (HBConst _ (HBConstNat _ Mesi.mesiI))); simpl.
          instantiate (1:= HBExp (HOstVal _ status eq_refl)); simpl.
          apply iff_refl.

      - intros.
        repeat autounfold with MesiRules.
        cbv [rqUpUpRule rule_trs].

        instantiate (1:= HTrsMTrs (HMTrs _)); simpl.
        apply TrsMTrs_ext; intros.
        instantiate (1:= fun var => HBind (var:= var) _ _); simpl.
        instantiate (3:= HGetFirstMsg); simpl.
        instantiate (1:= fun msg => HRet _ _ _).
        simpl; repeat f_equal.
        apply functional_extensionality; intros msg.
        repeat f_equal.
        { instantiate (1:= HOStateI _); reflexivity. }
        { instantiate (1:= HUpdUpLock _ _ _).
          simpl; f_equal.
          { instantiate (1:= HBExp (HVar _ _ _)).
            simpl; reflexivity.
          }
          { instantiate (1:= HBExp (HBConst _ (HBConstIdx hcfg_midx_sz _))).
            simpl; reflexivity.
          }
          { instantiate (1:= HBExp (HBConst _ (HBConstIdx hcfg_midx_sz _))).
            simpl; reflexivity.
          }
        }
        { instantiate (1:= HMsgOutUp _ _).
          simpl; repeat f_equal.
          instantiate (1:= HBExp (HMsgB _ _ _)).
          cbv [rqMsg]; simpl; f_equal.
          { instantiate (1:= HBConst _ (HBConstIdx hcfg_msg_id_sz _)).
            simpl; reflexivity.
          }
          { instantiate (1:= HBConst _ (HBConstBool _)).
            simpl; reflexivity.
          }
          { instantiate (1:= HBConst _ (HBConstNat _ _)).
            simpl; reflexivity.
          }
        }
    Defined.

  End L1Rules.
    
  Section Object.
    Variable (oidx: IdxT).

    Definition hl1: HObject (Mesi.l1 oidx).
    Proof.
      refine {| hobj_rules_ok := _ |}.
      cbv [l1 obj_rules].
      repeat match goal with
             | |- map _ _ = (_ :: _)%list => instantiate (1:= (_ :: _)%list); simpl; f_equal
             | |- map _ _ = nil => instantiate (1:= nil); reflexivity
             end.
      all: instantiate (1:= existT _ _ _); reflexivity.

      Unshelve. all: cbv beta.
      1: exact (hl1GetSImm _).
      1: exact (hl1GetSRqUpUp _).
      all: apply TODO.
    Defined.
    
    Definition hli: HObject (Mesi.li tr oidx) := TODO _.
    Definition hmem: HObject (Mesi.mem tr oidx) := TODO _.

  End Object.
  
  Definition himpl: HSystem (Mesi.impl Htr).
  Proof.
    refine {| hsys_objs_ok := _ |}.
    cbv [impl sys_objs].
    instantiate (1:= (_ ++ _)%list); rewrite map_app; f_equal.

    - instantiate (1:= (_ :: _)%list); simpl; f_equal.
      + instantiate (1:= existT _ _ (hmem _)); reflexivity.
      + instantiate (1:= map (fun i => existT _ _ (hli i))
                             (tl (c_li_indices (snd (tree2Topo tr 0))))).
        rewrite map_map.
        reflexivity.

    - instantiate (1:= map (fun i => existT _ _ (hl1 i))
                           (c_l1_indices (snd (tree2Topo tr 0)))).
      rewrite map_map.
      reflexivity.
  Defined.

End Deep.

