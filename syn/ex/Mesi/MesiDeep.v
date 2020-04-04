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
Lemma or_iff_sep: forall A B C D, (A <-> B) -> (C <-> D) -> (A \/ C <-> B \/ D).
Proof. firstorder. Qed.

Lemma eq_iff_sep: forall (A B C D: Type), A = B -> C = D -> (A = C <-> B = D).
Proof. intuition congruence. Qed.
Lemma lt_iff_sep: forall A B C D, A = B -> C = D -> (A < C <-> B < D).
Proof. firstorder. Qed.
Lemma le_iff_sep: forall A B C D, A = B -> C = D -> (A <= C <-> B <= D).
Proof. firstorder. Qed.
Lemma gt_iff_sep: forall A B C D, A = B -> C = D -> (A > C <-> B > D).
Proof. firstorder. Qed.
Lemma ge_iff_sep: forall A B C D, A = B -> C = D -> (A >= C <-> B >= D).
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


Ltac reify_MsgFrom t :=
  match t with
  | MsgsFrom [?midx] _ _ _ =>
    match midx with
    | rqUpFrom (l1ExtOf _) => constr:(HMsgFromExt midx)
    | downTo _ => constr:(HMsgFromParent)
    | _ => constr:(HMsgFromChild midx)
    end
  end.

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
    | IdxT => instantiate (1:= HBConstIdx _ _); reflexivity
    end
  end.

Ltac renote_bexp :=
  repeat
    (cbv [rqMsg rsMsg miv_id miv_value];
     try match goal with
         | |- interpBExp _ _ = ?t =>
           match t with
           | hvec_ith _ ?i => instantiate (1:= HOstVal _ i eq_refl); reflexivity
           | {| msg_id := _ |} => instantiate (1:= HMsgB _ _ _); simpl; f_equal
           | _ => is_const t; instantiate (1:= HBConst _ _); simpl; renote_const
           | _ => instantiate (1:= HVar _ _ _); reflexivity
           end
         end).

Ltac renote_exp :=
  match goal with
  | |- interpExp _ _ _ _ = _ =>
    instantiate (1:= HBExp _); simpl; renote_bexp; fail
  | |- interpExp _ _ _ _ = _ => idtac "FIXME: need [renote_eexp]"
  end.

Ltac renote_OPrecP :=
  repeat
    match goal with
    | |- interpOPrecP _ _ _ _ <-> ?t =>
      match t with
      | _ /\ _ => instantiate (1:= HAnd _ _); simpl; apply and_iff_sep
      | _ \/ _ => instantiate (1:= HAnd _ _); simpl; apply or_iff_sep
      | _ = true => instantiate (1:= HBoolT _); simpl; apply eq_iff_sep;
                    [renote_exp|reflexivity]
      | _ = false => instantiate (1:= HBoolF _); simpl; apply eq_iff_sep;
                     [renote_exp|reflexivity]
      | _ < _ => instantiate (1:= HNatLt (w:= _) _ _); simpl; apply lt_iff_sep; renote_exp
      | _ <= _ => instantiate (1:= HNatLe (w:= _) _ _); simpl; apply le_iff_sep; renote_exp
      | _ > _ => instantiate (1:= HNatGt (w:= _) _ _); simpl; apply gt_iff_sep; renote_exp
      | _ >= _ => instantiate (1:= HNatGe (w:= _) _ _); simpl; apply ge_iff_sep; renote_exp
      | _ => idtac "FIXME:"
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
  end.

Ltac renote_OState :=
  repeat
    match goal with
    | |- interpOState _ _ _ _ = ?t =>
      match t with
      | hvec_upd _ _ _ => idtac "FIXME: [renote_OState] :: update"
      | _ => instantiate (1:= HOStateI _); reflexivity
      end
    end.

Ltac renote_ORq :=
  match goal with
  | |- interpORq _ _ _ _ = ?t =>
    match t with
    | addRq _ upRq _ _ _ =>
      instantiate (1:= HUpdUpLock _ _ _); simpl; repeat f_equal; renote_exp
    | addRqS _ upRq _ =>
      instantiate (1:= HUpdUpLockS _); simpl; repeat f_equal; renote_exp
    | removeRq _ upRq => instantiate (1:= HRelUpLock _); reflexivity
    | addRq _ downRq _ _ _ =>
      instantiate (1:= HUpdDownLock _ _ _); simpl; repeat f_equal; renote_exp
    | addRqS _ downRq _ =>
      instantiate (1:= HUpdDownLockS _); simpl; repeat f_equal; renote_exp
    | removeRq _ downRq => instantiate (1:= HRelDownLock _); reflexivity
    | _ => instantiate (1:= HORqI _); reflexivity
    end
  end.

Ltac renote_MsgOuts :=
  match goal with
  | |- interpMsgOuts _ _ _ _ = ?t =>
    match t with
    | [(?midx, _)]%list =>
      match midx with
      | downTo (l1ExtOf _) =>
        instantiate (1:= HMsgOutExt _ _); simpl; repeat f_equal; renote_exp
      | _ => instantiate (1:= HMsgOutUp _ _); simpl; repeat f_equal; renote_exp
      end
    | _ => instantiate (1:= HMsgsOutDown _ _); simpl;
           idtac "FIXME: [renote_MsgOuts] :: HMsgsOutDown"
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
        + renote_MsgFrom.
        + renote_OPrec.

      - intros.
        repeat autounfold with MesiRules.
        cbv [immDownRule rule_trs].
        renote_OTrs.
    Defined.

    Definition hl1GetSRqUpUp: HRule (l1GetSRqUpUp oidx (l1ExtOf oidx)).
    Proof.
      refine {| hrule_msg_from := _ |}.

      - intros; repeat autounfold with MesiRules.
        cbv [rqUpUpRule rule_precond].
        apply and_iff_sep.
        + renote_MsgFrom.
        + renote_OPrec.

      - intros.
        repeat autounfold with MesiRules.
        cbv [rqUpUpRule rule_trs].
        renote_OTrs.

        + instantiate (1:= HBExp _); simpl.
          (* [is_const] fails with [downTo oidx] *)
          instantiate (1:= HBConst _ (HBConstIdx _ _)); reflexivity.
        + instantiate (1:= HBExp _); simpl.
          (* [is_const] fails with [downTo (l1ExtOf oidx)] *)
          instantiate (1:= HBConst _ (HBConstIdx _ _)); reflexivity.
        + instantiate (1:= HBExp _); simpl.
          renote_bexp.
          (* [is_const] fails with [0] *)
          instantiate (1:= HBConst _ (HBConstNat _ _)); reflexivity.
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

