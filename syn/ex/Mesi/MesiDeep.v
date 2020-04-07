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
  | HDirGetSt: hexp_dir var (HEType HDir) ->
               hexp_dir var (HBType (HNat 3))
  | HDirGetExcl: hexp_dir var (HEType HDir) ->
                 hexp_dir var (HBType HIdxO)
  | HDirGetStO: hbexp (bvar var) HIdxO ->
                hexp_dir var (HEType HDir) ->
                hexp_dir var (HBType (HNat 3))
  | HDirAddSharer: hbexp (bvar var) HIdxO ->
                   hexp_dir var (HEType HDir) ->
                   hexp_dir var (HEType HDir)
  | HDirRemoveSharer: hbexp (bvar var) HIdxO ->
                      hexp_dir var (HEType HDir) ->
                      hexp_dir var (HEType HDir)
  | HDirSetM: hbexp (bvar var) HIdxO -> hexp_dir var (HEType HDir)
  | HDirSetE: hbexp (bvar var) HIdxO -> hexp_dir var (HEType HDir)
  | HDirSetS: list (hbexp (bvar var) HIdxO) -> hexp_dir var (HEType HDir)
  | HDirSetI: hexp_dir var (HEType HDir).

  Fixpoint interp_hexp_dir (ost: OState) (orq: ORq Msg) (mins: list (Id Msg))
           {ht} (he: hexp_dir htypeDenote ht): htypeDenote ht :=
    match he in (hexp_dir _ h) return (htypeDenote h) with
    | HDirC _ => (ost#[dir])%hvec
    | HDirGetSt dir => dir_st (interp_hexp_dir ost orq mins dir)
    | HDirGetExcl dir => dir_excl (interp_hexp_dir ost orq mins dir)
    | HDirGetStO oidx dir => getDir (interpBExp ost oidx) (interp_hexp_dir ost orq mins dir)
    | HDirAddSharer oidx dir =>
      addSharer (interpBExp ost oidx) (interp_hexp_dir ost orq mins dir)
    | HDirRemoveSharer oidx dir =>
      removeSharer (interpBExp ost oidx) (interp_hexp_dir ost orq mins dir)
    | HDirSetM oidx => setDirM (interpBExp ost oidx)
    | HDirSetE oidx => setDirE (interpBExp ost oidx)
    | HDirSetS oinds => setDirS (map (interpBExp ost) oinds)
    | HDirSetI _ => setDirI
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
           | objIdxOf _ => instantiate (1:= HObjIdxOf _); simpl; f_equal
           | {| msg_id := _ |} => instantiate (1:= HMsgB _ _ _); simpl; f_equal
           | msg_id _ => instantiate (1:= HMsgId _); simpl; f_equal
           | msg_type _ => instantiate (1:= HMsgType _); simpl; f_equal
           | msg_value _ => instantiate (1:= HMsgValue _); simpl; f_equal
           | _ =>
             tryif is_var t then fail
             else (instantiate (1:= HBConst _ _); simpl; renote_const)
           | _ => instantiate (1:= HVar _ _ _); reflexivity
           end
         end).

Ltac renote_eexp := idtac "Error: redefine [renote_eexp]".

Ltac renote_exp :=
  match goal with
  | |- interpExp _ _ _ _ = _ =>
    instantiate (1:= HBExp _); simpl; renote_bexp; fail
  | |- interpExp _ _ _ _ = _ =>
    instantiate (1:= HEExp _ _); simpl; renote_eexp
  end.

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
  match goal with
  | |- interpORq _ _ _ _ = ?t =>
    match t with
    | addRq _ upRq _ _ _ =>
      instantiate (1:= HUpdUpLock _ _ _); simpl; repeat f_equal; renote_exp
    | addRqS _ upRq _ =>
      instantiate (1:= HUpdUpLockS _); simpl; repeat f_equal; renote_exp
    | removeRq _ upRq => instantiate (1:= HRelUpLock _); reflexivity
    | addRq _ downRq _ [_] _ =>
      instantiate (1:= HUpdDownLock _ [_] _); simpl; repeat f_equal; renote_exp
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
    | []%list => instantiate (1:= HMsgOutNil _); reflexivity
    | [(?midx, _)]%list =>
      match midx with
      | downTo (l1ExtOf _) =>
        instantiate (1:= HMsgOutExt _ _); simpl; repeat f_equal; renote_exp
      | _ => instantiate (1:= HMsgOutUp _ _); simpl; repeat f_equal; renote_exp
      | _ => instantiate (1:= HMsgsOutDown [_] _); simpl; repeat f_equal; renote_exp
      end
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
  cbv [rule_precond rule_trs].

Ltac renote_rule :=
  renote_rule_init;
  [apply and_iff_sep; [renote_MsgFrom|renote_OPrec]
  |renote_OTrs].

Tactic Notation "⇑rule" := renote_rule.

(* Specific to the MESI protocol *)
Ltac renote_eexp_dir :=
  repeat
    match goal with
    | |- interp_hexp_dir _ _ _ _ = ?t =>
      match t with
      | hvec_ith _ dir => instantiate (1:= HDirC _); reflexivity
      | dir_st _ => instantiate (1:= HDirGetSt _); simpl; f_equal
      | dir_excl _ => instantiate (1:= HDirGetExcl _); simpl; f_equal
      | getDir _ _ => instantiate (1:= HDirGetStO _ _); simpl; f_equal; [renote_bexp|]
      | addSharer _ _ =>
        instantiate (1:= HDirAddSharer _ _); simpl; f_equal; [renote_bexp|]
      | removeSharer _ _ =>
        instantiate (1:= HDirRemoveSharer _ _); simpl; f_equal; [renote_bexp|]
      | setDirM _ => instantiate (1:= HDirSetM _); simpl; f_equal; renote_bexp
      | setDirE _ => instantiate (1:= HDirSetE _); simpl; f_equal; renote_bexp
      | setDirS _ => instantiate (1:= HDirSetS _); simpl; f_equal;
                     idtac "FIXME: [renote_eexp_dir] :: setDirS"
      | setDirI => instantiate (1:= HDirSetI _); reflexivity
      end
    end.
Ltac renote_eexp ::= renote_eexp_dir.

Section Deep.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

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
      Unshelve.
      all: cbv beta.
      all: ⇑rule.
    Defined. (* takes ~30 seconds *)

    Definition hli: HObject (Mesi.li tr oidx).
    Proof.
      refine {| hobj_rules_ok := _ |}.
      cbv [li obj_rules].
      repeat match goal with
             | |- map _ _ = (_ ++ _)%list =>
               instantiate (1:= (_ ++ _)%list); rewrite map_app; simpl; f_equal
             | |- map _ _ = (_ :: _)%list => instantiate (1:= (_ :: _)%list); simpl; f_equal
             | |- map _ _ = nil => instantiate (1:= nil); reflexivity
             end.

      1: { cbv [liRulesFromChildren].
           admit.
      }

      all: instantiate (1:= existT _ _ _); reflexivity.

      Unshelve.
      1: admit.

      all: cbv beta.

      - ⇑rule.
      - ⇑rule.
      - admit. (* rsud *)
      - ⇑rule.
      - ⇑rule.
        + admit. (* [In _ (Topology.subtreeChildrenIndsOf _ _)] in precondition *)
        + admit. (* [rsUpFrom] exp *)
        + admit. (* [downTo] exp *)

      - admit. (* rsuu *)
      - ⇑rule.
      - admit. (* rsdrqd *)
      - admit. (* rsud *)
      - ⇑rule.
      - ⇑rule.
        + admit. (* [dir_sharers _ <> nil] in precondition *)
        + admit. (* [SubList (dir_sharers _)
                  *          (Topology.subtreeChildrenIndsOf _ _)] in precondition *)
        + instantiate (1:= HRet _ _ _); simpl; repeat f_equal.
          * renote_OState.
          * admit. (* [renote_ORq] :: addRq to sharers *)
          * admit. (* [renote_MsgOuts] :: msgs to sharers *)

      - admit. (* rqdd ditto *)
      - admit. (* rsuu *)
      - ⇑rule.
      - ⇑rule.
      - ⇑rule.
      - ⇑rule.
    Defined.

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

