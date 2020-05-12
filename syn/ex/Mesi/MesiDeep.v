Require Import List.

Require Import Compiler.Compiler.
Require Import Hemiola.Common Hemiola.Index Hemiola.HVector.
Require Import Hemiola.Ex.TopoTemplate Hemiola.Ex.RuleTemplate Hemiola.Ex.RuleTransform.
Require Import Hemiola.Ex.Mesi.Mesi Hemiola.Ex.Mesi.MesiImp.

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

(** * Configuration Instances *)
Existing Instance SpecInds.NatDecValue.
Existing Instance Mesi.ImplOStateIfc.

Definition HMesi := HNat 3.

Instance MesiHConfig: hconfig :=
  {| hcfg_msg_id_sz := (3, 2);
     hcfg_addr_sz := 32;
     hcfg_value_sz := 32;
     hcfg_children_max_pred := 1; (* #children = 2 *)
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
  | HDirGetSh: hexp_dir var (HEType HDir) ->
               hexp_dir var (HBType (HList HIdxO))
  | HDirRemoveSh: hexp_dir var (HBType (HList HIdxO)) ->
                  hbexp (bvar var) HIdxO ->
                  hexp_dir var (HBType (HList HIdxO))
  | HDirAddSharer: hbexp (bvar var) HIdxO ->
                   hexp_dir var (HEType HDir) ->
                   hexp_dir var (HEType HDir)
  | HDirRemoveSharer: hbexp (bvar var) HIdxO ->
                      hexp_dir var (HEType HDir) ->
                      hexp_dir var (HEType HDir)
  | HDirSetM: hbexp (bvar var) HIdxO -> hexp_dir var (HEType HDir)
  | HDirSetE: hbexp (bvar var) HIdxO -> hexp_dir var (HEType HDir)
  | HDirSetS: list (hbexp (bvar var) HIdxO) -> hexp_dir var (HEType HDir)
  | HDirSetI: hexp_dir var (HEType HDir)
  | HRqUpFrom: hexp_dir var (HBType HIdxO) -> hexp_dir var (HBType HIdxQ)
  | HRsUpFrom: hexp_dir var (HBType HIdxO) -> hexp_dir var (HBType HIdxQ)
  | HDownTo: hexp_dir var (HBType HIdxO) -> hexp_dir var (HBType HIdxQ)
  | HRqUpFromM: hexp_dir var (HBType (HList HIdxO)) -> hexp_dir var (HBType (HList HIdxQ))
  | HRsUpFromM: hexp_dir var (HBType (HList HIdxO)) -> hexp_dir var (HBType (HList HIdxQ))
  | HDownToM: hexp_dir var (HBType (HList HIdxO)) -> hexp_dir var (HBType (HList HIdxQ))
  | HSingleton: hexp_dir var (HBType HIdxQ) -> hexp_dir var (HBType (HList HIdxQ))
  | HInvalidate: hbexp (bvar var) (HNat 3) -> hexp_dir var (HBType (HNat 3)).

  Fixpoint interp_hexp_dir ht (he: hexp_dir htypeDenote ht)
           (ost: OState) (orq: ORq Msg) (mins: list (Id Msg)): htypeDenote ht :=
    match he in (hexp_dir _ h) return (htypeDenote h) with
    | HDirC _ => (ost#[dir])%hvec
    | HDirGetSt dir => dir_st (interp_hexp_dir dir ost orq mins)
    | HDirGetExcl dir => dir_excl (interp_hexp_dir dir ost orq mins)
    | HDirGetSh dir => dir_sharers (interp_hexp_dir dir ost orq mins)
    | HDirRemoveSh sh cidx => remove idx_dec (interpBExp ost orq cidx)
                                     (interp_hexp_dir sh ost orq mins)
    | HDirGetStO oidx dir => getDir (interpBExp ost orq oidx) (interp_hexp_dir dir ost orq mins)
    | HDirAddSharer oidx dir =>
      addSharer (interpBExp ost orq oidx) (interp_hexp_dir dir ost orq mins)
    | HDirRemoveSharer oidx dir =>
      removeSharer (interpBExp ost orq oidx) (interp_hexp_dir dir ost orq mins)
    | HDirSetM oidx => setDirM (interpBExp ost orq oidx)
    | HDirSetE oidx => setDirE (interpBExp ost orq oidx)
    | HDirSetS oinds => setDirS (map (interpBExp ost orq) oinds)
    | HDirSetI _ => setDirI
    | HRqUpFrom oidx => rqUpFrom (interp_hexp_dir oidx ost orq mins)
    | HRsUpFrom oidx => rsUpFrom (interp_hexp_dir oidx ost orq mins)
    | HDownTo oidx => downTo (interp_hexp_dir oidx ost orq mins)
    | HRqUpFromM oinds => map rqUpFrom (interp_hexp_dir oinds ost orq mins)
    | HRsUpFromM oinds => map rsUpFrom (interp_hexp_dir oinds ost orq mins)
    | HDownToM oinds => map downTo (interp_hexp_dir oinds ost orq mins)
    | HSingleton she => [interp_hexp_dir she ost orq mins]%list
    | HInvalidate st => invalidate (interpBExp ost orq st)
    end.

  Inductive OPrecDir (var: htype -> Type): Type :=
  | DirLastSharer: hbexp (bvar var) HIdxO -> OPrecDir var
  | DirNotLastSharer
  | DirOtherSharerExists: hbexp (bvar var) HIdxO -> OPrecDir var.

  Definition interp_OPrecDir (pd: OPrecDir htypeDenote)
             (ost: OState) (orq: ORq Msg) (mins: list (Id Msg)): Prop :=
    match pd with
    | DirLastSharer cidx => LastSharer (ost#[dir])%hvec (interpBExp ost orq cidx)
    | DirNotLastSharer _ => NotLastSharer (ost#[dir])%hvec
    | DirOtherSharerExists cidx => OtherSharerExists (ost#[dir])%hvec (interpBExp ost orq cidx)
    end.

  Instance DirExtExp: ExtExp :=
    {| heexp := hexp_dir;
       interp_heexp := interp_hexp_dir;
       heoprec := OPrecDir;
       interp_heoprec := interp_OPrecDir
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
        instantiate (1:= HEExp _ (HDownToM _)); simpl; rewrite map_map; simpl;
        f_equal; [apply functional_extensionality; intros; f_equal; renote_exp|renote_eexp]
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

(* Specific to the MESI protocol *)
Ltac renote_eexp_dir :=
  repeat
    match goal with
    | |- interp_hexp_dir _ _ _ _ = ?t =>
      match t with
      | hvec_ith _ dir => instantiate (1:= HDirC _); reflexivity
      | dir_st _ => instantiate (1:= HDirGetSt _); simpl; f_equal
      | dir_excl _ => instantiate (1:= HDirGetExcl _); simpl; f_equal
      | dir_sharers _ => instantiate (1:= HDirGetSh _); simpl; f_equal
      | remove _ _ _ => instantiate (1:= HDirRemoveSh _ _); simpl; f_equal; [renote_bexp|]
      | getDir _ _ => instantiate (1:= HDirGetStO _ _); simpl; f_equal; [renote_bexp|]
      | addSharer _ _ =>
        instantiate (1:= HDirAddSharer _ _); simpl; f_equal; [renote_bexp|]
      | removeSharer _ _ =>
        instantiate (1:= HDirRemoveSharer _ _); simpl; f_equal; [renote_bexp|]
      | setDirM _ => instantiate (1:= HDirSetM _); simpl; f_equal; renote_bexp
      | setDirE _ => instantiate (1:= HDirSetE _); simpl; f_equal; renote_bexp
      | setDirS _ => instantiate (1:= HDirSetS _); simpl; f_equal; renote_list_bexp
      | setDirI => instantiate (1:= HDirSetI _); reflexivity
      | rqUpFrom _ => instantiate (1:= HRqUpFrom _); simpl; f_equal
      | rsUpFrom _ => instantiate (1:= HRsUpFrom _); simpl; f_equal
      | downTo _ => instantiate (1:= HDownTo _); simpl; f_equal
      | map rqUpFrom _ => instantiate (1:= HRqUpFromM _); simpl; f_equal
      | map rsUpFrom _ => instantiate (1:= HRsUpFromM _); simpl; f_equal
      | map downTo _ => instantiate (1:= HDownToM _); simpl; f_equal
      | [_]%list => instantiate (1:= HSingleton _); simpl; f_equal
      | invalidate _ => instantiate (1:= HInvalidate _); simpl; f_equal; renote_bexp
      end
    end.
Ltac renote_eexp ::= renote_eexp_dir.

Ltac renote_OPrec_dir :=
  match goal with
  | |- interp_OPrecDir _ _ _ _ <-> ?t =>
    match t with
    | NotLastSharer _ =>
      instantiate (1:= DirNotLastSharer _); simpl; apply iff_refl
    | LastSharer _ _ =>
      instantiate (1:= DirLastSharer _); simpl; apply p_f_equal; renote_bexp
    | OtherSharerExists _ _ =>
      instantiate (1:= DirOtherSharerExists _); simpl; apply p_f_equal; renote_bexp
    end
  end.
Ltac renote_OPrec_ext ::= renote_OPrec_dir.

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
      all: idtac "Reifying the L1 cache..".
    Time Defined. (* takes ~30 seconds *)

    Definition hli: HObject (MesiImp.li tr oidx).
    Proof.
      refine {| hobj_rules_ok := _ |}.
      cbv [MesiImp.li obj_rules].
      repeat match goal with
             | |- map _ _ = (_ ++ _)%list =>
               instantiate (1:= (_ ++ _)%list); rewrite map_app; simpl; f_equal
             | |- map _ _ = (_ :: _)%list => instantiate (1:= (_ :: _)%list); simpl; f_equal
             | |- map _ _ = nil => instantiate (1:= nil); reflexivity
             end.

      1: {
        cbv [liRulesFromChildren].
        instantiate (1:= concat _).
        rewrite concat_map, map_map; do 2 f_equal.
        apply functional_extensionality; intros cidx.
        instantiate (1:= fun cidx => _); simpl.

        cbv [liRulesFromChild]; simpl.
        repeat match goal with
               | |- map _ _ = (_ :: _)%list => instantiate (1:= (_ :: _)%list); simpl; f_equal
               | |- map _ _ = nil => instantiate (1:= nil); reflexivity
               end.
        all: instantiate (1:= existT _ _ _); reflexivity.
      }

      all: instantiate (1:= existT _ _ _); reflexivity.

      Unshelve.
      all: cbv beta; try (⇑rule; fail).
      all: try (⇑rule; instantiate (1:= HBConst _ _); simpl; renote_const; fail).
      all: idtac "Reifying the Li cache..".
    Time Defined. (* takes ~4 minutes *)

    Definition hmem: HObject (MesiImp.mem tr oidx).
    Proof.
      refine {| hobj_rules_ok := _ |}.
      cbv [MesiImp.mem obj_rules].
      repeat match goal with
             | |- map _ _ = (_ ++ _)%list =>
               instantiate (1:= (_ ++ _)%list); rewrite map_app; simpl; f_equal
             | |- map _ _ = (_ :: _)%list => instantiate (1:= (_ :: _)%list); simpl; f_equal
             | |- map _ _ = nil => instantiate (1:= nil); reflexivity
             end.

      1: {
        cbv [memRulesFromChildren].
        instantiate (1:= concat _).
        rewrite concat_map, map_map; do 2 f_equal.
        apply functional_extensionality; intros cidx.
        instantiate (1:= fun cidx => _); simpl.

        cbv [memRulesFromChild]; simpl.
        repeat match goal with
               | |- map _ _ = (_ :: _)%list => instantiate (1:= (_ :: _)%list); simpl; f_equal
               | |- map _ _ = nil => instantiate (1:= nil); reflexivity
               end.
        all: instantiate (1:= existT _ _ _); reflexivity.
      }

      all: instantiate (1:= existT _ _ _); reflexivity.

      Unshelve.
      all: cbv beta; try (⇑rule; fail).
      all: try (⇑rule; instantiate (1:= HBConst _ _); simpl; renote_const; fail).
      all: idtac "Reifying the main memory..".
    Time Defined. (* takes ~90 seconds *)

  End Object.

  Definition himpl: HSystem (MesiImp.impl Htr).
  Proof.
    refine {| hsys_objs_ok := _ |}.
    cbv [MesiImp.impl sys_objs].
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

      all: idtac "Reifying the entire memory subsystem..".
  Time Defined.

End Deep.
