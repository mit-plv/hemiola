Require Import List FunctionalExtensionality.

Require Import Compiler.HemiolaDeep.
Require Import Hemiola.Common Hemiola.Index Hemiola.HVector.
Require Import Hemiola.Syntax Hemiola.RqRsLang.
Require Import Hemiola.Ex.TopoTemplate Hemiola.Ex.RuleTemplate Hemiola.Ex.RuleTransform.
Require Import Hemiola.Ex.Mesi.Mesi Hemiola.Ex.Mesi.MesiImp.

Set Implicit Arguments.

(** * Configuration Instances *)

Existing Instance SpecInds.NatDecValue.
Existing Instance Mesi.ImplOStateIfc.

Definition HMesi := HNat 3.

Instance MesiHConfig: hconfig :=
  {| hcfg_msg_id_sz := (3, 2);
     hcfg_addr_sz := 64;
     hcfg_value_sz := 64;
     hcfg_children_max_pred := 3; (* max(#children) = 4 *)
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

(** Rebinding (instantiating) reification tactics for the MESI protocol *)

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
    | |- map _ (interp_hexp_dir _ _ _ _) = map _ _ =>
      instantiate (1:= HDownToM _); simpl; rewrite map_map; simpl;
      f_equal; [apply functional_extensionality; intros; f_equal; renote_exp|]
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

    Definition hmem: HObject (Mesi.mem tr oidx).
    Proof.
      refine {| hobj_rules_ok := _ |}.
      cbv [Mesi.mem obj_rules memRulesFromChildren].
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

      Unshelve.
      all: cbv beta; try (⇑rule; fail).
      all: try (⇑rule; instantiate (1:= HBConst _ _); simpl; renote_const; fail).
      all: idtac "Reifying the main memory..".
    Time Defined. (* takes ~15 seconds *)

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
  Defined.

  Goal True. idtac "Trying to get out of the section..". auto. Qed.
Time End Deep.
