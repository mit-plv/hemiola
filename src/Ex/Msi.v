Require Import Bool Vector List String Peano_dec Lia.
Require Import Common FMap HVector ListSupport.

Require Import Ex.Spec.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

(** Message Ids *)

Definition msiRqS: IdxT := 0~>2.
Definition msiRsS: IdxT := 0~>3.
Definition msiDownRqS: IdxT := 0~>5.
Definition msiDownRsS: IdxT := 0~>6.

Definition msiRqM: IdxT := 1~>2.
Definition msiRsM: IdxT := 1~>3.
Definition msiDownRqIS: IdxT := 1~>4.
Definition msiDownRsIS: IdxT := 1~>5.
Definition msiDownRqIM: IdxT := 1~>6.
Definition msiDownRsIM: IdxT := 1~>7.

Definition msiInvRq: IdxT := 2~>4.
Definition msiInvWRq: IdxT := 2~>5.
Definition msiInvRs: IdxT := 2~>6.

(* Only used in inclusive cache-coherence protocols *)
Definition msiBInvRq: IdxT := 3~>0.
Definition msiBInvRs: IdxT := 3~>1.

(** Cache Status *)

Notation MSI := nat (only parsing).
Definition msiM: MSI := 3.
Definition msiS: MSI := 2.
Definition msiI: MSI := 1.
Definition msiNP: MSI := 0. (* Not Present *)

Section Invalidate.
  Definition invalidate (st: MSI) :=
    if eq_nat_dec st msiNP then msiNP else msiI.

  Lemma invalidate_sound:
    forall st, invalidate st <= msiI.
  Proof. unfold invalidate; cbv; intros; find_if_inside; lia. Qed.

  Lemma invalidate_I:
    forall st, msiI <= st -> invalidate st = msiI.
  Proof. unfold invalidate; cbv; intros; find_if_inside; lia. Qed.

  Lemma invalidate_NP:
    forall st, st = msiNP -> invalidate st = msiNP.
  Proof. unfold invalidate; cbv; intros; find_if_inside; lia. Qed.
End Invalidate.

Hint Resolve invalidate_sound.

Ltac solve_msi :=
  unfold msiM, msiS, msiI, msiNP in *; solve [auto|lia].

Definition val: Fin.t 4 := F1.
Definition owned: Fin.t 4 := F2.
Definition status: Fin.t 4 := F3.
Definition dir: Fin.t 4 := F4.

Section Directory.

  Record DirT: Set :=
    { dir_st: MSI; (* the summary status of children *)
      dir_excl: IdxT;
      dir_sharers: list IdxT
    }.

  Definition dirInit: DirT :=
    {| dir_st := msiI;
       dir_excl := ii;
       dir_sharers := nil |}.

  Import CaseNotations.
  Definition getDir (oidx: IdxT) (dir: DirT): MSI :=
    match case dir.(dir_st) on eq_nat_dec default msiI with
    | msiM: if idx_dec oidx dir.(dir_excl) then msiM else msiI
    | msiS: if in_dec idx_dec oidx dir.(dir_sharers)
            then msiS else msiI
    end.

  Definition setDirM (oidx: IdxT) :=
    {| dir_st := msiM;
       dir_excl := oidx;
       dir_sharers := nil |}.

  Definition setDirS (oinds: list IdxT) :=
    {| dir_st := msiS;
       dir_excl := 0;
       dir_sharers := oinds |}.

  Definition setDirI :=
    {| dir_st := msiI;
       dir_excl := 0;
       dir_sharers := nil |}.

  Definition addSharer (oidx: IdxT) (dir: DirT): DirT :=
    {| dir_st := msiS;
       dir_excl := dir.(dir_excl);
       dir_sharers :=
         if eq_nat_dec dir.(dir_st) msiS
         then oidx :: dir.(dir_sharers) else [oidx] |}.

  Definition removeSharer (oidx: IdxT) (dir: DirT): DirT :=
    {| dir_st := msiS;
       dir_excl := dir.(dir_excl);
       dir_sharers := removeOnce idx_dec oidx dir.(dir_sharers) |}.

  Definition LastSharer (dir: DirT) (cidx: IdxT) :=
    dir.(dir_sharers) = [cidx].

  Definition NotLastSharer (dir: DirT) :=
    2 <= List.length dir.(dir_sharers).

  Definition OtherSharerExists (dir: DirT) (cidx: IdxT) :=
    remove idx_dec cidx dir.(dir_sharers) <> nil.

  Section Facts.

    Ltac dir_crush :=
      cbv [getDir addSharer removeSharer
                  setDirI setDirS setDirM];
      simpl; intros;
      repeat find_if_inside;
      repeat
        (try match goal with
             | [H: ~ In ?oidx (?oidx :: _) |- _] => elim H; left; reflexivity
             | [Ht: In ?oidx ?l, Hn: ~ In ?oidx (_ :: ?l) |- _] => elim Hn; right; assumption
             | [H: In _ (_ :: _) |- _] => inv H
             | [H: _ |- _] => exfalso; auto; fail
             end; try subst; try reflexivity; try assumption; try solve_msi).

    Lemma getDir_M_imp:
      forall oidx dir,
        getDir oidx dir = msiM ->
        dir.(dir_st) = msiM /\ dir.(dir_excl) = oidx.
    Proof.
      unfold getDir, caseDec; intros.
      find_if_inside; [find_if_inside; [auto|discriminate]|].
      repeat (find_if_inside; [find_if_inside; discriminate|]).
      discriminate.
    Qed.

    Lemma getDir_S_imp:
      forall oidx dir,
        getDir oidx dir = msiS ->
        dir.(dir_st) = msiS /\ In oidx dir.(dir_sharers).
    Proof.
      unfold getDir, caseDec; intros.
      repeat (find_if_inside; [find_if_inside; discriminate|]).
      find_if_inside; [find_if_inside; [auto|discriminate]|].
      discriminate.
    Qed.

    Lemma getDir_addSharer_spec:
      forall dir,
        dir.(dir_st) <= msiS ->
        forall oidx sidx,
          getDir oidx (addSharer sidx dir) =
          if idx_dec sidx oidx
          then msiS else getDir oidx dir.
    Proof. dir_crush. Qed.

    Lemma getDir_removeSharer_sound:
      forall oidx sidx dir,
        getDir oidx (removeSharer sidx dir) <= msiS.
    Proof. dir_crush. Qed.

    Lemma getDir_removeSharer_neq:
      forall oidx sidx dir,
        getDir sidx dir = msiS ->
        oidx <> sidx ->
        getDir oidx (removeSharer sidx dir) = getDir oidx dir.
    Proof.
      dir_crush.
      - exfalso; apply removeOnce_In_2 in i; auto.
      - exfalso; elim n.
        apply removeOnce_In_1; assumption.
    Qed.

    Lemma getDir_LastSharer_eq:
      forall sidx dir,
        dir_st dir = msiS ->
        LastSharer dir sidx ->
        getDir sidx dir = msiS.
    Proof.
      unfold LastSharer; dir_crush.
      rewrite H0 in *; firstorder idtac.
    Qed.

    Lemma getDir_LastSharer_neq:
      forall oidx sidx dir,
        getDir sidx dir = msiS ->
        LastSharer dir sidx -> oidx <> sidx ->
        getDir oidx dir = msiI.
    Proof.
      unfold LastSharer; dir_crush.
      rewrite H0 in *; dest_in; exfalso; auto.
    Qed.

    Lemma getDir_S_sharer:
      forall dir,
        dir.(dir_st) = msiS ->
        forall oidx,
          In oidx dir.(dir_sharers) ->
          getDir oidx dir = msiS.
    Proof. dir_crush. Qed.

    Lemma getDir_S_non_sharer:
      forall dir,
        dir.(dir_st) = msiS ->
        forall oidx,
          ~ In oidx dir.(dir_sharers) ->
          getDir oidx dir = msiI.
    Proof. dir_crush. Qed.

    Lemma getDir_st_I:
      forall dir,
        dir.(dir_st) = msiI ->
        forall oidx, getDir oidx dir = msiI.
    Proof. dir_crush. Qed.

    Lemma getDir_st_sound:
      forall dir oidx,
        msiS <= getDir oidx dir ->
        getDir oidx dir <= dir.(dir_st).
    Proof. dir_crush. Qed.

    Lemma getDir_setDirI:
      forall oidx, getDir oidx setDirI = msiI.
    Proof. dir_crush. Qed.

    Lemma getDir_setDirS_I_imp:
      forall oidx shs, getDir oidx (setDirS shs) = msiI -> ~ In oidx shs.
    Proof. dir_crush. Qed.

    Lemma getDir_setDirS_S_imp:
      forall oidx shs, getDir oidx (setDirS shs) = msiS -> In oidx shs.
    Proof. dir_crush. Qed.

    Lemma getDir_setDirS_sound:
      forall oidx shs, getDir oidx (setDirS shs) <= msiS.
    Proof. dir_crush. Qed.

    Lemma getDir_setDirS_in:
      forall oidx shs, In oidx shs -> getDir oidx (setDirS shs) = msiS.
    Proof. dir_crush. Qed.

    Lemma getDir_setDirS_not_in:
      forall oidx shs, ~ In oidx shs -> getDir oidx (setDirS shs) = msiI.
    Proof. dir_crush. Qed.

    Lemma getDir_setDirS_eq:
      forall oidx, getDir oidx (setDirS [oidx]) = msiS.
    Proof. dir_crush. Qed.

    Lemma getDir_setDirM_eq:
      forall oidx, getDir oidx (setDirM oidx) = msiM.
    Proof. dir_crush. Qed.

    Lemma getDir_setDirM_neq:
      forall oidx eidx, eidx <> oidx -> getDir oidx (setDirM eidx) = msiI.
    Proof. dir_crush. Qed.

    Lemma getDir_excl_eq:
      forall dir eidx,
        eidx = dir.(dir_excl) ->
        dir.(dir_st) = msiM ->
        getDir eidx dir = dir.(dir_st).
    Proof. dir_crush. Qed.

    Lemma getDir_excl_neq:
      forall dir eidx,
        eidx = dir.(dir_excl) ->
        dir.(dir_st) = msiM ->
        forall oidx,
          oidx <> eidx ->
          getDir oidx dir = msiI.
    Proof. dir_crush. Qed.

  End Facts.

End Directory.
