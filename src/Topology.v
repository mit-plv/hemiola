Require Import Peano_dec List ListSupport.
Require Import Common FMap.

Set Implicit Arguments.

Open Scope list.

Section FindSome.
  Context {A B: Type}.
  Variable f: A -> option B.

  Fixpoint find_some (al: list A): option B :=
    match al with
    | nil => None
    | a :: al' =>
      match f a with
      | None => find_some al'
      | Some b => Some b
      end
    end.

  Lemma find_some_exist:
    forall al b,
      find_some al = Some b ->
      exists a,
        In a al /\ f a = Some b.
  Proof.
    induction al; simpl; intros; [discriminate|].
    destruct (f a) as [b'|] eqn:Ha.
    - inv H; eauto.
    - specialize (IHal _ H).
      destruct IHal as [a' [? ?]].
      exists a'; auto.
  Qed.

  Lemma find_some_not_None:
    forall a b al,
      In a al ->
      f a = Some b ->
      find_some al <> None.
  Proof.
    induction al; simpl; intros; [exfalso; auto|].
    destruct H; subst.
    - rewrite H0; discriminate.
    - destruct (f a0); [discriminate|auto].
  Qed.

End FindSome.

Section Collect.
  Context {A B: Type}.
  Variable f: A -> list B.

  Fixpoint collect (al: list A): list B :=
    match al with
    | nil => nil
    | a :: al' =>
      f a ++ collect al'
    end.

  Lemma collect_in:
    forall al a,
      In a al ->
      SubList (f a) (collect al).
  Proof.
    induction al; simpl; intros; [exfalso; auto|].
    destruct H; subst.
    - apply SubList_app_1, SubList_refl.
    - apply SubList_app_2; auto.
  Qed.

  Lemma collect_in_exist:
    forall al b,
      In b (collect al) ->
      exists a, In a al /\ In b (f a).
  Proof.
    induction al; simpl; intros; [exfalso; auto|].
    apply in_app_or in H; destruct H; eauto.
    specialize (IHal _ H).
    destruct IHal as [a' [? ?]].
    eauto.
  Qed.

End Collect.

(** The Coq standard library already has an equivalent definition [Exists]
 * but it does not guarantee termination when involved with mutually inductive
 * structures.
 *)
Section Exists.
  Context {A: Type}.
  Variable f: A -> Prop.

  Fixpoint Exists (al: list A): Prop :=
    match al with
    | nil => False
    | a :: al' =>
      f a \/ Exists al'
    end.

  Lemma exists_exists:
    forall al,
      Exists al ->
      exists a, In a al /\ f a.
  Proof.
    induction al; simpl; intros; [exfalso; auto|].
    destruct H; firstorder.
  Qed.

  Lemma exists_in:
    forall a al, In a al -> f a -> Exists al.
  Proof.
    induction al; simpl; intros; auto.
    destruct H; subst; auto.
  Qed.
  
End Exists.

Section DTree.

  Record dmc :=
    { dmc_me: IdxT;
      dmc_ups: list IdxT;
      dmc_downs: list IdxT
    }.

  Inductive DTree :=
  | DNode: dmc -> list DTree -> DTree.

  Fixpoint dtree_dec (dtr1 dtr2: DTree): {dtr1 = dtr2} + {dtr1 <> dtr2}.
  Proof.
    intros.
    decide equality.
    - apply (list_eq_dec dtree_dec).
    - decide equality.
      + apply (list_eq_dec eq_nat_dec).
      + apply (list_eq_dec eq_nat_dec).
      + apply eq_nat_dec.
  Defined.

  Section DTree_ind2.
    Variable P: DTree -> Prop.
    Hypotheses (H: forall i cs, Forall P cs -> P (DNode i cs)).

    Fixpoint DTree_ind2 (dtr: DTree): P dtr :=
      match dtr with
      | DNode i cs =>
        H i (list_ind
               (fun cs => Forall P cs)
               (Forall_nil _)
               (fun ic _ IH =>
                  Forall_cons ic (DTree_ind2 ic) IH) cs)
      end.
  End DTree_ind2.

  Definition rootOf (dtr: DTree): IdxT :=
    match dtr with
    | DNode root _ => root.(dmc_me)
    end.

  Definition dmcOf (dtr: DTree): dmc :=
    match dtr with
    | DNode root _ => root
    end.

  Definition childrenOf (dtr: DTree): list DTree :=
    match dtr with
    | DNode _ cs => cs
    end.

  Definition childrenIndsOf (dtr: DTree): list IdxT :=
    map rootOf (childrenOf dtr).

  Fixpoint parentOf (idx: IdxT) (dtr: DTree): option DTree :=
    match dtr with
    | DNode root cs =>
      if in_dec eq_nat_dec idx (map rootOf cs)
      then Some dtr
      else find_some (parentOf idx) cs
    end.

  Fixpoint indsOf (dtr: DTree): list IdxT :=
    match dtr with
    | DNode root cs =>
      root.(dmc_me) :: collect indsOf cs
    end.

  Fixpoint chnsOf (dtr: DTree): list IdxT :=
    match dtr with
    | DNode root cs =>
      (root.(dmc_ups) ++ root.(dmc_downs)) ++ collect chnsOf cs
    end.

  Fixpoint subtree (idx: IdxT) (dtr: DTree): option DTree :=
    match dtr with
    | DNode root cs =>
      if eq_nat_dec root.(dmc_me) idx
      then Some dtr
      else find_some (subtree idx) cs
    end.

  Fixpoint Subtree (str dtr: DTree): Prop :=
    str = dtr \/
    match dtr with
    | DNode root cs =>
      Exists (Subtree str) cs
    end.

  Definition subtreeIndsOf (dtr: DTree) (idx: IdxT): list IdxT :=
    (subtree idx dtr) >>=[nil] (fun tr => indsOf tr).

  Definition hasIdx (idx: IdxT) (dtr: DTree): option DTree :=
    if eq_nat_dec (rootOf dtr) idx
    then Some dtr
    else None.
  
  Fixpoint parentChnsOf (idx: IdxT) (dtr: DTree):
    option (dmc * IdxT (* parent index *)) :=
    match dtr with
    | DNode root cs =>
      match find_some (hasIdx idx) cs with
      | Some (DNode croot _) => Some (croot, root.(dmc_me))
      | None => find_some (parentChnsOf idx) cs
      end
    end.
  
  Definition upEdgesFrom (dtr: DTree) (idx: IdxT): list IdxT :=
    (parentChnsOf idx dtr) >>=[nil] (fun udp => dmc_ups (fst udp)).
  
  Definition downEdgesTo (dtr: DTree) (idx: IdxT): list IdxT :=
    (parentChnsOf idx dtr) >>=[nil] (fun udp => dmc_downs (fst udp)).

  Definition parentIdxOf (dtr: DTree) (idx: IdxT): option IdxT :=
    (parentChnsOf idx dtr) >>= (fun udp => Some (snd udp)).

  (** Well-formedness *)

  Definition UniqueInds (dtr: DTree): Prop :=
    NoDup (indsOf dtr).

  Definition UniqueChns (dtr: DTree): Prop :=
    NoDup (chnsOf dtr).

  Definition WfDTree (dtr: DTree): Prop :=
    UniqueInds dtr /\ UniqueChns dtr.
  
End DTree.

Section Facts.

  Ltac dtree_ind dtr :=
    let root := fresh "root" in
    let cs := fresh "cs" in
    induction dtr as [root cs] using DTree_ind2; simpl; intros.

  Ltac disc_find_some :=
    match goal with
    | [H: find_some _ _ = Some _ |- _] =>
      let ctr := fresh "ctr" in
      apply find_some_exist in H;
      destruct H as [ctr [? ?]]
    end.

  Ltac disc_exists :=
    match goal with
    | [H: Exists _ _ |- _] =>
      let ctr := fresh "ctr" in
      apply exists_exists in H;
      destruct H as [ctr ?]; dest
    end.

  Ltac disc_forall_in :=
    match goal with
    | [H1: Forall _ ?cs, H2: In _ ?cs |- _] =>
      let Hf := fresh "H" in
      pose proof H1 as Hf;
      rewrite Forall_forall in Hf;
      specialize (Hf _ H2)
    end.

  Lemma rootOf_dmcOf:
    forall dtr,
      rootOf dtr = dmc_me (dmcOf dtr).
  Proof.
    intros; destruct dtr; reflexivity.
  Qed.

  Lemma uniqueInds_child:
    forall root cs,
      UniqueInds (DNode root cs) ->
      forall ctr,
        In ctr cs ->
        UniqueInds ctr.
  Proof.
    unfold UniqueInds; intros.
    simpl in H.
    inv H.
    clear -H0 H4.
    induction cs; [inv H0|].
    destruct H0; subst.
    - eapply NoDup_app_weakening_1; eauto.
    - apply IHcs; auto.
      eapply NoDup_app_weakening_2; eauto.
  Qed.

  Lemma uniqueChns_child:
    forall root cs,
      UniqueChns (DNode root cs) ->
      forall ctr,
        In ctr cs ->
        UniqueChns ctr.
  Proof.
    unfold UniqueChns; intros.
    simpl in H.
    apply NoDup_app_weakening_2 in H.
    clear -H H0.
    induction cs; [inv H0|].
    destruct H0; subst.
    - eapply NoDup_app_weakening_1; eauto.
    - apply IHcs; auto.
      eapply NoDup_app_weakening_2; eauto.
  Qed.

  Lemma wfDTree_child:
    forall root cs,
      WfDTree (DNode root cs) ->
      forall ctr,
        In ctr cs ->
        WfDTree ctr.
  Proof.
    intros; destruct H; split.
    - eapply uniqueInds_child; eauto.
    - eapply uniqueChns_child; eauto.
  Qed.

  Lemma indsOf_self_in:
    forall dtr,
      In (rootOf dtr) (indsOf dtr).
  Proof.
    destruct dtr as [root cs]; simpl; auto.
  Qed.

  Lemma chnsOf_self_in:
    forall root cs,
      SubList (dmc_ups root ++ dmc_downs root)
              (chnsOf (DNode root cs)).
  Proof.
    intros; simpl.
    apply SubList_app_1, SubList_refl.
  Qed.

  Lemma childrenOf_indsOf:
    forall ctr dtr,
      In ctr (childrenOf dtr) ->
      SubList (indsOf ctr) (indsOf dtr).
  Proof.
    destruct dtr as [root cs]; simpl; intros.
    apply SubList_cons_right.
    apply collect_in; auto.
  Qed.

  Lemma parent_idx_not_in_children:
    forall dtr ctr,
      WfDTree dtr ->
      In ctr (childrenOf dtr) ->
      ~ In (rootOf dtr) (indsOf ctr).
  Proof.
    destruct dtr as [root cs]; intros.
    destruct H.
    red in H; simpl in H.
    inv H.
    intro Hx; elim H4.
    eapply collect_in; eauto.
  Qed.

  Lemma parent_idx_child_not_eq:
    forall dtr ctr,
      WfDTree dtr ->
      In ctr (childrenOf dtr) ->
      rootOf dtr <> rootOf ctr.
  Proof.
    intros; intro Hx.
    apply parent_idx_not_in_children in H0; [|eassumption].
    elim H0.
    rewrite Hx.
    apply indsOf_self_in.
  Qed.

  Lemma hasIdx_Some:
    forall idx dtr tr,
      hasIdx idx dtr = Some tr ->
      tr = dtr /\ rootOf dtr = idx.
  Proof.
    intros; unfold hasIdx in H.
    find_if_inside; [|discriminate].
    inv H; auto.
  Qed.

  Lemma subtree_rootOf:
    forall idx dtr str,
      subtree idx dtr = Some str ->
      rootOf str = idx.
  Proof.
    dtree_ind dtr; simpl; intros.
    find_if_inside.
    - inv H0; reflexivity.
    - disc_find_some.
      disc_forall_in.
      eauto.
  Qed.

  Lemma subtree_Subtree:
    forall dtr idx str,
      subtree idx dtr = Some str ->
      Subtree str dtr.
  Proof.
    dtree_ind dtr.
    find_if_inside; subst; [inv H0; auto|].
    disc_find_some.
    disc_forall_in.
    right; eapply exists_in; eauto.
  Qed.

  Lemma Subtree_wfDTree:
    forall dtr str,
      WfDTree dtr ->
      Subtree str dtr ->
      WfDTree str.
  Proof.
    dtree_ind dtr.
    destruct H1; subst; auto.
    disc_exists.
    disc_forall_in.
    eapply H3; eauto.
    eapply wfDTree_child; eauto.
  Qed.

  Lemma Subtree_refl:
    forall dtr, Subtree dtr dtr.
  Proof.
    dtree_ind dtr; auto.
  Qed.

  Lemma child_Subtree:
    forall dtr ctr,
      In ctr (childrenOf dtr) ->
      Subtree ctr dtr.
  Proof.
    dtree_ind dtr.
    right; eapply exists_in; eauto.
    apply Subtree_refl.
  Qed.

  Lemma Subtree_child:
    forall dtr ctr str,
      Subtree str dtr ->
      In ctr (childrenOf str) ->
      Subtree ctr dtr.
  Proof.
    dtree_ind dtr.
    destruct H0; subst.
    - simpl in *.
      right; eapply exists_in; eauto.
      apply Subtree_refl.
    - disc_exists.
      right; eapply exists_in; eauto.
      disc_forall_in; eauto.
  Qed.

  Lemma Subtree_trans:
    forall {dtr1 dtr2},
      Subtree dtr1 dtr2 ->
      forall {dtr3},
        Subtree dtr2 dtr3 ->
        Subtree dtr1 dtr3.
  Proof.
    dtree_ind dtr2; simpl; intros.
    destruct H0; subst; auto.
    disc_exists.
    rewrite Forall_forall in H.
    eapply H; eauto.
    eapply Subtree_child; eauto.
  Qed.

  Lemma Subtree_children_not_itself:
    forall str dtr,
      Subtree str dtr ->
      ~ Exists (Subtree dtr) (childrenOf str).
  Proof.
    dtree_ind dtr.
    destruct H0; subst.
    - intro Hx.
      disc_exists; simpl in *.
      disc_forall_in; specialize (H2 H1).
      elim H2.
      eapply exists_in; eauto.
      apply Subtree_refl.
    - disc_exists.
      disc_forall_in; specialize (H2 H1).
      intro Hx; elim H2; clear H2.
      disc_exists.
      eapply exists_in; eauto.
      eapply Subtree_trans; [|eassumption].
      eapply child_Subtree; auto.
  Qed.

  Lemma Subtree_child_not_itself:
    forall str dtr,
      Subtree str dtr ->
      forall ctr,
        In ctr (childrenOf str) ->
        ~ Subtree dtr ctr.
  Proof.
    intros.
    apply Subtree_children_not_itself in H.
    intro Hx; elim H; clear H.
    eapply exists_in; eauto.
  Qed.

  Lemma Subtree_antisym:
    forall dtr1 dtr2,
      Subtree dtr1 dtr2 ->
      Subtree dtr2 dtr1 ->
      dtr1 = dtr2.
  Proof.
    dtree_ind dtr1.
    destruct H1; subst; auto.
    exfalso.
    disc_exists.
    disc_forall_in.
    assert (Subtree ctr dtr2).
    { eapply Subtree_trans; [|eassumption].
      apply Subtree_child with (str:= DNode root cs); auto.
      apply Subtree_refl.
    }
    specialize (H3 _ H4 H2); subst.
    eapply Subtree_child_not_itself with (str:= DNode root cs); eauto.
  Qed.

  Lemma Subtree_indsOf:
    forall str dtr,
      Subtree str dtr ->
      SubList (indsOf str) (indsOf dtr).
  Proof.
    dtree_ind dtr.
    destruct H0; subst; [apply SubList_refl|].
    disc_exists.
    disc_forall_in.
    apply SubList_cons_right.
    eapply SubList_trans; [eauto|].
    apply collect_in; auto.
  Qed.

  Lemma children_indsOf_disj:
    forall dtr,
      WfDTree dtr ->
      forall ctr1 ctr2,
        In ctr1 (childrenOf dtr) ->
        In ctr2 (childrenOf dtr) ->
        ctr1 <> ctr2 ->
        DisjList (indsOf ctr1) (indsOf ctr2).
  Proof.
    destruct dtr as [root cs]; simpl; intros.
    destruct H.
    inv H.
    clear -H0 H1 H2 H7.
    induction cs; [inv H0|].
    destruct H0; subst.
    - destruct H1; subst; [exfalso; auto|].
      simpl in H7; apply (DisjList_NoDup eq_nat_dec) in H7.
      apply DisjList_comm in H7.
      eapply DisjList_comm, DisjList_SubList; [|eassumption].
      apply collect_in; auto.
    - destruct H1; subst.
      + simpl in H7; apply (DisjList_NoDup eq_nat_dec) in H7.
        apply DisjList_comm in H7.
        eapply DisjList_SubList; [|eassumption].
        apply collect_in; auto.
      + apply IHcs; auto.
        eapply NoDup_app_weakening_2; eauto.
  Qed.

  Lemma children_chnsOf_disj:
    forall dtr,
      WfDTree dtr ->
      forall ctr1 ctr2,
        In ctr1 (childrenOf dtr) ->
        In ctr2 (childrenOf dtr) ->
        ctr1 <> ctr2 ->
        DisjList (chnsOf ctr1) (chnsOf ctr2).
  Proof.
    destruct dtr as [root cs]; simpl; intros.
    destruct H.
    red in H3; simpl in H3.
    apply NoDup_app_weakening_2 in H3.
    clear -H0 H1 H2 H3.
    induction cs; [inv H0|].
    destruct H0; subst.
    - destruct H1; subst; [exfalso; auto|].
      simpl in H3; apply (DisjList_NoDup eq_nat_dec) in H3.
      apply DisjList_comm in H3.
      eapply DisjList_comm, DisjList_SubList; [|eassumption].
      apply collect_in; auto.
    - destruct H1; subst.
      + simpl in H3; apply (DisjList_NoDup eq_nat_dec) in H3.
        apply DisjList_comm in H3.
        eapply DisjList_SubList; [|eassumption].
        apply collect_in; auto.
      + apply IHcs; auto.
        eapply NoDup_app_weakening_2; eauto.
  Qed.

  Lemma rootOf_Subtree_eq:
    forall dtr,
      WfDTree dtr ->
      forall str1 str2,
        Subtree str1 dtr ->
        Subtree str2 dtr ->
        rootOf str1 = rootOf str2 ->
        str1 = str2.
  Proof.
    dtree_ind dtr.
    destruct H1, H2; subst; auto.
    - exfalso; simpl in *.
      disc_exists.
      elim (parent_idx_not_in_children _ H0 H1).
      simpl; rewrite H3.
      eapply Subtree_indsOf; [eassumption|].
      apply indsOf_self_in.
    - exfalso; simpl in *.
      disc_exists.
      elim (parent_idx_not_in_children _ H0 H1).
      simpl; rewrite <-H3.
      eapply Subtree_indsOf; [eassumption|].
      apply indsOf_self_in.
    - do 2 disc_exists.
      destruct (dtree_dec ctr ctr0); subst.
      + disc_forall_in.
        eapply H6; eauto.
        eapply wfDTree_child; eauto.
      + exfalso.
        eapply children_indsOf_disj in n; eauto.
        apply Subtree_indsOf in H4.
        apply Subtree_indsOf in H5.
        eapply DisjList_SubList in n; [|eassumption].
        eapply DisjList_comm, DisjList_SubList in n; [|eassumption].
        apply DisjList_comm in n.
        destruct (n (rootOf str1)).
        * elim H6; rewrite H3; apply indsOf_self_in.
        * elim H6; apply indsOf_self_in.
  Qed.

  Lemma Subtree_subtree:
    forall dtr,
      WfDTree dtr ->
      forall ctr,
        Subtree ctr dtr ->
        subtree (rootOf ctr) dtr = Some ctr.
  Proof.
    dtree_ind dtr.
    find_if_inside.
    - f_equal.
      eapply rootOf_Subtree_eq; eauto.
      apply Subtree_refl.
    - destruct H1; [subst; elim n; auto|].
      disc_exists.
      disc_forall_in.
      specialize (H3 (wfDTree_child H0 _ H1) _ H2).
      destruct (find_some (subtree (rootOf ctr)) cs) as [ctr1|] eqn:Hctr1;
        [|exfalso; eapply find_some_not_None; eauto].

      disc_find_some.
      f_equal.
      eapply rootOf_Subtree_eq; [eassumption|..].
      + apply subtree_Subtree in H5.
        eapply Subtree_trans; [eassumption|].
        apply Subtree_child with (str:= DNode root cs); auto.
        apply Subtree_refl.
      + apply subtree_Subtree in H3.
        eapply Subtree_trans; [eassumption|].
        apply Subtree_child with (str:= DNode root cs); auto.
        apply Subtree_refl.
      + apply subtree_rootOf in H3.
        apply subtree_rootOf in H5.
        congruence.
  Qed.

  Lemma subtreeIndsOf_indsOf:
    forall dtr,
      WfDTree dtr ->
      forall ctr,
        Subtree ctr dtr ->
        subtreeIndsOf dtr (rootOf ctr) = indsOf ctr.
  Proof.
    intros.
    apply Subtree_subtree in H0; [|assumption].
    unfold subtreeIndsOf; rewrite H0; reflexivity.
  Qed.

  Lemma Subtree_subtreeIndsOf_self_in:
    forall dtr,
      WfDTree dtr ->
      forall str,
        Subtree str dtr ->
        In (rootOf str) (subtreeIndsOf dtr (rootOf str)).
  Proof.
    intros.
    unfold subtreeIndsOf.
    rewrite Subtree_subtree by assumption.
    simpl; apply indsOf_self_in.
  Qed.

  Lemma indsOf_in_Subtree:
    forall dtr oidx,
      In oidx (indsOf dtr) ->
      exists str,
        rootOf str = oidx /\ Subtree str dtr.
  Proof.
    dtree_ind dtr.
    destruct H0; subst.
    - exists (DNode root cs); auto.
    - apply collect_in_exist in H0.
      destruct H0 as [ctr [? ?]].
      disc_forall_in; specialize (H2 _ H1).
      destruct H2 as [str [? ?]]; subst.
      exists str; split; [reflexivity|].
      right; eapply exists_in; eauto.
  Qed.

  Lemma child_parentIdxOf:
    forall ctr ptr,
      In ctr (childrenOf ptr) ->
      parentIdxOf ptr (rootOf ctr) = Some (rootOf ptr).
  Proof.
    dtree_ind ptr.
    unfold parentIdxOf; simpl.
    destruct (find_some (hasIdx (rootOf ctr)) cs) as [[croot ccs]|] eqn:Hc;
      [reflexivity|].
    exfalso.
    eapply find_some_not_None; [..|exact Hc]; eauto.
    unfold hasIdx.
    find_if_inside; [reflexivity|exfalso; auto].
  Qed.

  Lemma chnsOf_child:
    forall dtr ctr,
      In ctr (childrenOf dtr) ->
      SubList (chnsOf ctr) (chnsOf dtr).
  Proof.
    destruct dtr as [root cs]; simpl; intros.
    apply SubList_app_2.
    apply collect_in; auto.
  Qed.

  Lemma chnsOf_Subtree:
    forall dtr str,
      Subtree str dtr ->
      SubList (chnsOf str) (chnsOf dtr).
  Proof.
    dtree_ind dtr.
    destruct H0; subst.
    - apply SubList_refl.
    - disc_exists.
      disc_forall_in; specialize (H2 _ H1).
      apply SubList_app_2.
      eapply SubList_trans; [eassumption|].
      apply collect_in; auto.
  Qed.

  Lemma parentChnsOf_case:
    forall dtr cidx croot pidx,
      parentChnsOf cidx dtr = Some (croot, pidx) ->
      exists ctr,
        In ctr (childrenOf dtr) /\
        ((cidx = rootOf ctr /\ croot = dmcOf ctr) \/
         parentChnsOf cidx ctr = Some (croot, pidx)).
  Proof.
    destruct dtr as [root cs]; simpl; intros.
    destruct (find_some (hasIdx cidx) cs) as [[croot' ccs]|] eqn:Hctr.
    - inv H; disc_find_some.
      apply hasIdx_Some in H0; dest; subst; simpl in *.
      exists (DNode croot ccs); auto.
    - disc_find_some; eauto.
  Qed.

  Lemma parentChnsOf_Subtree:
    forall dtr cidx croot pidx,
      parentChnsOf cidx dtr = Some (croot, pidx) ->
      exists ctr ptr,
        Subtree ptr dtr /\ rootOf ptr = pidx /\
        dmcOf ctr = croot /\ croot.(dmc_me) = cidx /\
        In ctr (childrenOf ptr).
  Proof.
    dtree_ind dtr.
    destruct (find_some (hasIdx cidx) cs) as [[croot' ccs]|] eqn:Hctr.
    - inv H0.
      disc_find_some.
      apply hasIdx_Some in H1; dest; subst.
      exists (DNode croot ccs), (DNode root cs).
      repeat split; auto.
    - disc_find_some.
      disc_forall_in.
      specialize (H2 _ _ _ H1).
      destruct H2 as [cdtr [ptr ?]]; dest.
      exists cdtr, ptr.
      repeat split; auto.
      assert (Subtree ctr (DNode root cs))
        by (apply child_Subtree; assumption).
      apply (Subtree_trans H2 H7).
  Qed.

  Lemma parentChnsOf_chnsOf:
    forall dtr idx croot pidx,
      parentChnsOf idx dtr = Some (croot, pidx) ->
      SubList (croot.(dmc_ups) ++ croot.(dmc_downs)) (chnsOf dtr).
  Proof.
    intros.
    apply parentChnsOf_Subtree in H.
    destruct H as [ctr [ptr ?]]; dest; subst.
    eapply SubList_trans; [|eapply chnsOf_Subtree; eassumption].
    eapply SubList_trans; [|apply chnsOf_Subtree;
                            apply child_Subtree; eassumption].
    destruct ctr as [croot ccs]; simpl in *.
    apply chnsOf_self_in.
  Qed.

  Lemma parentChnsOf_child_chnsOf:
    forall dtr cidx croot pidx,
      parentChnsOf cidx dtr = Some (croot, pidx) ->
      exists ctr,
        In ctr (childrenOf dtr) /\
        SubList (croot.(dmc_ups) ++ croot.(dmc_downs)) (chnsOf ctr).
  Proof.
    intros.
    apply parentChnsOf_case in H.
    destruct H as [ctr ?]; dest.
    exists ctr.
    destruct H0; dest; subst.
    - split; auto.
      destruct ctr as [root cs].
      apply chnsOf_self_in.
    - split; auto.
      eapply parentChnsOf_chnsOf; eauto.
  Qed.

  Lemma parentChnsOf_root_disj:
    forall dtr,
      WfDTree dtr ->
      forall idx croot pidx,
        parentChnsOf idx dtr = Some (croot, pidx) ->
        DisjList (croot.(dmc_ups) ++ croot.(dmc_downs))
                 ((dmcOf dtr).(dmc_ups) ++ (dmcOf dtr).(dmc_downs)).
  Proof.
    destruct dtr as [root cs]; intros; simpl.
    destruct H.
    red in H1; simpl in H1.
    apply (DisjList_NoDup eq_nat_dec) in H1.
    eapply DisjList_SubList; [|apply DisjList_comm; eassumption].
    apply parentChnsOf_child_chnsOf in H0.
    destruct H0 as [ctr ?]; dest; simpl in *.
    eapply SubList_trans; [eassumption|].
    apply collect_in; auto.
  Qed.

  Lemma parentIdxOf_Subtree:
    forall dtr cidx pidx,
      parentIdxOf dtr cidx = Some pidx ->
      exists ctr ptr,
        Subtree ptr dtr /\ rootOf ptr = pidx /\
        rootOf ctr = cidx /\ In ctr (childrenOf ptr).
  Proof.
    unfold parentIdxOf; intros.
    destruct (parentChnsOf cidx dtr) as [[croot pidx']|] eqn:Hcp;
      [|discriminate].
    inv H.
    apply parentChnsOf_Subtree in Hcp.
    destruct Hcp as [ctr [ptr ?]]; dest; subst.
    exists ctr, ptr.
    repeat split; auto.
    destruct ctr; reflexivity.
  Qed.

  Section Wf.
    Variable dtr: DTree.
    Hypothesis Hwf: WfDTree dtr.

    Lemma parentChnsOf_Subtree_eq:
      forall str,
        Subtree str dtr ->
        forall oidx,
          oidx <> rootOf str ->
          In oidx (indsOf str) ->
          parentChnsOf oidx dtr = parentChnsOf oidx str.
    Proof.
    Admitted.

    Lemma parentIdxOf_Subtree_eq:
      forall str,
        Subtree str dtr ->
        forall oidx,
          oidx <> rootOf str ->
          In oidx (indsOf str) ->
          parentIdxOf dtr oidx = parentIdxOf str oidx.
    Proof.
      intros.
      unfold parentIdxOf.
      erewrite parentChnsOf_Subtree_eq; eauto.
    Qed.

    Lemma parentIdxOf_not_eq:
      forall idx pidx,
        parentIdxOf dtr idx = Some pidx ->
        idx <> pidx.
    Proof.
      intros.
      apply parentIdxOf_Subtree in H.
      destruct H as [ctr [ptr ?]]; dest; subst.
      pose proof (Subtree_wfDTree _ Hwf H).
      apply parent_idx_not_in_children in H2; [|assumption].
      intro Hx; subst; elim H2.
      rewrite <-Hx.
      apply indsOf_self_in.
    Qed.

    Lemma parentIdxOf_asym:
      forall oidx1 oidx2,
        parentIdxOf dtr oidx1 = Some oidx2 ->
        parentIdxOf dtr oidx2 = Some oidx1 ->
        False.
    Proof.
      intros.
      apply parentIdxOf_Subtree in H.
      destruct H as [ctr1 [ptr1 ?]].
      apply parentIdxOf_Subtree in H0.
      destruct H0 as [ctr2 [ptr2 ?]].
      dest; subst.
      pose proof (Subtree_trans (child_Subtree _ _ H6) H).
      pose proof (Subtree_trans (child_Subtree _ _ H3) H0).
      eapply rootOf_Subtree_eq in H1; eauto; subst.
      eapply rootOf_Subtree_eq in H2; eauto; subst.
      apply parent_idx_not_in_children in H3.
      - elim H3.
        eapply childrenOf_indsOf; [eassumption|].
        apply indsOf_self_in.
      - eapply Subtree_wfDTree; eauto.
    Qed.

    Lemma parentChnsOf_Some_in_tree:
      forall oidx cp,
        parentChnsOf oidx dtr = Some cp ->
        In oidx (indsOf dtr).
    Proof.
      destruct cp as [croot pidx]; intros.
      apply parentChnsOf_Subtree in H.
      destruct H as [ctr [ptr ?]]; dest; subst.
      eapply Subtree_indsOf; [eassumption|].
      eapply childrenOf_indsOf; [eassumption|].
      rewrite <-rootOf_dmcOf.
      eapply indsOf_self_in.
    Qed.

    Lemma indsOf_composed:
      forall oidx root cs,
        In oidx (indsOf (DNode root cs)) ->
        oidx = root.(dmc_me) \/
        (exists ctr, In ctr cs /\ In oidx (indsOf ctr)).
    Proof.
      simpl; intros.
      destruct H; auto.
      apply collect_in_exist in H.
      destruct H as [ctr [? ?]].
      eauto.
    Qed.

    Lemma subtreeIndsOf_composed:
      forall oidx roidx,
        In oidx (subtreeIndsOf dtr roidx) ->
        oidx = roidx \/
        (exists cidx,
            parentIdxOf dtr cidx = Some roidx /\
            In oidx (subtreeIndsOf dtr cidx)).
    Proof.
      intros.
      unfold subtreeIndsOf in H.
      destruct (subtree roidx dtr) as [[root cs]|] eqn:Htr; [|inv H].
      apply indsOf_composed in H.
      destruct H; subst.
      - left; apply subtree_rootOf in Htr; assumption.
      - right.
        destruct H as [ctr [? ?]].
        exists (rootOf ctr).
        split.
        + pose proof Htr.
          apply subtree_rootOf in H1; simpl in H1; subst.
          apply subtree_Subtree in Htr.
          rewrite parentIdxOf_Subtree_eq with (str:= DNode root cs).
          * apply child_parentIdxOf; auto.
          * assumption.
          * apply neq_sym.
            eapply parent_idx_child_not_eq.
            { eapply Subtree_wfDTree; eauto. }
            { assumption. }
          * eapply Subtree_indsOf with (str:= ctr).
            { apply child_Subtree; auto. }
            { apply indsOf_self_in. }
        + rewrite subtreeIndsOf_indsOf; auto.
          apply subtree_Subtree in Htr.
          eapply Subtree_trans; [|eassumption].
          apply child_Subtree; auto.
    Qed.

    Lemma parentChnsOf_subtreeIndsOf_self_in:
      forall cidx,
        parentChnsOf cidx dtr <> None ->
        In cidx (subtreeIndsOf dtr cidx).
    Proof.
      intros.
      destruct (parentChnsOf cidx dtr) as [[croot pidx]|] eqn:Hcp;
        [|exfalso; auto].
      apply parentChnsOf_Subtree in Hcp.
      destruct Hcp as [ctr [ptr ?]]; dest; subst.
      rewrite <-rootOf_dmcOf.
      apply Subtree_subtreeIndsOf_self_in; auto.
      eapply Subtree_trans; [|eassumption].
      apply child_Subtree; auto.
    Qed.

    Lemma parent_subtreeIndsOf_self_in:
      forall cidx oidx,
        parentIdxOf dtr cidx = Some oidx ->
        In oidx (subtreeIndsOf dtr oidx).
    Proof.
      intros.
      apply parentIdxOf_Subtree in H.
      destruct H as [ctr [ptr ?]]; dest; subst.
      apply Subtree_subtreeIndsOf_self_in; auto.
    Qed.

    Lemma subtreeIndsOf_child_in:
      forall cidx pidx,
        parentIdxOf dtr cidx = Some pidx ->
        In cidx (subtreeIndsOf dtr pidx).
    Proof.
      intros.
      apply parentIdxOf_Subtree in H.
      destruct H as [ctr [ptr ?]]; dest; subst.
      rewrite subtreeIndsOf_indsOf by assumption.
      eapply childrenOf_indsOf; [eassumption|].
      apply indsOf_self_in.
    Qed.

    Lemma subtreeIndsOf_child_disj:
      forall cidx1 cidx2 pidx,
        cidx1 <> cidx2 ->
        parentIdxOf dtr cidx1 = Some pidx ->
        parentIdxOf dtr cidx2 = Some pidx ->
        DisjList (subtreeIndsOf dtr cidx1) (subtreeIndsOf dtr cidx2).
    Proof.
      intros.
      apply parentIdxOf_Subtree in H0.
      destruct H0 as [ctr1 [ptr1 ?]]; dest.
      apply parentIdxOf_Subtree in H1.
      destruct H1 as [ctr2 [ptr2 ?]]; dest; subst.
      rewrite subtreeIndsOf_indsOf;
        [|assumption
         |eapply Subtree_child; [|eassumption]; assumption].
      rewrite subtreeIndsOf_indsOf;
        [|assumption
         |eapply Subtree_child; [|eassumption]; assumption].
      eapply rootOf_Subtree_eq in H5; eauto; subst.
      eapply children_indsOf_disj with (dtr:= ptr1); eauto.
      - eapply Subtree_wfDTree; eauto.
      - intro Hx; subst; auto.
    Qed.

    Lemma subtreeIndsOf_other_child_not_in:
      forall cidx1 cidx2 pidx,
        cidx1 <> cidx2 ->
        parentIdxOf dtr cidx1 = Some pidx ->
        parentIdxOf dtr cidx2 = Some pidx ->
        ~ In cidx1 (subtreeIndsOf dtr cidx2).
    Proof.
      intros.
      pose proof (subtreeIndsOf_child_disj H H0 H1).
      specialize (H2 cidx1).
      destruct H2; [elim H2|auto].
      apply parentChnsOf_subtreeIndsOf_self_in.
      unfold parentIdxOf in H0.
      destruct (parentChnsOf cidx1 dtr);
        simpl in *; discriminate.
    Qed.

    Lemma parent_not_in_subtree:
      forall oidx pidx,
        parentIdxOf dtr oidx = Some pidx ->
        ~ In pidx (subtreeIndsOf dtr oidx).
    Proof.
      intros.
      apply parentIdxOf_Subtree in H.
      destruct H as [ctr [ptr ?]]; dest; subst.
      rewrite subtreeIndsOf_indsOf.
      - eapply parent_idx_not_in_children in H2; [eassumption|].
        eapply Subtree_wfDTree; eauto.
      - assumption.
      - eapply Subtree_trans; [|eassumption].
        eapply Subtree_child; eauto.
        apply Subtree_refl.
    Qed.

    Lemma subtreeIndsOf_SubList:
      forall oidx1 oidx2,
        In oidx1 (subtreeIndsOf dtr oidx2) ->
        SubList (subtreeIndsOf dtr oidx1) (subtreeIndsOf dtr oidx2).
    Proof.
      intros.
      unfold subtreeIndsOf in H.
      destruct (subtree oidx2 dtr) as [str2|] eqn:Hstr2; [|inv H].
      simpl in H.

      pose proof (subtree_Subtree _ _ Hstr2).
      apply subtree_rootOf in Hstr2; subst.
      rewrite subtreeIndsOf_indsOf with (ctr:= str2) by assumption.

      apply indsOf_in_Subtree in H.
      destruct H as [str1 [? ?]]; subst.
      rewrite subtreeIndsOf_indsOf;
        [|eassumption
         |eapply Subtree_trans; eauto].
      apply Subtree_indsOf; auto.
    Qed.

    Lemma subtreeIndsOf_In_each_other_eq:
      forall oidx1 oidx2,
        In oidx1 (subtreeIndsOf dtr oidx2) ->
        In oidx2 (subtreeIndsOf dtr oidx1) ->
        oidx1 = oidx2.
    Proof.
      intros.
      unfold subtreeIndsOf in H.
      destruct (subtree oidx2 dtr) as [str2|] eqn:Hstr2; [simpl in H|inv H].
      unfold subtreeIndsOf in H0.
      destruct (subtree oidx1 dtr) as [str1|] eqn:Hstr1; [simpl in H0|inv H0].
      apply indsOf_in_Subtree in H.
      destruct H as [ctr1 [? ?]]; subst.
      apply indsOf_in_Subtree in H0.
      destruct H0 as [ctr2 [? ?]]; subst.
      pose proof (subtree_Subtree _ _ Hstr1).
      pose proof (subtree_Subtree _ _ Hstr2).
      apply subtree_rootOf in Hstr1.
      apply subtree_rootOf in Hstr2.
      eapply rootOf_Subtree_eq in Hstr1; eauto; subst;
        [|eapply Subtree_trans; eauto].
      eapply rootOf_Subtree_eq in Hstr2; eauto; subst;
        [|eapply Subtree_trans; eauto].
      pose proof (Subtree_antisym _ _ H0 H1); subst.
      reflexivity.
    Qed.

    Lemma inside_child_in:
      forall cidx pidx oidx,
        parentIdxOf dtr cidx = Some pidx ->
        In pidx (subtreeIndsOf dtr oidx) ->
        In cidx (subtreeIndsOf dtr oidx).
    Proof.
      intros.
      apply subtreeIndsOf_SubList in H0.
      apply H0.
      apply subtreeIndsOf_child_in; auto.
    Qed.

    Lemma outside_parent_out:
      forall oidx cidx pidx,
        ~ In cidx (subtreeIndsOf dtr oidx) ->
        parentIdxOf dtr cidx = Some pidx ->
        ~ In pidx (subtreeIndsOf dtr oidx).
    Proof.
      intros.
      intro Hx; elim H.
      eapply inside_child_in; eauto.
    Qed.

    Lemma inside_parent_in:
      forall cidx pidx oidx,
        parentIdxOf dtr cidx = Some pidx ->
        In cidx (subtreeIndsOf dtr oidx) ->
        cidx <> oidx ->
        In pidx (subtreeIndsOf dtr oidx).
    Proof.
    Admitted.

    Lemma outside_child_in:
      forall oidx cidx pidx,
        ~ In pidx (subtreeIndsOf dtr oidx) ->
        parentIdxOf dtr cidx = Some pidx ->
        cidx = oidx \/ ~ In cidx (subtreeIndsOf dtr oidx).
    Proof.
      intros.
      destruct (eq_nat_dec cidx oidx); auto.
      right.
      intro Hx; elim H.
      eapply inside_parent_in; eauto.
    Qed.

    Lemma inside_child_outside_parent_case:
      forall cidx pidx oidx,
        parentIdxOf dtr cidx = Some pidx ->
        In cidx (subtreeIndsOf dtr oidx) ->
        ~ In pidx (subtreeIndsOf dtr oidx) ->
        cidx = oidx.
    Proof.
      intros.
      destruct (eq_nat_dec cidx oidx); auto.
      eapply inside_parent_in in H; try eassumption.
      exfalso; auto.
    Qed.

    Lemma subtreeIndsOf_child_SubList:
      forall cidx pidx,
        parentIdxOf dtr cidx = Some pidx ->
        SubList (subtreeIndsOf dtr cidx) (subtreeIndsOf dtr pidx).
    Proof.
      intros.
      apply subtreeIndsOf_SubList.
      apply subtreeIndsOf_child_in; assumption.
    Qed.

    Lemma parentChnsOf_NoDup:
      forall idx croot pidx,
        parentChnsOf idx dtr = Some (croot, pidx) ->
        NoDup (croot.(dmc_ups) ++ croot.(dmc_downs)).
    Proof.
      intros.
      apply parentChnsOf_Subtree in H.
      destruct H as [ctr [ptr ?]]; dest; subst.
      assert (WfDTree ctr).
      { destruct ptr as [proot pcs].
        eapply wfDTree_child with (root:= proot) (cs:= pcs); eauto.
        eapply Subtree_wfDTree; eauto.
      }
      destruct H0.
      destruct ctr as [croot ccs].
      red in H1; simpl in H1.
      simpl; eapply NoDup_app_weakening_1; eauto.
    Qed.

    Lemma parentChnsOf_DisjList:
      forall idx1 croot1 pidx1 idx2 croot2 pidx2,
        idx1 <> idx2 ->
        parentChnsOf idx1 dtr = Some (croot1, pidx1) ->
        parentChnsOf idx2 dtr = Some (croot2, pidx2) ->
        DisjList (croot1.(dmc_ups) ++ croot1.(dmc_downs))
                 (croot2.(dmc_ups) ++ croot2.(dmc_downs)).
    Proof.
      induction dtr as [root cs] using DTree_ind2; intros.
      eapply parentChnsOf_case in H1; simpl in H1.
      destruct H1 as [ctr1 ?].
      eapply parentChnsOf_case in H2; simpl in H2.
      destruct H2 as [ctr2 ?]; dest.
      destruct H3, H4; dest; subst.
      - eapply DisjList_SubList with (l1:= chnsOf ctr1);
          [destruct ctr1 as [croot1 ccs1]; unfold dmcOf;
           apply chnsOf_self_in|].
        eapply DisjList_comm, DisjList_SubList with (l1:= chnsOf ctr2);
          [destruct ctr2 as [croot2 ccs2]; unfold dmcOf;
           apply chnsOf_self_in|].
        apply DisjList_comm.
        eapply children_chnsOf_disj; eauto.
        intro Hx; subst; auto.
      - destruct (dtree_dec ctr1 ctr2); subst.
        + eapply parentChnsOf_root_disj; eauto.
          eapply wfDTree_child; eauto.
        + eapply DisjList_SubList; [eapply parentChnsOf_chnsOf; eauto|].
          destruct ctr2 as [root2 cs2]; simpl in *.
          eapply DisjList_comm, DisjList_SubList;
            [eapply chnsOf_self_in with (cs:= cs2)|].
          apply DisjList_comm.
          eapply children_chnsOf_disj; eauto.
      - destruct (dtree_dec ctr1 ctr2); subst.
        + eapply DisjList_comm, parentChnsOf_root_disj; eauto.
          eapply wfDTree_child; eauto.
        + eapply DisjList_comm, DisjList_SubList;
            [eapply parentChnsOf_chnsOf; eauto|].
          destruct ctr1 as [root1 cs1]; simpl in *.
          eapply DisjList_comm, DisjList_SubList;
            [eapply chnsOf_self_in with (cs:= cs1)|].
          apply DisjList_comm.
          eapply children_chnsOf_disj; eauto.
      - destruct (dtree_dec ctr1 ctr2); subst.
        + disc_forall_in.
          eapply H5; eauto.
          eapply wfDTree_child; eauto.
        + eapply DisjList_SubList; [eapply parentChnsOf_chnsOf; eauto|].
          eapply DisjList_comm, DisjList_SubList;
            [eapply parentChnsOf_chnsOf; eauto|].
          apply DisjList_comm.
          eapply children_chnsOf_disj; eauto.
    Qed.
    
  End Wf.

End Facts.

Close Scope list.

