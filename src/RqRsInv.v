Require Import Peano_dec List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics StepM Invariant Serial.
Require Import Reduction Commutable QuasiSeq Topology.
Require Import RqRsTopo.

Open Scope list.
Open Scope fmap.

(** Useful invariants on top of [RqRsSys] *)

Inductive TrsType := RqUp | RqDown | RsUp | RsDown.
(* Object index -> TrsTypes (ordered, head is the oldest one) *)
Definition TrsState := M.t (list TrsType).

Definition addTrsState (oidx: IdxT) (tr: TrsType) (ts: TrsState): TrsState :=
  match ts@[oidx] with
  | Some tts => ts +[oidx <- tr :: tts]
  | None => ts +[oidx <- [tr]]
  end.

Definition rssOfL (lbl: MLabel) :=
  match lbl with
  | RlblInt oidx _ _ mouts =>
    match mouts with
    | nil => Some oidx (* Requests are never ignored. *)
    | (midx, mout) :: _ =>
      if eq_nat_dec (msg_type mout) MRs
      then Some oidx else None
    end
  | _ => None
  end.

Fixpoint rssOf (hst: MHistory): list IdxT :=
  match hst with
  | nil => nil
  | lbl :: hst' => (rssOfL lbl) ::> (rssOf hst')
  end.

Definition trsTypeOf (gtr: DTree) (idm: Id Msg):
  option IdxT * option IdxT * TrsType :=
  (findEdge gtr (fst idm))
    >>=[(None, None, RqUp)]
    (fun e =>
       (e.(edge_from),
        e.(edge_to),
        match fst (fst e.(edge_chn)) with
        | CUp => if eq_nat_dec (msg_type (snd idm)) MRq then RqUp else RsUp
        | CDown => if eq_nat_dec (msg_type (snd idm)) MRq then RqDown else RsDown
        end)).

(* Definition SemiDisjTrsType (t1 t2: TrsType) := *)
(*   match t1, t2 with *)
(*   | RqUp, RqDown => True *)
(*   | RqUp, RsUp => True *)
(*   | RqDown, RqUp => True *)
(*   (** Since there is always a single downward channel, we need to keep the order *)
(*    * in the channel. *)
(*    *) *)
(*   (* | RqDown, RsDown => True *) *)
(*   | _, _ => False *)
(*   end. *)

(* Definition SemiDisjTrsState (ts1 ts2: TrsState) := *)
(*   forall oidx, *)
(*     match ts1@[oidx], ts2@[oidx] with *)
(*     | Some tts1, Some tts2 => *)
(*       forall t1 t2, *)
(*         In t1 tts1 -> In t2 tts2 -> *)
(*         SemiDisjTrsType t1 t2 *)
(*     | _, _ => True *)
(*     end. *)

(* Definition rqsOfL (lbl: MLabel) := *)
(*   match lbl with *)
(*   | RlblInt oidx _ _ mouts => *)
(*     match mouts with *)
(*     | nil => None (* Requests are never ignored. *) *)
(*     | (midx, mout) :: _ => *)
(*       if eq_nat_dec (msg_type mout) MRq *)
(*       then Some oidx else None *)
(*     end *)
(*   | _ => None *)
(*   end. *)

Section AtomicInv.
  Context {oifc: OStateIfc}.
  Variables (gtr: DTree)
            (sys: System oifc).

  Hypothesis (Hitr: GoodIterationSys gtr oifc sys).

  Definition subtreeInds (sroot: option IdxT): list IdxT :=
    sroot >>=[nil] (fun sroot => dg_vs (topoOfT (subtree gtr sroot))).

  Definition subtreeCInds (sroot: option IdxT): list IdxT :=
    removeL eq_nat_dec (dg_vs (topoOfT gtr))
            (sroot >>=[nil] (fun sroot => dg_vs (topoOfT (subtree gtr sroot)))).

  Definition rqCover (idm: Id Msg): list IdxT :=
    let from := fst (fst (trsTypeOf gtr idm)) in
    let to := snd (fst (trsTypeOf gtr idm)) in
    match snd (trsTypeOf gtr idm) with
    | RqUp => dg_vs (topoOfT gtr) (* the entire indices *)
    | RqDown => subtreeInds to
    | _ => nil
    end.
  
  Fixpoint rqCovers (eouts: list (Id Msg)): list IdxT :=
    match eouts with
    | nil => nil
    | idm :: eouts' => rqCover idm ++ rqCovers eouts'
    end.
  
  Definition rsCover (idm: Id Msg): list IdxT :=
    let from := fst (fst (trsTypeOf gtr idm)) in
    let to := snd (fst (trsTypeOf gtr idm)) in
    match snd (trsTypeOf gtr idm) with
    | RsUp => subtreeInds from
    | RsDown => subtreeCInds to
    | _ => nil
    end.
  
  Fixpoint rsCovers (eouts: list (Id Msg)): list IdxT :=
    match eouts with
    | nil => nil
    | idm :: eouts' => rsCover idm ++ rsCovers eouts'
    end.

  Definition AtomicInv (eouts: list (Id Msg)) (hst: MHistory) :=
    NoDup (rssOf hst) /\
    SubList (rssOf hst) (rsCovers eouts) /\
    DisjList (rssOf hst) (rqCovers eouts).

  Lemma atomic_inv:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        steps step_m sys s1 hst s2 ->
        AtomicInv eouts hst.
  Proof.
    induction 1; simpl; intros; subst.
    
    - inv H; inv H3; inv H5.

      red in Hitr; rewrite Forall_forall in Hitr.
      specialize (Hitr _ H3).
      red in Hitr; rewrite Forall_forall in Hitr.
      specialize (Hitr _ H4).
      red in Hitr.

  Admitted.
  
End AtomicInv.

(* Want: between two continuous histories H1 and H2, after H1, related locks are
 * never released until H2.
 *)
Section LockInv.
  Context {oifc: OStateIfc}.
  Variables (gtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrr: GoodLockingSys gtr oifc sys).

  Section OnMState.
    Variables (orqs: ORqs Msg)
              (msgs: MessagePool Msg).

    Definition OLocked (oidx: IdxT) :=
      orqs@[oidx] >>=[False]
        (fun orq =>
           orq@[O] >>=[False]
             (fun aorq => aorq@[downRq] <> None)).

    Definition DownLockFreeInv (oidx: IdxT) :=
      let str := subtree gtr oidx in
      ForallQ (fun midx q =>
                 if midx ?<n (rsUpEdges str)
                 then q = nil
                 else if midx ?<n (downEdges str)
                      then filter (fun msg => msg.(msg_type) ==n MRq) q = nil
                      else True) msgs.

    Definition DownLockedInv (oidx: IdxT) (rqi: RqInfo Msg) :=
      let str := subtree gtr oidx in
      let ctrs := childrenOf str in
      Forall (fun child =>
                match child with
                | Leaf => True
                | Node croot _ =>
                  (rsEdgeUpFrom gtr croot)
                    >>=[True]
                    (fun rsUp =>
                       if rsUp ?<n rqi.(rqi_minds_rss)
                       then (edgeDownTo gtr croot)
                              >>=[True]
                              (fun down =>
                                 xor3 (length (findQ rsUp msgs) = 1)
                                      (length (filter (fun msg => msg.(msg_type) ==n MRq)
                                                      (findQ down msgs)) = 1)
                                      (OLocked croot))
                       else DownLockFreeInv croot)
                end) ctrs.

    Definition LockInvORq (oidx: IdxT) (orq: ORq Msg) :=
      match orq@[O] with
      | Some aorq =>
        match aorq@[downRq] with
        | Some downRqi => DownLockedInv oidx downRqi
        | None => DownLockFreeInv oidx
        end
      | None => DownLockFreeInv oidx
      end.

    Definition LockInvMO :=
      forall oidx,
        In oidx (map (@obj_idx _) sys.(sys_objs)) ->
        LockInvORq oidx (orqs@[oidx] >>=[[]] (fun orq => orq)).

  End OnMState.
  
  Definition LockInv (st: MState oifc) :=
    LockInvMO st.(bst_orqs) st.(bst_msgs).

  Lemma lockInv_init:
    sys.(sys_orqs_inits) = [] ->
    InvInit sys LockInv.
  Proof.
    intros; do 3 red; cbn.
    intros; cbn; rewrite H; cbn.
    do 2 red; cbn; intros.
    find_if_inside; auto.
    find_if_inside; auto.
  Qed.

  Lemma lockInv_step_ext_in:
    forall oss orqs msgs eins,
      LockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      eins <> nil ->
      ValidMsgsExtIn sys eins ->
      LockInv {| bst_oss := oss;
                 bst_orqs := orqs;
                 bst_msgs := enqMsgs eins msgs |}.
  Proof.
    unfold LockInv, LockInvMO; cbn; intros.
    specialize (H oidx H2).
    unfold LockInvORq in *.
    remember (orqs@[oidx]) as orq; destruct orq as [orq|]; cbn in *.
    - remember (orq@[0]) as aorq; destruct aorq as [aorq|]; cbn in *.
      + admit.
      + admit.
    - admit.
    
  Admitted.

  Lemma lockInv_step_ext_out:
    forall oss orqs msgs eouts,
      LockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      eouts <> nil ->
      Forall (FirstMPI msgs) eouts ->
      ValidMsgsExtOut sys eouts ->
      LockInv {| bst_oss := oss;
                 bst_orqs := orqs;
                 bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
  Admitted.
  
  Lemma lockInv_step:
    InvStep sys step_m LockInv.
  Proof.
    red; intros.
    
    inv H1; auto.
    - apply lockInv_step_ext_in; auto.
    - apply lockInv_step_ext_out; auto.
    - 
  Admitted.

End LockInv.

Close Scope list.
Close Scope fmap.

