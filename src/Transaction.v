Require Import Peano_dec List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics StepM Invariant Serial.
Require Import Reduction Commutable QuasiSeq Topology.

Open Scope list.
Open Scope fmap.

(* TODOs:
 * 0. Have a notion of transaction paths ([TrsPath]) that includes a 
 *    "transaction type" of each object (e.g., upward-request, downward-request,
 *    etc.).
 * 1. An [Atomic] step --> exists a corresponding [TrsPath]
 * 2. For each history [hst] between continuous histories [h1] and [h2]:
 *    we need to have a way to check whether [hst] is right- or left-pushable.
 * 3. 1) Theorem (disjointness between [h1] and [h2]):
 *    [h1 -*- h2], where 
 *    [h1 -*- h2 ≜ rqsOf(h1) -*- rqsOf(h2) /\ rssOf(h1) -*- rssOf(h2)].
 *    Note that [-*-] is not commutative.
 *    2) Theorem (disjointness of [hst]): [∀hst. h1 -*- hst \/ hst -*- h2]
 * 4. Theorem: [∀h1 h2. h1 -*- h2 -> MDisjoint h1 h2 -> Commutable h1 h2]
 *)

Section Conditions.
  Context {oifc: OStateIfc}.

  (** Preconditions and postconditions dealing with messages. *)

  Definition MsgsFrom (froms: list IdxT): OPrec oifc :=
    fun _ _ mins => idsOf mins = froms.

  Definition MsgIdsFrom (msgIds: list IdxT): OPrec oifc :=
    fun _ _ mins => map msg_id (valsOf mins) = msgIds.

  Definition MsgsFromORq (addr: AddrT) (rqty: IdxT): OPrec oifc :=
    fun _ orq mins =>
      (getRq orq addr rqty)
        >>=[False] (fun rqi => idsOf mins = rqi_minds_rss rqi).

  Definition MsgsTo (tos: list IdxT) (rule: Rule oifc): Prop :=
    forall ost orq mins,
      idsOf (snd (rule.(rule_trs) ost orq mins)) = tos.

  Definition RqAccepting: OPrec oifc :=
    fun _ _ mins =>
      Forall (fun idm => msg_type (valOf idm) = MRq) mins.

  Definition RsAccepting: OPrec oifc :=
    fun _ _ mins =>
      Forall (fun idm => msg_type (valOf idm) = MRs) mins.

  Definition RqForwarding (rule: Rule oifc) :=
    forall ost orq mins,
      Forall (fun idm => msg_type (valOf idm) = MRq)
             (snd (rule.(rule_trs) ost orq mins)).

  Definition RsForwarding (rule: Rule oifc) :=
    forall ost orq mins,
      Forall (fun idm => msg_type (valOf idm) = MRs)
             (snd (rule.(rule_trs) ost orq mins)).

  (** Preconditions to check the lock state *)
  Definition upRq := 0.
  Definition downRq := 1.

  Definition LockFree (orq: ORq Msg) (addr: AddrT) :=
    orq@[addr] >>=[True] (fun aorq => aorq = []).

  Definition HalfLockFree (orq: ORq Msg) (addr: AddrT) :=
    orq@[addr] >>=[True] (fun aorq => aorq@[downRq] = None).

  Definition Locked (orq: ORq Msg) (addr: AddrT) (rss: list IdxT) :=
    orq@[addr] >>=[False]
      (fun aorq =>
         exists rqi,
           aorq@[downRq] = Some rqi /\
           rqi.(rqi_minds_rss) = rss).

  Definition HalfLocked (orq: ORq Msg) (addr: AddrT) (rsFrom: IdxT) :=
    orq@[addr] >>=[False]
      (fun aorq =>
         aorq@[downRq] = None /\
         exists rqi,
           aorq@[upRq] = Some rqi /\
           rqi.(rqi_minds_rss) = [rsFrom]).

  (** TODO: discuss whether it's fine to have a locking mechanism 
   * only for a single address. *)
  Definition LockFree0: OPrec oifc :=
    fun ost orq mins => LockFree orq O.

  Definition HalfLockFree0: OPrec oifc :=
    fun ost orq mins => HalfLockFree orq O.

  Definition Locking0 (rule: Rule oifc) (rss: list IdxT): Prop :=
    forall ost orq mins,
      Locked (snd (fst (rule.(rule_trs) ost orq mins))) O rss.

  Definition HalfLocking0 (rule: Rule oifc) (rsFrom: IdxT): Prop :=
    forall ost orq mins,
      HalfLocked (snd (fst (rule.(rule_trs) ost orq mins))) O rsFrom.

  Definition Releasing0 (rule: Rule oifc) (rss: list IdxT): Prop :=
    forall ost orq mins,
      Locked orq O rss /\
      LockFree (snd (fst (rule.(rule_trs) ost orq mins))) O.

  Definition HalfReleasing0 (rule: Rule oifc) (rsFrom: IdxT): Prop :=
    forall ost orq mins,
      HalfLocked orq O rsFrom /\
      HalfLockFree (snd (fst (rule.(rule_trs) ost orq mins))) O.

  Definition StateUnchanged (rule: Rule oifc): Prop :=
    forall ost orq mins,
      ost = fst (fst (rule.(rule_trs) ost orq mins)).

End Conditions.

Section RqRsTopo.

  Inductive RqRsTopo: DTree -> Prop :=
  | RqRsNode:
      forall ridx cs,
        Forall (fun udc =>
                  List.length (fst (fst udc)) = 2 /\ (* Two upward channels *)
                  List.length (snd (fst udc)) = 1 /\ (* A single downward channel *)
                  RqRsTopo (snd udc)) cs ->
        RqRsTopo (Node ridx cs).

  (* NOTE: should have length 2 if [RqRsTopo gtr] *)
  Definition edgesUpFrom (gtr: DTree) (oidx: IdxT): list IdxT :=
    map (fun e => snd e.(edge_chn)) (upEdgesFrom gtr oidx).

  Definition edgesUpTo (gtr: DTree) (oidx: IdxT): list IdxT :=
    map (fun e => snd e.(edge_chn)) (upEdgesTo gtr oidx).

  (* NOTE: should have length 1 if [RqRsTopo gtr] *)
  Definition edgesDownFrom (gtr: DTree) (oidx: IdxT): list IdxT :=
    map (fun e => snd e.(edge_chn)) (downEdgesFrom gtr oidx).

  (* NOTE: should have length 1 if [RqRsTopo gtr] *)
  Definition edgesDownTo (gtr: DTree) (oidx: IdxT): list IdxT :=
    map (fun e => snd e.(edge_chn)) (downEdgesTo gtr oidx).

  Section PerSystem.
    Variables (gtr: DTree) (oifc: OStateIfc).
    
    Section PerObject.
      Variable (oidx: IdxT).
      
      (** * Rule predicates about which messages to accept *)

      (* A rule handling a request from one of its children *)
      Definition RqFromDownRule (rule: Rule oifc) :=
        exists rqFrom,
          In rqFrom (edgesUpTo gtr oidx) /\
          (rule.(rule_precond)
           ->oprec (MsgsFrom [rqFrom]
                    /\oprec RqAccepting
                    /\oprec LockFree0)).

      (* A rule handling a request from the parent *)
      Definition RqFromUpRule (rule: Rule oifc) :=
        exists rqFrom,
          In rqFrom (edgesDownTo gtr oidx) /\
          (rule.(rule_precond)
           ->oprec (MsgsFrom [rqFrom]
                    /\oprec RqAccepting
                    /\oprec HalfLockFree0)).

      (* A rule handling responses from some of its children *)
      Definition RsFromDownRule (rule: Rule oifc) :=
        exists rssFrom,
          SubList rssFrom (edgesUpTo gtr oidx) /\ NoDup rssFrom /\
          (rule.(rule_precond) ->oprec (MsgsFrom rssFrom /\oprec RsAccepting)) /\
          Releasing0 rule rssFrom.

      (* A rule handling a response from the parent *)
      Definition RsFromUpRule (rule: Rule oifc) :=
        exists rsFrom,
          In rsFrom (edgesDownTo gtr oidx) /\
          (rule.(rule_precond) ->oprec (MsgsFrom [rsFrom] /\oprec RsAccepting)) /\
          HalfReleasing0 rule rsFrom.

      (** * Rule predicates about which messages to release *)

      (* A rule making requests to some of its children *)
      Definition RqToDownRule (rule: Rule oifc) :=
        exists rqsTo rssFrom,
          SubList rqsTo (edgesDownFrom gtr oidx) /\ NoDup rqsTo /\
          MsgsTo rqsTo rule /\ RqForwarding rule /\
          Locking0 rule rssFrom /\
          (* RqRsChannels rqsTo rssFrom /\ *)
          StateUnchanged rule.

      (* A rule making a request to the parent *)
      Definition RqToUpRule (rule: Rule oifc) :=
        exists rqTo rsFrom,
          In rqTo (edgesUpFrom gtr oidx) /\
          MsgsTo [rqTo] rule /\ RqForwarding rule /\
          HalfLocking0 rule rsFrom /\
          (* RqRsChannels [rqTo] [rsFrom] /\ *)
          StateUnchanged rule.

      (* A rule making a response to one of its children *)
      Definition RsToDownRule (rule: Rule oifc) :=
        exists rsTo,
          In rsTo (edgesDownFrom gtr oidx) /\
          MsgsTo [rsTo] rule /\
          RsForwarding rule.
      
      (* A rule making a response to the parent *)
      Definition RsToUpRule (rule: Rule oifc) :=
        exists rsTo,
          In rsTo (edgesUpFrom gtr oidx) /\
          MsgsTo [rsTo] rule /\
          RsForwarding rule.

      Definition RqRsGoodAccept (rule: Rule oifc) :=
        RqFromDownRule rule \/
        RqFromUpRule rule \/
        RsFromDownRule rule \/
        RsFromUpRule rule.

      Definition RqRsGoodRelease (rule: Rule oifc) :=
        RqToDownRule rule \/
        RqToUpRule rule \/
        RqToDownRule rule \/
        RsToUpRule rule.

      Definition RqRsRule (rule: Rule oifc) :=
        RqRsGoodAccept rule /\
        RqRsGoodRelease rule.

    End PerObject.

    Definition RqRsObj (obj: Object oifc) :=
      Forall (RqRsRule (obj_idx obj)) (obj_rules obj).
    
    Definition RqRsSys (sys: System oifc) :=
      Forall RqRsObj (sys_objs sys).
    
  End PerSystem.
  
End RqRsTopo.

(*! Invariants *)

Section LockInv.
  Context {oifc: OStateIfc}.
  Variables (gtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrr: RqRsSys gtr oifc sys).

  Section OnMessagePool.
    Variable (msgs: MessagePool Msg).
    
    Definition FullLockInv (oidx: IdxT) (rqi: RqInfo Msg) :=
      let msgs := msgs in
      True.

    Definition HalfLockInv (oidx: IdxT) :=
      True.

    Definition LockFreeInv (oidx: IdxT) :=
      True.

    Definition LockInvORq (oidx: IdxT) (orq: ORq Msg) :=
      match orq@[O] with
      | Some aorq =>
        match aorq@[downRq] with
        | Some downRqi => FullLockInv oidx downRqi
        | None =>
          match aorq@[upRq] with
          | Some upRqi => HalfLockInv oidx
          | None => LockFreeInv oidx
          end
        end
      | None => LockFreeInv oidx
      end.

    Definition LockInvMO (orqs: ORqs Msg) :=
      forall oidx,
        In oidx (map (@obj_idx _) sys.(sys_objs)) ->
        LockInvORq oidx (orqs@[oidx] >>=[[]] (fun orq => orq)).

  End OnMessagePool.
  
  Definition LockInv (st: MState oifc) :=
    LockInvMO st.(bst_msgs) st.(bst_orqs).

End LockInv.


(* Inductive TrsType := RqUp | RqDown | Rs. *)
(* Definition TrsState := M.t TrsType. (* Object index -> TrsType *) *)

(* Definition SemiDisjTrsType (t1 t2: TrsType) := *)
(*   match t1, t2 with *)
(*   | RqUp, Rs => True *)
(*   | _, _ => False *)
(*   end. *)

(* Definition SemiDisjTrsState (ts1 ts2: TrsState) := *)
(*   forall oidx, *)
(*     match ts1@[oidx], ts2@[oidx] with *)
(*     | Some t1, Some t2 => SemiDisjTrsType t1 t2 *)
(*     | _, _ => True *)
(*     end. *)

(* Section SemiDisj. *)
(*   Context {oifc: OStateIfc}. *)
(*   Variables (gtr: DTree) *)
(*             (sys: System oifc). *)

(*   Definition trsStateOfL (lbl: MLabel) := *)
(*     match lbl with *)
(*     | RlblInt oidx _ _ mouts => *)
(*       (oidx, *)
(*        match mouts with *)
(*        | nil => Rs (* Requests are never ignored. *) *)
(*        | (midx, mout) :: _ => *)
(*          if eq_nat_dec (msg_type mout) MRs *)
(*          then Rs *)
(*          else if idxUpEdge gtr midx *)
(*               then RqUp *)
(*               else RqDown *)
(*        end) *)
(*     | _ => (0, RqUp) (* never happens *) *)
(*     end. *)

(*   Fixpoint trsStateOf (hst: MHistory): TrsState := *)
(*     match hst with *)
(*     | nil => [] *)
(*     | lbl :: hst' => *)
(*       let trsl := trsStateOfL lbl in *)
(*       (trsStateOf hst') +[fst trsl <- snd trsl] *)
(*     end. *)
  
(*   Definition RqRsNonConflictingR (rule1 rule2: Rule oifc) := *)
(*     if rule_msg_type_to rule1 ==n MRs then *)
(*       if rule_msg_type_to rule2 ==n MRs then False *)
(*       else True *)
(*     else True. *)

(*   Definition RqRsNonConflictingL (oidx1 ridx1 oidx2 ridx2: IdxT) := *)
(*     oidx1 <> oidx2 \/ *)
(*     (oidx1 = oidx2 /\ *)
(*      forall obj rule1 rule2, *)
(*        In obj (sys_objs sys) -> obj_idx obj = oidx1 -> *)
(*        In rule1 (obj_rules obj) -> rule_idx rule1 = ridx1 -> *)
(*        In rule2 (obj_rules obj) -> rule_idx rule2 = ridx2 -> *)
(*        RqRsNonConflictingR rule1 rule2). *)

(*   Definition RqRsNonConflicting (hst1 hst2: MHistory) := *)
(*     forall oidx1 ridx1 ins1 outs1 oidx2 ridx2 ins2 outs2, *)
(*       In (RlblInt oidx1 ridx1 ins1 outs1) hst1 -> *)
(*       In (RlblInt oidx2 ridx2 ins2 outs2) hst2 -> *)
(*       RqRsNonConflictingL oidx1 ridx1 oidx2 ridx2. *)

(*   Definition SemiDisjHistories (hst1 hst2: MHistory) := *)
(*     exists inits1 ins1 outs1 eouts1 inits2 ins2 outs2 eouts2, *)
(*       Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 /\ *)
(*       Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 /\ *)
(*       SemiDisjTrsState *)
      
(*       RqRsNonConflicting hst1 hst2 /\ *)
(*       DisjList (idsOf ins1) (idsOf ins2) /\ *)
(*       DisjList (idsOf ins1) (idsOf outs2) /\ *)
(*       DisjList (idsOf outs1) (idsOf outs2). *)

(*   Lemma noncontinuous_SemiDisjHistories_NonConflicting: *)
(*     forall st1 st2 hst1 hst2 hst, *)
(*       Reachable (steps step_m) sys st1 -> *)
(*       steps step_m sys st1 (hst2 ++ hst ++ hst1) st2 -> *)
(*       ~ Continuous hst1 hst2 -> *)
(*       SemiDisjHistories hst1 hst2 -> *)
(*       NonConflicting sys hst1 hst2. *)
(*   Proof. *)

(*   Lemma noncontinuous_SemiDisjHistories_MDisjoint: *)
(*     forall st1 st2 hst1 hst2 hst, *)
(*       Reachable (steps step_m) sys st1 -> *)
(*       steps step_m sys st1 (hst2 ++ hst ++ hst1) st2 -> *)
(*       ~ Continuous hst1 hst2 -> *)
(*       SemiDisjHistories hst1 hst2 -> *)
(*       MDisjoint hst1 hst2. *)
(*   Proof. *)
(*     intros. *)
(*     destruct H2 as [inits1 [ins1 [outs1 [eouts1 [inits2 [ins2 [outs2 [eouts2 ?]]]]]]]]. *)
(*     dest. *)
(*     do 8 eexists; repeat split; try eassumption. *)
(*     unfold Continuous in H1. *)

(*   Lemma noncontinuous_SemiDisjHistories_Commutable: *)
(*     forall st1 st2 hst1 hst2 hst, *)
(*       Reachable (steps step_m) sys st1 -> *)
(*       steps step_m sys st1 (hst2 ++ hst ++ hst1) st2 -> *)
(*       ~ Continuous hst1 hst2 -> *)
(*       SemiDisjHistories hst1 hst2 -> *)
(*       Reducible sys (hst2 ++ hst1) (hst1 ++ hst2). *)
(*   Proof. *)
(*     intros. *)
(*     apply nonconflicting_mdisjoint_commutable_atomic. *)
(*     - eauto using noncontinuous_SemiDisjHistories_NonConflicting. *)
(*     - eauto using noncontinuous_SemiDisjHistories_MDisjoint. *)
(*   Qed. *)

(* End SemiDisj. *)

(* Section Pushability. *)
(*   Context {oifc: OStateIfc}. *)
(*   Variables (gtr: DTree) *)
(*             (sys: System oifc). *)
(*   Hypothesis (Hrr: RqRsSys gtr oifc sys). *)

(*   Fixpoint rssOf (hst: MHistory): list IdxT := *)
(*     match hst with *)
(*     | nil => nil *)
(*     | lbl :: hst' => *)
(*       let trsl := trsStateOfL lbl in *)
(*       match snd trsl with *)
(*       | Rs => fst trsl :: rssOf hst' *)
(*       | _ => rssOf hst' *)
(*       end *)
(*     end. *)
  
(*   Definition RqRsLPush (hst1 hst: MHistory) := *)
(*     M.KeysDisj (trsStateOf hst) (rssOf hst1). *)

(*   Definition RqRsRPush (hst1 hst: MHistory) := *)
(*     ~ M.KeysDisj (trsStateOf hst) (rssOf hst1). *)
    
(*   Lemma RqRsRPush_right_push: *)
(*     forall hst1, RqRsRPush hst1 hst1. *)
(*   Proof. *)
(*     intros; red; intros. *)
(*   Admitted. *)

(*   Lemma RqRsLPush_left_push: *)
(*     forall hst1 hst2, *)
(*       ValidContinuous sys hst1 hst2 -> *)
(*       RqRsLPush hst1 hst2. *)
(*   Proof. *)
(*     intros; red. *)
(*   Admitted. *)

(*   Lemma RqRsPush_left_or_right: *)
(*     forall hst1 hst2, *)
(*       ValidContinuous sys hst1 hst2 -> *)
(*       forall st1, *)
(*         Reachable (steps step_m) sys st1 -> *)
(*         forall hsts st2, *)
(*           Forall (AtomicEx msg_dec) hsts -> *)
(*           steps step_m sys st1 (concat (hst2 :: hsts ++ [hst1])) st2 -> *)
(*           Forall (fun hst => ~ Continuous hst1 hst) hsts -> *)
(*           Forall (fun hst => ~ Continuous hst hst2) hsts -> *)
(*           Forall (fun hst => RqRsLPush hst1 hst \/ *)
(*                              RqRsRPush hst1 hst) hsts. *)
(*   Proof. *)
(*     intros. *)
(*   Admitted. *)

(*   Lemma RqRsPush_pushable_1: *)
(*     forall hst1 hst2, *)
(*       ValidContinuous sys hst1 hst2 -> *)
(*       forall st1, *)
(*         Reachable (steps step_m) sys st1 -> *)
(*         forall hsts st2, *)
(*           Forall (AtomicEx msg_dec) hsts -> *)
(*           steps step_m sys st1 (concat (hst2 :: hsts ++ [hst1])) st2 -> *)
(*           Forall (fun hst => ~ Continuous hst1 hst) hsts -> *)
(*           Forall (fun hst => ~ Continuous hst hst2) hsts -> *)
(*           LRPushable sys (RqRsLPush hst1) (RqRsRPush hst1) *)
(*                      (hsts ++ [hst1]). *)
(*   Proof. *)
(*     intros. *)
(*   Admitted. *)

(*   Lemma RqRsPush_pushable_2: *)
(*     forall hst1 hst2, *)
(*       ValidContinuous sys hst1 hst2 -> *)
(*       forall st1, *)
(*         Reachable (steps step_m) sys st1 -> *)
(*         forall hsts st2, *)
(*           Forall (AtomicEx msg_dec) hsts -> *)
(*           steps step_m sys st1 (concat (hst2 :: hsts ++ [hst1])) st2 -> *)
(*           Forall (fun hst => ~ Continuous hst1 hst) hsts -> *)
(*           Forall (fun hst => ~ Continuous hst hst2) hsts -> *)
(*           LRPushable sys (RqRsLPush hst1) (RqRsRPush hst1) *)
(*                      (hst2 :: hsts). *)
(*   Proof. *)
(*     intros. *)
(*   Admitted. *)

(*   Lemma rqrs_well_interleaved_push: *)
(*     WellInterleavedPush sys. *)
(*   Proof. *)
(*     red; intros. *)
(*     exists (RqRsLPush hst1). *)
(*     exists (RqRsRPush hst1). *)
(*     pose proof H; destruct H0. *)
(*     split; [|split; [|split; [|split]]]. *)
(*     - apply RqRsRPush_right_push. *)
(*     - apply RqRsLPush_left_push; auto. *)
(*     - eapply RqRsPush_left_or_right; eauto. *)
(*     - eapply RqRsPush_pushable_1; eauto. *)
(*     - eapply RqRsPush_pushable_2; eauto. *)
(*   Qed. *)

(*   Theorem rqrs_serializable: *)
(*     SerializableSys sys. *)
(*   Proof. *)
(*     apply well_interleaved_serializable. *)
(*     apply well_interleaved_push_ok. *)
(*     apply rqrs_well_interleaved_push. *)
(*   Qed. *)
  
(* End Pushability. *)

(* Section TrsPath. *)
(*   Variables (gtr: DTree). *)

(*   Inductive TrsPath: *)
(*     edge DChn (* an initial edge *) -> *)
(*     edges DChn (* all involved edges *) -> *)
(*     TrsState (* all involved vertices *) -> *)
(*     edges DChn (* end edges *) -> Prop := *)
(*   | TrsPathNil: forall ie, TrsPath ie [ie] [] [ie] *)
(*   | TrsPathRqUp: *)
(*       forall ie es tst ees e v ne, *)
(*         TrsPath ie es tst ees -> *)
(*         In e ees -> edge_to e = Some v -> *)
(*         edge_from ne = Some v -> fst ne.(edge_chn) = DUp -> *)
(*         tst@[v] = None -> *)
(*         TrsPath ie (ne :: es) (tst +[v <- RqUp]) *)
(*                 (ne :: removeOnce (edge_dec dchn_dec) e ees) *)
(*   | TrsPathRqDown: *)
(*       forall ie es tst ees e v nes, *)
(*         TrsPath ie es tst ees -> *)
(*         In e ees -> edge_to e = Some v -> *)
(*         Forall (fun ne => edge_from ne = Some v /\ fst ne.(edge_chn) = DDown) nes -> *)
(*         (tst@[v] = None \/ tst@[v] = Some RqUp) -> *)
(*         TrsPath ie (nes ++ es) (tst +[v <- RqDown]) *)
(*                 (nes ++ removeOnce (edge_dec dchn_dec) e ees) *)
(*   | TrsPathRs: *)
(*       forall ie es tst ees rss v rsb, *)
(*         TrsPath ie es tst ees -> *)
(*         SubList rss ees -> *)
(*         Forall (fun rse => edge_from rse <> None /\ edge_to rse = Some v) rss -> *)
(*         NoDup (map (@edge_from _) rss) -> *)
(*         (tst@[v] = Some RqUp \/ tst@[v] = Some RqDown) -> *)
(*         EdgeIn gtr rsb -> *)
(*         TrsPath ie (rsb :: es) (tst +[v <- Rs]) *)
(*                 (rsb :: removeL (edge_dec dchn_dec) ees rss). *)
  
(* End TrsPath. *)

Close Scope list.
Close Scope fmap.

