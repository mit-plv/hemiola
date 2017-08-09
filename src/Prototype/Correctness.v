Require Import Bool List String Peano_dec Eqdep.
Require Import Tactics FMap Language SingleValue Transaction Simulation.
Require Import FunctionalExtensionality.

Open Scope fmap.

Section System.
  Variables extIdx1 extIdx2: nat.

  Local Definition IState := State SVMType SVM ImplState.
  Local Definition SState := State SVMType SVM SpecState.

  (* The first intuition: if one of [ValStatus]s in objects is [Valid], then
   * that object has the value that should be mapped to the spec.
   * It implicitly assumes that only one object has a [Valid] flag.
   *)
  Definition validValue (p c1 c2: ImplState) :=
    match impl_status p with
    | Valid => Some (impl_value p)
    | _ => match impl_status c1 with
           | Valid => Some (impl_value c1)
           | _ => match impl_status c2 with
                  | Valid => Some (impl_value c2)
                  | _ => None
                  end
           end
    end.

  (* We will give a simulation relation that ignores all "unfinished transactions",
   * thus the [Messages]-mapping should be just about external incoming queues.
   *)
  Definition specMsgs (eToC1 eToC2: Queue SVMType SVM): Messages SVMType SVM :=
    match eToC1 with
    | nil =>
      match eToC2 with
      | nil => []
      | _ => [] +[child1Idx <- [] +[extIdx1 <- [] +[specChn <- eToC1] ] ]
      end
    | _ => [] +[child1Idx <- [] +[extIdx1 <- [] +[specChn <- eToC1] ] ]
           +[child2Idx <- [] +[extIdx2 <- [] +[specChn <- eToC2] ] ]
    end.

  Local Definition sim (ist: IState) (sst: SState): Prop.
  Proof.
    destruct ist as [ioss imsgs].
    refine (exists iosp iosc1 iosc2,
               ioss = []+[child2Idx <- iosc2]+[child1Idx <- iosc1]+[parentIdx <- iosp] /\ _).
    set (findM extIdx1 child1Idx implChn imsgs) as eToC1.
    set (findM extIdx2 child1Idx implChn imsgs) as eToC2.

    refine (match validValue iosp iosc1 iosc2 with
            | Some v => sst = {| st_oss := []+[specIdx <- v];
                                 st_msgs := specMsgs eToC1 eToC2 |}
            | None => _
            end).

    (* If we cannot find the valid value, that means [impl] is in a transient 
     * state. Now in order to find the valid value, we have to investigate 
     * messages, "carefully considering transactions and interleavings."
     *
     * Below cases (and the order among them) requires a number of invariants
     * that are mostly about transient states and interleavings. They are not
     * proven here; just let's imagine how complicated they are.
     *)
    set (findM child1Idx parentIdx implChn imsgs) as c1ToP.
    set (findM child2Idx parentIdx implChn imsgs) as c2ToP.
    set (findM parentIdx child1Idx implChn imsgs) as pToC1.
    set (findM parentIdx child2Idx implChn imsgs) as pToC2.

    (* In this simple protocol, if we find a [InvResp] message then we can find
     * the valid value from this message.
     *)
    destruct (find (fun m => match msg_value m with
                             | InvResp _ => true
                             | _ => false
                             end) (c1ToP ++ c2ToP)) as [invRespM|];
      [exact (exists v, msg_value invRespM = InvResp v /\
                        sst = {| st_oss := []+[specIdx <- v];
                                 st_msgs := specMsgs eToC1 eToC2 |})|].

    (* If there are no [InvResp] messages, then we need to find a [GetResp]
     * message (from the parent) secondly.
     *)
    destruct (find (fun m => match msg_value m with
                             | GetResp _ => true
                             | _ => false
                             end) (c1ToP ++ c2ToP)) as [getRespM|];
      [exact (exists v, msg_value getRespM = GetResp v /\
                        sst = {| st_oss := []+[specIdx <- v];
                                 st_msgs := specMsgs eToC1 eToC2 |})|].

    (* The third case is to find a [SetResp] message (from the parent). In
     * this case, the other child (which is not getting the [SetResp]) still
     * has the value.
     *)
    destruct (find (fun m => match msg_value m with
                             | SetResp => true
                             | _ => false
                             end) c1ToP);
      [exact (sst = {| st_oss := []+[specIdx <- impl_value iosc2];
                       st_msgs := specMsgs eToC1 eToC2 |})|].
    destruct (find (fun m => match msg_value m with
                             | SetResp => true
                             | _ => false
                             end) c2ToP);
      [exact (sst = {| st_oss := []+[specIdx <- impl_value iosc1];
                       st_msgs := specMsgs eToC1 eToC2 |})|].

    (* No more cases left *)
    exact False.
  Defined.

  Axiom sim_simulates:
    Simulates svmT_dec svm_dec sim (impl extIdx1 extIdx2) (spec extIdx1 extIdx2).

  Theorem impl_refines_spec:
    Refines svmT_dec svm_dec (impl extIdx1 extIdx2) (spec extIdx1 extIdx2).
  Proof.
    apply simulation_implies_refinement with (sim:= sim).
    - apply sim_simulates.
    - do 3 eexists; split; reflexivity.
  Qed.

End System.

