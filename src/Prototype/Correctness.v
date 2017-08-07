Require Import Bool List String Peano_dec Eqdep.
Require Import FMap Language SingleValue Transaction Simulation.
Require Import FunctionalExtensionality.

Open Scope fmap.

Section System.
  Variables extIdx1 extIdx2: nat.

  Local Definition IState := State SVMType SVM ImplState.
  Local Definition SState := State SVMType SVM SpecState.

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

  Local Definition sim (ist: IState) (sst: SState): Prop.
  Proof.
    destruct ist as [ioss imsgs].
    refine (exists iosp iosc1 iosc2,
               ioss = []+[child2Idx <- iosc2]+[child1Idx <- iosc1]+[parentIdx <- iosp] /\ _).

    refine (match validValue iosp iosc1 iosc2 with
            | Some v => _
            | None => _
            end).
    - exact (sst = {| st_oss := []+[specIdx <- v];
                      st_msgs := imsgs |}).
    - exact True. (* TODO *)
  Defined.

  Theorem sim_simulates:
    Simulates svmT_dec svm_dec sim (impl extIdx1 extIdx2) (spec extIdx1 extIdx2).
  Proof.
    unfold Simulates; intros.
    
  Admitted.

  Theorem impl_refines_spec:
    Refines svmT_dec svm_dec (impl extIdx1 extIdx2) (spec extIdx1 extIdx2).
  Proof.
    apply simulation_implies_refinement with (sim:= sim).
    - apply sim_simulates.
    - do 3 eexists; split; reflexivity.
  Qed.

  (* Theorem impl_linear: Linear (impl extIdx1 extIdx2). *)

End System.

