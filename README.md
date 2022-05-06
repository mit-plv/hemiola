Hemiola: A DSL and Verification Tools to Guide Design and Proof of Hierarchical Cache-Coherence Protocols
=========================================================================================================

Let's get started
-----------------

Thank you very much for your effort to evaluate our artifact!
In this artifact, we provide Hemiola, a framework embedded in Coq to guide the user to design, verify, and synthesize hardware cache-coherence protocols.
This artifact specifically contains the following items:

- The Hemiola framework (https://github.com/mit-plv/hemiola/tree/cav22-artifact)
  + Framework Coq code
  + Case studies: three hierarchical cache-coherence protocols
  + The Hemiola-to-Kami protocol compiler
- External projects/tools to replicate the evaluation numbers in the paper
  + The Kami framework and its transliterator to Bluespec (https://github.com/mit-plv/kami/tree/cav22-artifact)
  + The Bluespec compiler/simulator (https://github.com/B-Lang-org/bsc)
  + The Riscy processor
    * The cache-coherence protocol (https://github.com/joonwonc/riscy-cc)
    * Library (https://github.com/joonwonc/riscy-OOO)

All the code and tools have already been git-cloned and built for faster evaluation, but it is totally okay trying to rebuild everything for tests.

Directory content
-----------------

- hemiola: **the current directory** containing the framework, case studies, and protocol compiler
  + src: framework code
    * Dsl: the Hemiola DSL
    * Ex: case studies
    * Lib: library used in the framework (e.g., finite maps, tree topology, etc.)
    * System: formal semantics and serializability definitions/lemmas
  + syn: compilation from Hemiola to Bluespec
    * compiler: the Hemiola-to-Kami protocol compiler
    * ex: the MESI protocol instances for evaluation
    * integration: Bluespec wrapper code to run compiled Bluespec protocols
      - sim: simulation build directory
    * predefs: predefined Bluespec code for the MESI protocol instances
- kami: the Kami framework to compile Hemiola protocols to Bluespec implementations
- riscy-cc: the cache-coherence protocol used in the Riscy processors
- riscy-OOO: the Riscy processor code including library code

Artifact evaluation steps
-------------------------

We would appreciate it if you can check the following tasks for evaluation:
- To check all the mechanized proofs in the framework
- To build the two MESI Hemiola protocol implementations, run them with the benchmarks, and compare all the numbers with the ones in the paper

### Scope of artifact evaluation; claim for reusability

In Figure 8 of the paper, we provided two evaluation tables: one for simulation and the other for synthesis.
You should be able to replicate the simulation results but not the synthesis results, since it simply requires an FPGA board (Xilinx VC707), which is definitely neither free nor open-source.
We would like to provide this artifact standalone, and FPGA cannot be provided forever.
That said, we still claim the reusability of this artifact, since 1) the framework code can be reused and 2) the simulation results can be replicated repeatedly within the artifact.

### Checking the proofs

You can simply do `make` (in `hemiola/src`) to check all the framework code and proofs.
It is already done in VM, thus you may want to do `make clean` first.

(Run Xfce Terminal)
`hemiola@hemiola-VirtualBox:~$ cd Artifact/hemiola/src`
`hemiola@hemiola-VirtualBox:~/Artifact/hemiola/src$ make clean; make`

It should finish without any errors, indicating that all the proofs are valid.
Using the default VM resource setting (4GB RAM and two cores), it takes around 2.5 hours.

### Replication of the simulation results

#### Generation of the two MESI implementation instances

In order to replicate the simulation results (provided in Figure 8 of the paper), we first need to compile the MESI case-study protocol and generate two Bluespec implementation instances (shown as Hemiola2 and Hemiola3 in Figure 8).
They are already provided in VM: `hemiola/syn/integration/CC_L1LL4.bsv` (Hemiola2) and `hemiola/syn/integration/CC_L1L2LL.bsv` (Hemiola3).

For replication check, you can do `make` to compile/generate those files.

(Assuming `hemiola/src` is fully compiled by `make`)
`hemiola@hemiola-VirtualBox:~$ cd Artifact/hemiola/syn`
`hemiola@hemiola-VirtualBox:~/Artifact/hemiola/syn$ make mesi_l2_bsv` (for Hemiola2)
(Do `make mesi_l3_bsv` for Hemiola3)

Without any errors, it should generate `hemiola/syn/CC.bsv` for each `make`, taking around 10 minutes.
You may want to do `diff` between the newly generated Bluespec implementation and the one already provided, for example:

(After doing `make mesi_l2_bsv`)
`hemiola@hemiola-VirtualBox:~/Artifact/hemiola/syn$ diff CC.bsv ./integration/CC_L1LL4.bsv`
`hemiola@hemiola-VirtualBox:~/Artifact/hemiola/syn$`
(No output means the two files are same)

#### Simulation of the instances

Now we are ready to replicate the simulation results.
Here also simple various `make`s will build executables compiled by the Bluespec compiler.

1. First of all, we need to set the instance to generate the simulation results.
   `hemiola@hemiola-VirtualBox:~$ cd Artifact/hemiola/syn/integration/sim`
   `hemiola@hemiola-VirtualBox:~/Artifact/hemiola/syn/integration/sim$ make set_cc_mesi_l2` (for Hemiola2)
   (Do `make set_cc_mesi_l3` for Hemiola3)
   The `make` above will simply change the symbolic link `hemiola/syn/integration/HCC.bsv` accordingly.

2. Now build the executable by doing the following `make`s.
   Different `make` is required for each benchmark shown in Figure 8 of the paper.
   - For all-shared: `make build_all_shared`
   - For pair-shared: `make build_pair_shared`
   - For ex:sh=1:1: `make build_ex_sh_1`
   - For ex:sh=4:1: `make build_ex_sh_2`
   - The first `make` builds the executable from nothing, taking around 3 minutes.
     Later `make`s will be much faster, around a minute.

3. With a successful build, we should have `hemiola/syn/integration/sim/Top`; running it will show the result:
   `hemiola@hemiola-VirtualBox:~/Artifact/hemiola/syn/integration/sim$ ./Top`
   (After around a minute)
   `Test done, #trs/cycle: xxxxxx / 500000`
   (Type Ctrl+C to quit)

You may want to repeat the steps 1 and 2 repeatedly (for each instance/benchmark) to confirm that the numbers match the ones in the paper.

#### (Optional) Simulation of the comparison target

This artifact is also able to replicate the simulation results of the comparison target (shown as RiscyOO in Figure 8 of the paper).

1. Go to the Riscy cache-coherence protocol project directory.
   `hemiola@hemiola-VirtualBox:~$ cd Artifact/riscy-cc/sim-hemiola`
   `hemiola@hemiola-VirtualBox:~/Artifact/riscy-cc/sim-hemiola$`

2. Build the executable by doing the following `make`s.
   Different `make` is required for each benchmark shown in Figure 8 of the paper.
   - For all-shared: `make build_all_shared`
   - For pair-shared: `make build_pair_shared`
   - For ex:sh=1:1: `make build_ex_sh_1`
   - For ex:sh=4:1: `make build_ex_sh_2`
   - The first `make` builds the executable from nothing, taking around 10 minutes.
     Later `make`s will be much faster, around a minute.

3. With a successful build, we should have `riscy-cc/sim-hemiola/Top`; running it will show the result:
   (Since the Riscy protocol prints verbose logs in simulation, we will want to ignore such logs like below)
   `hemiola@hemiola-VirtualBox:~/Artifact/riscy-cc/sim-hemiola$ ./Top >/dev/null`
   (After around a minute)
   `Test done, #trs/cycle: xxxxxx / 500000`
   (Type Ctrl+C to quit)

You may want to repeat the step 2 repeatedly (for each benchmark) to confirm that the numbers match the ones in the paper.

Appendix: tools installed in VM
-------------------------------

- OPAM (OCaml Package Manaager, https://opam.ocaml.org/)
  + coq 8.14.1
  + ocaml 4.14.0
  + ocamlbuild 0.14.1
- Bluespec Compiler, version 2022.01
