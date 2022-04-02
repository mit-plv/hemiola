Hemiola: A Framework for Structural Design and Proof of Cache-Coherence Protocols
=================================================================================

Requirements
------------

### Basic

- Coq 8.14.1 (https://coq.inria.fr/download) to machine-check all the proofs

### Optional

- Kami (https://github.com/mit-plv/kami/tree/master) to compile Hemiola protocols
- OCaml 4.0.4 and Batteries Library for OCaml (2.5.2) to use the Kami-to-Bluespec transliterator
- Bluespec compiler (https://github.com/B-Lang-org/bsc) to simulate or synthesize Bluespec code
- To synthesize Bluespec code on FPGAs
  + Connectal library (http://www.connectal.org/)
  + Vivado 2015.4
  + Xilinx Virtex-7 VC707 Evaluation Kit FPGA

Makefiles
---------

- To machine-check the Coq proofs in Hemiola
  + Check all the framework code: `make -j4` in `./src`
  + Only the library code: `make lib` in `./src`
- To compile Hemiola case-study: `make` in `./syn`
  + The default source protocol is the 3-level noninclusive MESI protocol.
  + It will generate `./syn/CC.bsv`.
  + All the case-study protocols are precompiled in `./syn/integration`:
    * `./syn/integration/CC_L1LL4`: the 2-level noninclusive MESI protocol
    * `./syn/integration/CC_L1L2LL`: the 3-level noninclusive MESI protocol
- To simulate a compiled protocol: `make` in `./syn/integration/sim`
- To synthesize a compiled protocol: `make -j4 build.vc707g2` in `./syn/integration/syn`
