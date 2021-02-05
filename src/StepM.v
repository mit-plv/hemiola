Require Import Bool List String PeanoNat.
Require Import Common FMap Syntax Semantics.

Local Open Scope fmap.

Inductive step_m `{DecValue} `{OStateIfc} (sys: System):
  State -> RLabel -> State -> Prop :=
| SmSlt: forall st, step_m sys st RlblEmpty st
| SmIns: forall pst nst oss orqs msgs eins,
    eins <> nil ->
    ValidMsgsExtIn sys eins ->
    pst = {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
    nst = {| st_oss := oss;
             st_orqs := orqs;
             st_msgs := enqMsgs eins msgs
          |} ->
    step_m sys pst (RlblIns eins) nst
| SmOuts: forall pst nst oss orqs msgs eouts,
    eouts <> nil ->
    Forall (FirstMPI msgs) eouts ->
    ValidMsgsExtOut sys eouts ->
    pst = {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
    nst = {| st_oss := oss;
             st_orqs := orqs;
             st_msgs := deqMsgs (idsOf eouts) msgs
          |} ->
    step_m sys pst (RlblOuts eouts) nst
| SmInt: forall oidx obj rule pst nst oss orqs msgs os porq pos norq ins outs,
    In obj (sys_objs sys) ->
    In rule (obj_rules obj) ->
    oidx = obj_idx obj ->

    oss@[oidx] = Some os ->
    orqs@[oidx] = Some porq ->

    Forall (FirstMPI msgs) ins ->
    ValidMsgsIn sys ins ->

    rule_precond rule os porq ins ->
    rule_trs rule os porq ins = (pos, norq, outs) ->
    ValidMsgsOut sys outs ->

    DisjList (idsOf ins) (idsOf outs) ->

    pst = {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
    nst = {| st_oss := oss +[ oidx <- pos ];
             st_orqs := orqs +[ oidx <- norq ];
             st_msgs := enqMsgs outs (deqMsgs (idsOf ins) msgs)
          |} ->

    step_m sys pst (RlblInt oidx (rule_idx rule) ins outs) nst.
