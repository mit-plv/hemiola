Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.

Open Scope fmap.

Inductive step_m {oifc} (sys: System oifc):
  MState oifc -> MLabel -> MState oifc -> Prop :=
| SmSlt: forall st, step_m sys st (RlblEmpty _) st
| SmIns: forall pst nst oss orqs msgs eins,
    eins <> nil ->
    ValidMsgsExtIn sys eins ->
    pst = {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
    nst = {| bst_oss := oss;
             bst_orqs := orqs;
             bst_msgs := enqMsgs eins msgs
          |} ->
    step_m sys pst (RlblIns eins) nst
| SmOuts: forall pst nst oss orqs msgs eouts,
    eouts <> nil ->
    Forall (FirstMPI msgs) eouts ->
    ValidMsgsExtOut sys eouts ->
    pst = {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
    nst = {| bst_oss := oss;
             bst_orqs := orqs;
             bst_msgs := deqMsgs (idsOf eouts) msgs
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
    map msg_id (valsOf ins) = rule_msg_ids_from rule ->
    map msg_id (valsOf outs) = rule_msg_ids_to rule ->
    Forall (fun msg => msg_type msg = rule_msg_type_from rule) (valsOf ins) ->
    Forall (fun msg => msg_type msg = rule_msg_type_to rule) (valsOf outs) ->

    rule_precond rule os porq ins ->
    rule_trs rule os porq ins =
    (pos, norq, outs) ->
    ValidMsgsOut sys outs ->

    DisjList (idsOf ins) (idsOf outs) ->

    pst = {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
    nst = {| bst_oss := oss +[ oidx <- pos ];
             bst_orqs := orqs +[ oidx <- norq ];
             bst_msgs := enqMsgs outs (deqMsgs (idsOf ins) msgs)
          |} ->

    step_m sys pst (RlblInt oidx (rule_idx rule) ins outs) nst.

Close Scope fmap.

