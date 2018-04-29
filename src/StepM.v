Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.

Inductive step_m (sys: System): MState -> MLabel -> MState -> Prop :=
| SmSlt: forall st, step_m sys st (emptyRLabel _) st
| SmIns: forall pst nst oss orqs msgs eins,
    eins <> nil ->
    ValidMsgsExtIn sys eins ->
    pst = {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
    nst = {| bst_oss := oss;
             bst_orqs := orqs;
             bst_msgs := distributeMsgs eins msgs
          |} ->
    step_m sys pst (RlblIns eins) nst
| SmOuts: forall pst nst oss orqs msgs eouts,
    eouts <> nil ->
    Forall (FirstMP msgs) eouts ->
    ValidMsgsExtOut sys eouts ->
    pst = {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
    nst = {| bst_oss := oss;
             bst_orqs := orqs;
             bst_msgs := removeMsgs eouts msgs
          |} ->
    step_m sys pst (RlblOuts eouts) nst
| SmInt: forall pst nst oss orqs msgs oidx os porq pos norq ins rule iouts,
    oidx = rule_oidx rule ->
    In oidx (indicesOf sys) ->
    oss@[oidx] = Some os ->
    orqs@[oidx] = Some porq ->

    Forall (FirstMP msgs) ins ->
    ValidMsgsIn oidx ins ->
    map (fun tmsg => msg_id tmsg) ins = rule_mids rule ->

    In rule (sys_rules sys) ->
    rule_precond rule os porq ins ->
    rule_postcond rule os porq ins pos norq iouts ->
    ValidMsgsOut oidx iouts ->

    pst = {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
    nst = {| bst_oss := oss +[ oidx <- pos ];
             bst_orqs := orqs +[ oidx <- norq ];
             bst_msgs := distributeMsgs iouts (removeMsgs ins msgs)
          |} ->

    step_m sys pst (RlblInt (Some rule) ins iouts) nst.

