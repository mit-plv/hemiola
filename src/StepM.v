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
             bst_msgs := enqMsgs eins msgs
          |} ->
    step_m sys pst (RlblIns eins) nst
| SmOuts: forall pst nst oss orqs msgs eouts,
    eouts <> nil ->
    Forall (fun idm => FirstMP (fst idm) (snd idm) msgs) eouts ->
    ValidMsgsExtOut sys eouts ->
    pst = {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
    nst = {| bst_oss := oss;
             bst_orqs := orqs;
             bst_msgs := deqMsgs (idsOf eouts) msgs
          |} ->
    step_m sys pst (RlblOuts eouts) nst
| SmInt: forall pst nst oss orqs msgs oidx os porq pos norq ins rule iouts,
    oidx = rule_oidx rule ->
    In oidx (oindsOf sys) ->
    oss@[oidx] = Some os ->
    orqs@[oidx] = Some porq ->

    Forall (fun idm => FirstMP (fst idm) (snd idm) msgs) ins ->
    ValidMsgsIn sys ins ->
    idsOf ins = rule_minds rule ->

    In rule (sys_rules sys) ->
    rule_precond rule os porq ins ->
    rule_postcond rule os porq ins pos norq iouts ->
    ValidMsgsOut iouts ->

    pst = {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
    nst = {| bst_oss := oss +[ oidx <- pos ];
             bst_orqs := orqs +[ oidx <- norq ];
             bst_msgs := enqMsgs iouts (deqMsgs (idsOf ins) msgs)
          |} ->

    step_m sys pst (RlblInt (Some rule) ins iouts) nst.

