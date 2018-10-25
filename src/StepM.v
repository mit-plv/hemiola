Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.

Open Scope fmap.

Inductive step_m (sys: System): MState -> MLabel -> MState -> Prop :=
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
| SmInt: forall oidx obj rule
                pst nst oss orqs msgs os porq pos norq ins iouts
                (Hifc: ost_ifc os = obj_ifc obj),
    In obj (sys_objs sys) ->
    In rule (obj_rules obj) ->
    oidx = obj_idx obj ->
    
    oss@[oidx] = Some os ->
    orqs@[oidx] = Some porq ->

    Forall (FirstMPI msgs) ins ->
    ValidMsgsIn sys ins ->
    idsOf ins = rule_minds rule ->
    map msg_id (valsOf ins) = rule_msg_ids rule ->

    rule_precond rule (match Hifc with eq_refl => ost_st os end) porq ins ->
    rule_trs rule (match Hifc with eq_refl => ost_st os end) porq ins =
    (pos, norq, iouts) ->
    ValidMsgsOut sys iouts ->

    DisjList (idsOf ins) (idsOf iouts) ->

    pst = {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
    nst = {| bst_oss := oss +[ oidx <- {| ost_st := pos |} ];
             bst_orqs := orqs +[ oidx <- norq ];
             bst_msgs := enqMsgs iouts (deqMsgs (idsOf ins) msgs)
          |} ->

    step_m sys pst (RlblInt oidx (rule_idx rule) ins iouts) nst.

Close Scope fmap.

