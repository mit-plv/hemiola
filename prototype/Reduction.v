Require Import List String Peano_dec.
Require Import FMap Language Transaction.

Set Implicit Arguments.

Section Reduction.
  Context {MsgT ValT StateT: Type}.
  Hypothesis (msgT_dec : forall m1 m2 : MsgT, {m1 = m2} + {m1 <> m2}).
  Hypothesis (valT_dec : forall v1 v2 : ValT, {v1 = v2} + {v1 <> v2}).

  Local Notation Msg := (Msg MsgT ValT).
  Local Notation MsgId := (MsgId MsgT).
  Local Notation Label := (Label MsgT ValT).

  Definition History4 (hst: list Msg) (msg1 msg2 msg3 msg4: Msg)
             (shst1 shst2 shst3 shst4 shst5: list Msg) :=
    hst = shst5 ++ msg4 :: shst4 ++ msg3 :: shst3 ++ msg2 :: shst2 ++ msg1 :: shst1.

  Definition Interleaving21 (hst: list Msg) (rq1 rs1 rq2 rs2: Msg)
             (shst1 shst2 shst3 shst4 shst5: list Msg) :=
    isTrsPair msgT_dec (msg_id rq1) (msg_id rs1) = true /\
    isTrsPair msgT_dec (msg_id rq2) (msg_id rs2) = true /\
    History4 hst rq1 rq2 rs1 rs2 shst1 shst2 shst3 shst4 shst5.
  
  Definition Interleaving22 (hst: list Msg) (rq1 rs1 rq2 rs2: Msg)
             (shst1 shst2 shst3 shst4 shst5: list Msg) :=
    isTrsPair msgT_dec (msg_id rq1) (msg_id rs1) = true /\
    isTrsPair msgT_dec (msg_id rq2) (msg_id rs2) = true /\
    History4 hst rq1 rq2 rs2 rs1 shst1 shst2 shst3 shst4 shst5.

  Definition Interleaving2 (hst: list Msg) (rq1 rs1 rq2 rs2: Msg)
             (shst1 shst2 shst3 shst4 shst5: list Msg) :=
    Interleaving21 hst rq1 rs1 rq2 rs2 shst1 shst2 shst3 shst4 shst5 \/
    Interleaving22 hst rq1 rs1 rq2 rs2 shst1 shst2 shst3 shst4 shst5.
    
  Definition Sequential2 (hst: list Msg) (rq1 rs1 rq2 rs2: Msg)
             (shst1 shst2 shst3 shst4 shst5: list Msg) :=
    isTrsPair msgT_dec (msg_id rq1) (msg_id rs1) = true /\
    isTrsPair msgT_dec (msg_id rq2) (msg_id rs2) = true /\
    History4 hst rq1 rs1 rq2 rs2 shst1 shst2 shst3 shst4 shst5.

  Definition Reducible2 (sys: System MsgT ValT StateT) :=
    forall hst,
      History msgT_dec valT_dec sys hst ->
      forall rq1 rs1 rq2 rs2 shst1 shst2 shst3 shst4 shst5,
        Interleaving2 hst rq1 rs1 rq2 rs2 shst1 shst2 shst3 shst4 shst5 ->
        exists hst',
          History msgT_dec valT_dec sys hst' /\
          Sequential2 hst' rq1 rs1 rq2 rs2 shst1 shst2 shst3 shst4 shst5.

  Section Facts.

    Lemma singleton_reducible_linear:
      forall obj,
        Reducible2 (obj :: nil) ->
        Linear msgT_dec valT_dec (obj :: nil).
    Proof.
    Admitted.

  End Facts.
  
End Reduction.

