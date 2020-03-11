Require Import Hemiola.Common Hemiola.Index Hemiola.Syntax.
Require Import Hemiola.Ex.TopoTemplate.
Require Import HemiolaDeep.

Require Import Kami.Lib.Struct Kami.

Set Implicit Arguments.

Import MonadNotations.
Module H := Hemiola.Syntax.
Module K := Kami.Syntax.

Section Compile.
  Context `{DecValue} `{oifc: OStateIfc}.

  Definition compile_OState_init: list K.RegInitT :=
    nil. (** TODO *)

  Section PreEval.

    Definition HOIdx := Bit 8.
    Definition HMIdx := Bit 5.
    Definition HValue := Bit 32.

    Definition HMsg :=
      STRUCT { "id" :: HMIdx;
               "type" :: Bool;
               "value" :: HValue }.

    Definition UpLock :=
      STRUCT { "ul_valid" :: Bool;
               "ul_rsb" :: Bool;
               "ul_msg" :: Struct HMsg;
               "ul_rssFrom" :: Array HOIdx 8;
               "ul_rsbTo" :: HOIdx }.

    Definition DownLock :=
      STRUCT { "dl_valid" :: Bool;
               "dl_rsb" :: Bool;
               "dl_msg" :: Struct HMsg;
               "dl_rssFrom" :: Array HOIdx 8;
               "dl_rsbTo" :: HOIdx }.

    Fixpoint idxToNat (deg: nat) (midx: IdxT): nat :=
      match midx with
      | nil => 0
      | d :: ds => d + deg * (idxToNat deg ds)
      end.
    Notation "% i %: d" :=
      (Const _ (natToWord _ (idxToNat d i))) (at level 5): kami_expr_scope.

    Context {var: K.Kind -> Type}.
    Variables (oidx: IdxT)
              (msgIn: var (Struct HMsg))
              (ul: var (Struct UpLock))
              (dl: var (Struct DownLock)).

    Definition compile_Rule_rqrs_prec (rrp: HOPrecR)
               (midxCont: option IdxT) (cont: K.ActionT var K.Void)
      : option IdxT (* midx *) * K.ActionT var K.Void :=
      (match rrp with
       | HRqAccepting => (None, Assert (!(#msgIn!HMsg@."type")); cont)
       | HRsAccepting => (None, Assert (#msgIn!HMsg@."type"); cont)
       | HUpLockFree => (None, Assert (!(#ul!UpLock@."ul_valid")); cont)
       | HDownLockFree => (None, Assert (!(#dl!DownLock@."dl_valid")); cont)
       | HUpLockMsgId mty mid =>
         (None,
          Assert (#ul!UpLock@."ul_valid");
         Assert (#ul!UpLock@."ul_rsb");
         Assert (#ul!UpLock@."ul_msg"!HMsg@."type" == Const _ (ConstBool mty));
         Assert (#ul!UpLock@."ul_msg"!HMsg@."id" == %mid%:5);
         cont)
       | HUpLockMsg =>
         (None, Assert (#ul!UpLock@."ul_valid"); Assert (#ul!UpLock@."ul_rsb"); cont)
       | HUpLockIdxBack =>
         (None, Assert (#ul!UpLock@."ul_valid"); Assert (#ul!UpLock@."ul_rsb"); cont)
       | HUpLockBackNone =>
         (None, Assert (#ul!UpLock@."ul_valid"); Assert (!(#ul!UpLock@."ul_rsb")); cont)
       | HDownLockMsgId mty mid =>
         (None,
          Assert (#dl!DownLock@."dl_valid");
         Assert (#dl!DownLock@."dl_rsb");
         Assert (#dl!DownLock@."dl_msg"!HMsg@."type" == Const _ (ConstBool mty));
         Assert (#dl!DownLock@."dl_msg"!HMsg@."id" == %mid%:5);
         cont)
       | HDownLockMsg =>
         (None, Assert (#dl!DownLock@."dl_valid"); Assert (#dl!DownLock@."dl_rsb"); cont)
       | HDownLockIdxBack =>
         (None, Assert (#dl!DownLock@."dl_valid"); Assert (#dl!DownLock@."dl_rsb"); cont)
       | HMsgFromParent => (Some (downTo oidx), cont)
       | HMsgFromChild cidx => (Some (rsUpFrom cidx), cont)
       | HMsgIdFrom msgId =>
         (None, Assert (#msgIn!HMsg@."id" == %msgId%:5); cont)
       end)%kami_action.
    
    Definition compile_Rule_prop_prec (pp: HOPrecP)
               (cont: K.ActionT var K.Void): K.ActionT var K.Void :=
      cont. (** TODO *)

    Fixpoint compile_Rule_prec (rp: HOPrec)
             (cont: K.ActionT var K.Void): K.ActionT var K.Void :=
      match rp with
      | HOPrecAnd prec1 prec2 =>
        let crule1 := compile_Rule_prec prec1 cont in
        compile_Rule_prec prec2 crule1
      | HOPrecRqRs rrprec =>
        snd (compile_Rule_rqrs_prec rrprec None cont) (** FIXME *)
      | HOPrecProp pprec => compile_Rule_prop_prec pprec cont
      end.

    Definition compile_Rule_trs (rtrs: HOTrs): K.Action K.Void :=
      cheat _.

  End PreEval.

  Definition compile_Rule (rule: {sr: H.Rule & HRule sr}):
    Attribute (K.Action K.Void) :=
    (* let ctrs := compile_Rule_trs (hrule_trs (projT2 rule)) in *)
    (* let crule := compile_Rule_prec (hrule_precond (projT2 rule)) ctrs in *)
    (* {| attrName := ""; attrType := crule |}. *)
    cheat _. (** FIXME *)
  
  Definition compile_Rules (rules: list {sr: H.Rule & HRule sr}):
    list (Attribute (K.Action K.Void)) :=
    map compile_Rule rules.
  
  Definition compile_Object (obj: HObject): option K.Modules :=
    let cregs := compile_OState_init in
    let crules := compile_Rules (hobj_rules obj) in
    Some (K.Mod cregs crules nil).
  
  Fixpoint compile_Objects (objs: list HObject): option Kami.Syntax.Modules :=
    match objs with
    | nil => None
    | obj :: objs' =>
      (cmod <-- compile_Object obj;
      cmods <-- compile_Objects objs';
      Some (ConcatMod cmod cmods))
    end.
  
  Definition compile_System (sys: HSystem): option Kami.Syntax.Modules :=
    compile_Objects sys.(hsys_objs).

End Compile.

