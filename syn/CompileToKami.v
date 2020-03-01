Require Import Hemiola.Common Hemiola.Syntax HemiolaDeep.

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
    Definition HMIdx := Bit 4.
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

    Context {var: K.Kind -> Type}.
    Variables (msgIn: var (Struct HMsg))
              (ul: var (Struct UpLock))
              (dl: var (Struct DownLock)).

    Definition compile_Rule_rqrs_prec (rrp: HOPrecR)
               (cont: K.ActionT var K.Void): K.ActionT var K.Void :=
      (match rrp with
       | HRqAccepting => (Assert (!(#msgIn!HMsg@."type")); cont)
       | HRsAccepting => (Assert (#msgIn!HMsg@."type"); cont)
       | HUpLockFree => (Assert (!(#ul!UpLock@."ul_valid")); cont)
       | HDownLockFree => (Assert (!(#dl!DownLock@."dl_valid")); cont)
       | HUpLockMsgId mty mid =>
         (Assert (#ul!UpLock@."ul_valid");
         Assert (#ul!UpLock@."ul_rsb");
         Assert (#ul!UpLock@."ul_msg"!HMsg@."type" == Const _ (ConstBool mty));
         (* Assert (#ul!UpLock@."ul_msg"!HMsg@."id" == $mid); *) (** FIXME *)
         cont)
       | HUpLockMsg =>
         (Assert (#ul!UpLock@."ul_valid"); Assert (#ul!UpLock@."ul_rsb"); cont)
       | HUpLockIdxBack =>
         (Assert (#ul!UpLock@."ul_valid"); Assert (#ul!UpLock@."ul_rsb"); cont)
       | HUpLockBackNone =>
         (Assert (#ul!UpLock@."ul_valid"); Assert (!(#ul!UpLock@."ul_rsb")); cont)
       | HDownLockMsgId mty mid =>
         (Assert (#dl!DownLock@."dl_valid");
         Assert (#dl!DownLock@."dl_rsb");
         Assert (#dl!DownLock@."dl_msg"!HMsg@."type" == Const _ (ConstBool mty));
         (* Assert (#dl!DownLock@."dl_msg"!HMsg@."id" == $mid); *) (** FIXME *)
         cont)
       | HDownLockMsg =>
         (Assert (#dl!DownLock@."dl_valid"); Assert (#dl!DownLock@."dl_rsb"); cont)
       | HDownLockIdxBack =>
         (Assert (#dl!DownLock@."dl_valid"); Assert (#dl!DownLock@."dl_rsb"); cont)
       | HMsgsFrom _ => cont (** TODO: how to deal with multiple input messages? *)
       | HMsgIdsFrom _ => cont (** TODO: ditto *)
       | HMsgIdFromEach _ => cont (** TODO: ditto *)
       | HMsgsFromORq _ => cont (** TODO: ditto *)
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
      | HOPrecRqRs rrprec => compile_Rule_rqrs_prec rrprec cont
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

