From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
From mathcomp Require Import fingroup finset. 
From mathcomp Require Import cyclic zmodp.

Require Import Posrat Premeas Meas Aux Logic finfun_fixed String SSRString SeqOps RLems Tacs DerivedTacs.

Section SecChan.
  Context (msg : finType) (ctxt : finType) (key : finType).
  Context (mzero : msg).
  Context (keyGen : meas key).
  Context (enc : msg -> key -> meas ctxt).
  Context (dec : ctxt -> key -> msg).
  Context (leak : ctxt -> nat).
  Context (dec_correct : forall m k c, c \in support (enc m k) -> dec c k = m).

  Inductive ty :=
  | tyMsg
  | tyKey
  | tyCtx
  | tyUnit
  | tyPair : ty -> ty -> ty.

  Definition seq5 := [:: 0; 1; 2; 3].
  Notation InSeqSub s x := (@SeqSub _ s x is_true_true).

  Fixpoint ty_enc (t : ty) : GenTree.tree (seq_sub seq5) :=
    match t with
    | tyMsg => GenTree.Leaf (InSeqSub seq5 0)
    | tyKey => GenTree.Leaf (InSeqSub seq5 1)
    | tyCtx => GenTree.Leaf (InSeqSub seq5 2)
    | tyUnit => GenTree.Leaf  (InSeqSub seq5 3)
    | tyPair t1 t2 => GenTree.Node 0 [:: ty_enc t1; ty_enc t2]
    end.

  Print seq_sub.

  Fixpoint ty_dec (t : GenTree.tree (seq_sub seq5)) : ty :=
    match t with
    | GenTree.Leaf n => match (ssval n) with
                          | 0 => tyMsg
                          | 1 => tyKey
                          | 2 => tyCtx
                          | 3 => tyUnit
                          | _ => tyMsg
                                   end
      | GenTree.Node _ (x :: y :: _) => tyPair (ty_dec x) (ty_dec y)
      | _ => tyMsg
               end.

  Lemma ty_can : cancel ty_enc ty_dec.
    move => x.
    induction x; rewrite //=.
    rewrite IHx1 IHx2 //=.
  Qed.
  Canonical ty_eq := EqType ty (CanEqMixin ty_can).
  Canonical ty_ch := ChoiceType ty (CanChoiceMixin ty_can).

  Fixpoint denomTy (t : ty) : choiceType :=
    match t with
      | tyMsg => msg
      | tyKey => key
      | tyCtx => ctxt
      | tyUnit => [choiceType of unit]
      | tyPair t1 t2 => [choiceType of (denomTy t1) * (denomTy t2)]
                          end.

  Local Instance ty_type : type [eqType of ty].
   econstructor.
   instantiate (1 := denomTy).
   instantiate (1 := tyPair).
   done.
 Defined.

  Definition rl := rlist [choiceType of string] [choiceType of ty].

  Open Scope string_scope.

  Definition realSender : rl :=
    [::
       inr ("inS", tyMsg);
       inr ("keyS", tyKey);
       [:: ("inS", tyMsg); ("keyS", tyKey)] ~> ("sendS", tyCtx) vis enc].

  Definition realReceiver : rl :=
    [::
       inr ("keyR", tyKey);
       inr ("deliv", tyCtx);
       [:: ("deliv", tyCtx); ("keyR", tyKey)] ~> ("outR", tyMsg) dvis dec].

  Definition realNet : rl :=
    [:: inr ("sendS", tyCtx);
       [:: ("sendS", tyCtx)] ~> ("leak", tyCtx) dvis id;
       inr ("ans", tyUnit);
       [:: ("sendS", tyCtx); ("ans", tyUnit)] ~> ("deliv", tyCtx) dvis (fun x _ => x)].

  Definition FKey : rl :=
    [:: [::] ~> ("keygen", tyKey) hid keyGen;
        [:: ("keygen", tyKey)] ~> ("keyS", tyKey) dvis id;
        [:: ("keygen", tyKey)] ~> ("keyR", tyKey) dvis id].

  Definition realNoCorr :=
    realSender ||| realReceiver ||| realNet ||| FKey.

  Definition idealSender :=
    [:: inr ("inS", tyMsg);
        [:: ("inS", tyMsg)] ~> ("sendS", tyMsg) dvis id].

  Definition idealReceiver :=
    [:: inr ("deliv", tyMsg);
       [:: ("deliv", tyMsg)] ~> ("outR", tyMsg) dvis id].

  Definition FSec :=
    [:: inr ("sendS", tyMsg);
       [:: ("sendS", tyMsg)] ~> ("query", tyUnit) dvis (fun _ => tt);
       inr ("ans", tyUnit);
       [:: ("sendS", tyMsg); ("ans", tyUnit)] ~> ("deliv", tyMsg) dvis (fun x _ => x)].

  Definition idealNoCorr :=
    idealSender ||| idealReceiver ||| FSec.

  Definition CPA (b : bool) :=
    [::
       inr ("inCPA", tyMsg);
       [::] ~> ("keygen", tyKey) hid keyGen;
       [:: ("inCPA", tyMsg); ("keygen", tyKey)] ~> ("ct", tyCtx) vis (fun m k => if b then (enc m k) else (enc mzero k))].
                              
    Definition cpa_sim := [::
            inr ("inS", tyMsg);
            inr ("ans", tyUnit);
            [:: ("inS", tyMsg)] ~> ("inCPA", tyMsg) dvis id;
            inr ("ct", tyCtx);
            [:: ("ct", tyCtx)] ~> ("leak", tyCtx) dvis id;
            [:: ("inS", tyMsg); ("ans", tyUnit)] ~> ("outR", tyMsg) dvis (fun x _ => x)].

    Definition rps_nocorr_sim :=
      [:: inr ("query", tyUnit);
         [::] ~> ("keygen", tyKey) hid keyGen;
          [:: ("query", tyUnit); ("keygen", tyKey)] ~> ("leak", tyCtx) vis (fun _  k => enc mzero k)].

    (* TODO split up so QED finishes *)

  Theorem noCorr_1 : CPA true ~~> CPA false -> realNoCorr ~~> (cpa_sim ||| (CPA true)).
    intros.
    rewrite /realNoCorr /rlist_comp_hide; vm_compute RChans; simpl.
    autosubst_at leftc "deliv" "outR".
    remove_at leftc "deliv".
    autosubst_at leftc "keyS" "sendS".
    remove_at leftc "keyS".
    autosubst_at leftc "keyR" "outR".
    remove_at leftc "keyR".
    autosubst_at rightc "inCPA" "ct".
    remove_at rightc "inCPA".
    rename_at leftc "sendS" "ct".
    arg_move_at leftc "ct" "inS" 0.
    
    trans_at leftc "ct" "leak" "keygen" tyKey.
    r_ext_at leftc "outR" (rbind [:: ("keygen", tyKey); ("ct", tyCtx)] [:: ("ans", tyUnit)] ("tmp", tyMsg) ("outR", tyMsg) (fun x y => ret (dec y x)) (fun (x : msg) _ _ _ => ret x)).

        intros; unlock rbind; rewrite //=.
        msimp; done.
    unfold_at leftc "outR".

    trans_rev_at leftc "tmp" "outR" "keygen".
    trans_rev_at leftc "tmp" "outR" "ct".
    pair_at leftc "leak" "tmp" "X".
    trans_rev_at leftc "X" "leak" "ct".
    trans_rev_at leftc "X" "tmp" "ct".
    trans_at leftc "ct" "X" "inS" tyMsg.
    r_move_at leftc "ct" 0.
    r_move_at leftc "X" 1.
    arg_move_at leftc "X" "ct" 0.
    fold_at leftc.
    r_ext_at leftc "X" (fun m k => n2 <- enc m k; ret (n2, m)).
        intros.
        apply mbind_eqP.
        intros; msimp.
        erewrite dec_correct.
        apply: erefl.
        done.
   unfold_bind2_at leftc "X" "ct" tyCtx.
   unfold_at leftc "X".
   autosubst_at leftc "X" "leak".
   autosubst_at leftc "X" "tmp".
   remove_at leftc "X".
   autosubst_at leftc "tmp" "outR".
   remove_at leftc "tmp".
   trans_rev_at leftc "ct" "leak" "keygen".
   trans_rev_at leftc "ct" "leak" "inS".
   hid_str_at leftc "ct" "outR".
   hid_str_at leftc "keygen" "outR".
   align.
   reflexivity.
Qed.

  Theorem noCorr_2 : (cpa_sim ||| (CPA false)) ~~> (rps_nocorr_sim ||| idealNoCorr).
    rewrite /realNoCorr /rlist_comp_hide; vm_compute RChans; simpl.
    autosubst_at rightc "query" "leak".
    remove_at rightc "query".
    autosubst_at rightc "sendS" "leak".
    autosubst_at rightc "sendS" "deliv".
    remove_at rightc "sendS".
    autosubst_at rightc "deliv" "outR".
    remove_at rightc "deliv".
    autosubst_at leftc "inCPA" "ct".
    remove_at leftc "inCPA".
    r_move_at leftc "ct" 0.
    r_move_at leftc "leak" 1.
    trans_at leftc "ct" "leak" "inS" tyMsg.
    trans_at leftc "ct" "leak" "keygen" tyKey.
    arg_move_at leftc "leak" "ct" 0.
    arg_move_at leftc "leak" "inS" 1.
    fold_at leftc.
    r_ext_at leftc "leak" (fun (_ : msg) x0 => enc mzero x0).
     intros; rewrite bind_ret //=.
   align.
   reflexivity.
  Qed.

  Theorem noCorr : CPA true ~~> CPA false -> exists sim, r_compat _ _ sim idealNoCorr /\ realNoCorr ~~> (sim ||| idealNoCorr).
    intros; exists rps_nocorr_sim; split.
    done.
    etransitivity.
    apply noCorr_1.
    done.
    etransitivity.
    apply: rewr_congr.
    done.
    instantiate (1 := CPA false).
    done.
    apply noCorr_2.
  Qed.


  (* TODO corruption case *)
       
       