From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
From mathcomp Require Import fingroup finset. 
From mathcomp Require Import cyclic zmodp.

Require Import Posrat Premeas Meas Aux Logic finfun_fixed String SSRString SeqOps RLems Tacs DerivedTacs.

Section SecChan.
  Context (msg : finType) (ctxt : finType) (key : finType).
  Context (keyGen : meas key).
  Context (enc : msg -> key -> meas ctxt).
  Context (dec : ctxt -> key -> msg).
  Context (leak : ctxt -> nat).
  Context (dec_correct : forall m k c, c \in support (enc m k) -> dec c k = m).

  Inductive ty :=
  | tyMsg
  | tyKey
  | tyCtx
  | tyNat
  | tyUnit
  | tyPair : ty -> ty -> ty.

  Definition seq5 := [:: 0; 1; 2; 3; 4].
  Notation InSeqSub s x := (@SeqSub _ s x is_true_true).

  Fixpoint ty_enc (t : ty) : GenTree.tree (seq_sub seq5) :=
    match t with
    | tyMsg => GenTree.Leaf (InSeqSub seq5 0)
    | tyKey => GenTree.Leaf (InSeqSub seq5 1)
    | tyCtx => GenTree.Leaf (InSeqSub seq5 2)
    | tyNat => GenTree.Leaf  (InSeqSub seq5 3)
    | tyUnit => GenTree.Leaf  (InSeqSub seq5 4)
    | tyPair t1 t2 => GenTree.Node 0 [:: ty_enc t1; ty_enc t2]
    end.

  Print seq_sub.

  Fixpoint ty_dec (t : GenTree.tree (seq_sub seq5)) : ty :=
    match t with
    | GenTree.Leaf n => match (ssval n) with
                          | 0 => tyMsg
                          | 1 => tyKey
                          | 2 => tyCtx
                          | 3 => tyNat
                          | 4 => tyUnit
                          | _ => tyNat
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
      | tyNat => [choiceType of nat]
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
       [:: ("sendS", tyCtx)] ~> ("leak", tyNat) dvis leak;
       inr ("ans", tyUnit);
       [:: ("sendS", tyCtx); ("ans", tyUnit)] ~> ("deliv", tyCtx) dvis (fun x _ => x)].

  Definition FKey : rl :=
    [:: [::] ~> ("samp", tyKey) hid keyGen;
        [:: ("samp", tyKey)] ~> ("keyS", tyKey) dvis id;
        [:: ("samp", tyKey)] ~> ("keyR", tyKey) dvis id].

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
       inr ("in", tyMsg);
       [::] ~> ("keygen", tyKey) hid keyGen;
       [:: ("in", tyMsg); ("keyGen", tyKey)] ~> ("ct", tyCtx) vis (fun m k => if b then (enc m k) else (munif ctxt))].

  Theorem noCorr : CPA true ~~> CPA false -> realNoCorr ~~> idealNoCorr.
    intro.
    rewrite /realNoCorr /rlist_comp_hide; vm_compute RChans; simpl.
    autosubst_at leftc "deliv" "outR".
    remove_at leftc "deliv".
    autosubst_at leftc "keyS" "sendS".
    remove_at leftc "keyS".
    autosubst_at leftc "keyR" "outR".
    remove_at leftc "keyR".


    trans_at leftc "sendS" "leak" "samp" tyKey.
    r_ext_at leftc "outR" (rbind [:: ("samp", tyKey); ("sendS", tyCtx)] [:: ("ans", tyUnit)] ("tmp", tyMsg) ("outR", tyMsg) (fun x y => ret (dec y x)) (fun (x : msg) _ _ _ => ret x)).
    intros; unlock rbind; rewrite //=.
    msimp; done.
    unfold_at leftc "outR".
    trans_rev_at leftc "tmp" "outR" "samp".
    trans_rev_at leftc "tmp" "outR" "sendS".
    pair_at leftc "leak" "tmp" "X".
    rewrite /remove2 //=.
    (* X tmp leak outR inS sendS ans samp *)
    trans_rev_at leftc "X" "leak" "sendS".

    Print r_prod.

    
    
    
    hid_str_at leftc "sendS" "outR".

       

       