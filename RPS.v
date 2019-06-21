
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
From mathcomp Require Import fingroup finset. 
From mathcomp Require Import cyclic zmodp.

Require Import Posrat Premeas Meas Aux Logic finfun_fixed String SSRString SeqOps RLems Tacs.


Section RPS.
  Inductive play := rock | paper | scissors.
  Definition play_enc : play -> option bool :=
    fun p =>
      match p with
        | rock => None
        | paper => Some false
        | scissors => Some true end.
  Definition play_dec : option bool -> play :=
    fun p =>
      match p with
        | None => rock
        | Some false => paper
        | Some true => scissors end.
  Lemma play_cancel : cancel play_enc play_dec.
  by elim.
  Qed.
  Canonical play_eq := EqType play (CanEqMixin play_cancel).
  Canonical play_ch := ChoiceType play (CanChoiceMixin play_cancel).
  Canonical play_co := CountType play (CanCountMixin play_cancel).
  Canonical play_fin := FinType play (CanFinMixin play_cancel).

  
  Inductive ty :=
    | tyPlay
    | tyAns
    | tyUnit
    | tyPair : ty -> ty -> ty.

  Fixpoint ty_enc (t : ty) : GenTree.tree (option bool) :=
    match t with
      | tyPlay => GenTree.Leaf (Some false)
      | tyAns => GenTree.Leaf (Some true)
      | tyUnit => GenTree.Leaf None
      | tyPair t1 t2 => GenTree.Node 0 [:: ty_enc t1; ty_enc t2]
                                     end.
  Fixpoint ty_dec (t : GenTree.tree (option bool)) : ty :=
    match t with
      | GenTree.Leaf (Some false) => tyPlay
      | GenTree.Leaf (Some true) => tyAns
      | GenTree.Leaf None => tyUnit
      | GenTree.Node _ (x :: y :: _) => tyPair (ty_dec x) (ty_dec y)
      | _ => tyPlay
               end.

  Lemma ty_can : cancel ty_enc ty_dec.
    move => x.
    induction x; rewrite //=.
    rewrite IHx1 IHx2 //=.
  Qed.

  Canonical ty_eq := EqType ty (CanEqMixin ty_can).
  Canonical ty_ch := ChoiceType ty (CanChoiceMixin ty_can).

  Fixpoint denomTy (t : ty) : finType :=
    match t with
      | tyPlay => [finType of play]
      | tyAns => [finType of option bool]
      | tyUnit => [finType of unit]
      | tyPair t1 t2 => [finType of (denomTy t1) * (denomTy t2)]
                          end.

  Local Instance ty_type : type [eqType of ty].
   econstructor.
   instantiate (1 := denomTy).
   instantiate (1 := tyPair).
   done.
 Defined.

  Definition rps_comp (p q : play) : option bool :=
    match p with
    | rock =>
      match q with
        | rock => None
        | scissors => Some false
        | paper => Some true end
    | paper => 
      match q with
        | rock => Some false
        | scissors => Some true
        | paper => None end
    | scissors =>
      match q with
        | rock => Some true
        | scissors => None
        | paper => Some false
      end
        end.

  Definition rl := rlist [choiceType of string] [choiceType of ty].

  Open Scope string_scope.

  Definition ans_flip (o : option bool) :=
    match o with
    | None => None
    | Some b => Some (~~ b)
                     end.

  Definition rpsIdeal : rl :=
    [:: inr ("inA", tyPlay);
      inr ("inB", tyPlay);
      [:: ("inA", tyPlay); ("inB", tyPlay)] ~> ("comp", tyAns) dhid rps_comp;
      [:: ("comp", tyAns)] ~> ("outA", tyAns) dvis id;
      [:: ("comp", tyAns)] ~> ("outB", tyAns) dvis id
    ].

  Definition rpsRealP (p : bool) :rl :=
    let me := if p then "A" else "B" in
    let them := if p then "B" else "A" in
    [:: inr ("in" ++ me, tyPlay);
       inr ("committed" ++ them, tyUnit);
       inr ("val" ++ them, tyPlay);
       [:: ("in" ++ me, tyPlay)] ~> ("com" ++ me, tyPlay) dvis id;
       [:: ("com" ++ me, tyPlay); ("committed" ++ them, tyUnit)] ~> ("open" ++ me, tyUnit) dvis (fun _ _ => tt);
       [:: ("in"++me, tyPlay); ("val"++them, tyPlay)] ~> ("out"++me, tyAns) dvis (if p then rps_comp else (fun y x => rps_comp x y))
    ].


  Definition rps_simp : rl :=
    [::
      [:: ("inA", tyPlay); ("inB", tyPlay)] ~> ("outB", tyAns) vis (fun y x  => ret rps_comp y x);
      [:: ("inB", tyPlay); ("inA", tyPlay)] ~> ("outA", tyAns)
      vis (fun y x  => ret rps_comp x y); inr ("inB", tyPlay); inr ("inA", tyPlay)].

  Definition rpsRealF (p : bool) : rl :=
    let me := if p then "A" else "B" in
    [:: inr ("com"++me, tyPlay);
        [:: ("com"++me, tyPlay)] ~> ("committed"++me, tyUnit) dvis (fun _ => tt);
        inr ("open"++me, tyUnit);
        [:: ("com"++me, tyPlay); ("open"++me, tyUnit)] ~> ("val"++me, tyPlay) dvis (fun x _ => x)
                                                       ].


  Definition rpsReal := (rpsRealF true ||| rpsRealF false ||| rpsRealP true ||| rpsRealP false).

  Close Scope posrat_scope.
  Open Scope nat_scope.

  Lemma eqVneq_xx {A : eqType} (x : A) : eqVneq x x = left erefl.
    destruct (eqVneq x x).
    have -> //=: e = erefl by apply eq_irrelevance.
    exfalso.
    rewrite eq_refl in i; done.
  Qed.

  (******* NOBODY CORRUPTED ********)
    
  Lemma ideal_rewr : r_rewr rps_simp rpsIdeal.
    rewrite /rpsIdeal /rps_simp.
    simpl.
    trans_at rightc "comp" "outA" "inA" tyPlay.
    trans_at rightc "comp" "outA" "inB" tyPlay.
    arg_move_at rightc "outA" "comp" 0.
    arg_move_at rightc "outA" "inA" 1.
    subst_at rightc "comp" "outA".
    hid_str_at rightc "comp" "outA".

    trans_at rightc "comp" "outB" "inA" tyPlay.
    trans_at rightc "comp" "outB" "inB" tyPlay.
    arg_move_at rightc "outB" "comp" 0.
    arg_move_at rightc "outB" "inA" 1.
    subst_at rightc "comp" "outB".
    hid_str_at rightc "comp" "outB".

    remove_at rightc "comp".
    r_move_at rightc "outB" 0.
    r_move_at rightc "outA" 1.
    arg_move_at leftc "outA" "inA" 0.
    r_move_at leftc "inB" "inA".
    reflexivity.
 Qed.

  Lemma real_rewr : r_rewr rpsReal rps_simp.
    rewrite /rpsReal /rpsRealF /rpsRealP.
    simpl.
    rewrite /rlist_comp_hide.
    vm_compute RChans; rewrite //=.

    simpl.
    trans_at leftc "committedA" "openB" "comA" tyPlay.
    arg_move_at leftc "openB" "committedA" 0.
    subst_at leftc "committedA" "openB".
    hid_str_at leftc "committedA" "openB".

    trans_at leftc "committedB" "openA" "comB" tyPlay.
    arg_move_at leftc "openA" "committedB" 0.
    subst_at leftc "committedB" "openA".
    hid_str_at leftc "committedB" "openA".

    remove_at leftc "committedA".
    remove_at leftc "committedB".

    trans_at leftc "openA" "valA" "comB" tyPlay.
    arg_move_at leftc "valA" "openA" 0.
    subst_at leftc "openA" "valA".
    hid_str_at leftc "openA" "valA".
    remove_at leftc "openA".

    trans_at leftc "openB" "valB" "comA" tyPlay.
    arg_move_at leftc "valB" "openB" 0.
    subst_at leftc "openB" "valB".
    hid_str_at leftc "openB" "valB".
    remove_at leftc "openB".

    trans_at leftc "valA" "outB" "comA" tyPlay.
    trans_at leftc "valA" "outB" "comB" tyPlay.
    arg_move_at leftc "outB" "valA" 0.
    subst_at leftc "valA" "outB".
    hid_str_at leftc "valA" "outB".
    remove_at leftc "valA".

    trans_at leftc "valB" "outA" "comB" tyPlay.
    trans_at leftc "valB" "outA" "comA" tyPlay.
    arg_move_at leftc "outA" "valB" 0.
    subst_at leftc "valB" "outA".
    hid_str_at leftc "valB" "outA".
    remove_at leftc "valB".

    hid_str_at leftc "comA" "outA".
    hid_str_at leftc "comB" "outB".

    trans_at leftc "comA" "outB" "inA" tyPlay.
    arg_move_at leftc "outB" "comA" 0.
    arg_move_at leftc "outB" "inA" 1.
    subst_at leftc "comA" "outB".
    hid_str_at leftc "comA" "outB".
    remove_at leftc "comA".

    trans_at leftc "comB" "outA" "inB" tyPlay.
    arg_move_at leftc "outA" "comB" 0.
    arg_move_at leftc "outA" "inB" 1.
    subst_at leftc "comB" "outA".
    hid_str_at leftc "comB" "outA".
    remove_at leftc "comB".

    rewrite /rps_simp.
    r_move_at leftc "outB" 0.
    r_move_at leftc "outA" 1.
    r_move_at leftc "inB" 2.
    reflexivity.
Qed.

Lemma rps_no_corr : rpsReal ~~> rpsIdeal.
  rewrite real_rewr.
  apply ideal_rewr.
Qed.
