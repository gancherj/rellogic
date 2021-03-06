
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
From mathcomp Require Import fingroup finset. 
From mathcomp Require Import cyclic zmodp.

Require Import Posrat Premeas Meas Aux Reaction finfun_fixed String SSRString SeqOps RLems.


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
    [:: inr "inA";
      inr "inB";
      [:: ("inA", tyPlay); ("inB", tyPlay)] ~> ("comp", tyAns) dhid rps_comp;
      [:: ("comp", tyAns)] ~> ("outA", tyAns) dvis id;
      [:: ("comp", tyAns)] ~> ("outB", tyAns) dvis id
    ].

  Definition rpsRealP (p : bool) :rl :=
    let me := if p then "A" else "B" in
    let them := if p then "B" else "A" in
    [:: inr ("in" ++ me);
       inr ("committed" ++ them);
       inr ("val" ++ them);
       [:: ("in" ++ me, tyPlay)] ~> ("com" ++ me, tyPlay) dvis id;
       [:: ("com" ++ me, tyPlay); ("committed" ++ them, tyUnit)] ~> ("open" ++ me, tyUnit) dvis (fun _ _ => tt);
       [:: ("in"++me, tyPlay); ("val"++them, tyPlay)] ~> ("out"++me, tyAns) dvis (if p then rps_comp else (fun y x => rps_comp x y))
    ].

  Lemma wf_realP b : r_wf (rpsRealP b).
  rewrite /rpsRealP /r_wf; destruct b; done.
  Qed.

  Definition rps_simp : rl :=
    [::
      [:: ("inA", tyPlay); ("inB", tyPlay)] ~> ("outB", tyAns) vis (fun y x  => ret rps_comp y x);
      [:: ("inB", tyPlay); ("inA", tyPlay)] ~> ("outA", tyAns)
      vis (fun y x  => ret rps_comp x y); inr "inB"; inr "inA"].

  Definition rpsRealF (p : bool) : rl :=
    let me := if p then "A" else "B" in
    [:: inr ("com"++me);
        [:: ("com"++me, tyPlay)] ~> ("committed"++me, tyUnit) dvis (fun _ => tt);
        inr ("open"++me);
        [:: ("com"++me, tyPlay); ("open"++me, tyUnit)] ~> ("val"++me, tyPlay) dvis (fun x _ => x)
                                                       ].

  Lemma wf_realF b : r_wf (rpsRealF b).
  rewrite /rpsRealF /r_wf; destruct b; done.
  Qed.

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
    r_move "outA" 0.
    arg_focus "inA".
    r_prod "outA" "outB" "tmp".
    rewrite /eq_rect_r /=.
    r_ext "tmp" (fun x y => a <- ret (rps_comp x y); ret (a, a)).
    intros; destruct x; destruct x0; simpl; msimp; done.
    unfold_bind2 "tmp" "comp" tyAns.
    r_subst "tmp" "outB".
    r_str "outB" "tmp".
    r_subst "tmp" "outA".
    r_str "outA" "tmp".
    r_str_inp "outA" "inA".
    r_str_inp "outA" "inB".
    r_str_inp "outB" "inA".
    r_str_inp "outB" "inB".
    r_clean.
    r_align.
    reflexivity.
  Qed.

  Lemma real_rewr : r_rewr rpsReal rps_simp.
    rewrite /rpsReal /rpsRealF /rpsRealP.
    simpl.
    rewrite /rlist_comp_hide.
    vm_compute RChans; rewrite //=.

    simpl.
    r_weakstr "committedA" "comA".
    r_weakstr "committedB" "comB".
    r_str_inp "committedA" "inA".
    r_str_inp "committedB" "inB".
    r_move "openA" 0; arg_focus "committedB".
    r_str "openA" "committedB".
    r_move "openB" 0; arg_focus "committedA".
    r_str "openB" "committedA".
    repeat r_clean.
    r_subst "comA" "openA".
    r_str "openA" "comA".
    r_str_inp "openA" "inA".
    r_str "valA" "openA".

    r_subst "comB" "openB".
    r_str "openB" "comB".
    r_str_inp "openB" "inB".
    r_str "valB" "openB".
    repeat r_clean.

    r_subst "valB" "outA".
    r_str "outA" "valB".
    r_subst "valA" "outB".
    r_str "outB" "valA".
    repeat r_clean.

    r_subst "comA" "outB".
    r_str "outB" "comA".

    r_subst "comB" "outA".
    r_str "outA" "comB".
    repeat r_clean.
    rewrite /rps_simp.
    simpl.
    r_align.
    reflexivity.
  Qed.

      