
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
From mathcomp Require Import fingroup finset. 
From mathcomp Require Import cyclic zmodp.

Require Import Posrat Premeas Meas Aux Logic finfun_fixed String SSRString SeqOps RLems Tacs DerivedTacs.


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
    [:: inp ("inA", tyPlay);
      inp ("inB", tyPlay);
      [:: ("inA", tyPlay)] ~> ("sendA", tyPlay) hid mret;
      [:: ("inB", tyPlay)] ~> ("sendB", tyPlay) hid mret;
      [:: ("sendA", tyPlay); ("sendB", tyPlay)] ~> ("recvA", tyAns) dhid rps_comp;
      [:: ("sendA", tyPlay); ("sendB", tyPlay)] ~> ("recvB", tyAns) dhid rps_comp;
      [:: ("recvA", tyAns)] ~> ("outA", tyAns) dvis id;
      [:: ("recvB", tyAns)] ~> ("outB", tyAns) dvis id
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

    autosubst_at rightc "sendA" "recvA".
    autosubst_at rightc "sendB" "recvB".
    autosubst_at rightc "recvA" "outA".
    autosubst_at rightc "recvB" "outB".
    autosubst_at rightc "sendA" "outB".
    autosubst_at rightc "sendB" "outA".
    remove_at rightc "recvA".
    remove_at rightc "recvB".
    remove_at rightc "sendA".
    remove_at rightc "sendB".
    align.
    reflexivity.
 Qed.

  Lemma real_rewr : r_rewr rpsReal rps_simp.
    rewrite /rpsReal /rpsRealF /rpsRealP.
    simpl.
    rewrite /rlist_comp_hide.
    vm_compute RChans; rewrite //=.

    simpl.
    autosubst_at leftc "committedA" "openB".
    autosubst_at leftc "committedB" "openA".
    remove_at leftc "committedA".
    remove_at leftc "committedB".
    autosubst_at leftc "comA" "valA".
    autosubst_at leftc "comA" "openB".
    autosubst_at leftc "comA" "openA".
    remove_at leftc "comA".
    autosubst_at leftc "comB" "valB".
    autosubst_at leftc "comB" "openA".
    autosubst_at leftc "comB" "openB".
    remove_at leftc "comB".
    autosubst_at leftc "openA" "valA".
    remove_at leftc "openA".
    autosubst_at leftc "openB" "valB".
    remove_at leftc "openB".
    autosubst_at leftc "valB" "outA".
    remove_at leftc "valB".
    autosubst_at leftc "valA" "outB".
    remove_at leftc "valA".
    rewrite /rps_simp //=.
    align.
    arg_move_at leftc "outB" "inB" 1.
    reflexivity.
Qed.

Lemma rps_no_corr : rpsReal ~~> rpsIdeal.
  rewrite real_rewr.
  apply ideal_rewr.
Qed.

Print rps_comp.

Definition rps_comp_inv_b x y :=
  match y with
  | None =>
    match x with
    | rock => rock
    | paper => paper
    | scissors => scissors
    end
  | Some false =>
    match x with
      | rock => paper
      | paper => scissors
      | scissors => rock
    end
  | Some true =>
    match x with
    | rock => scissors
    | scissors => paper
    | paper => rock
    end
      end.
      


Lemma rps_comp_inv_bE x y : rps_comp_inv_b x (rps_comp y x) = y. 
induction x; induction y; done.
Qed.

Definition rpsIdeal_corr : rl :=
[:: inr ("inA", tyPlay);
    inr ("comB", tyPlay);
    [:: ("inA", tyPlay)] ~> ("sendA", tyPlay) hid mret;
    [:: ("comB", tyPlay)] ~> ("sendB", tyPlay) hid mret;
    [::] ~> ("committedA", tyUnit) dvis tt;
    inr ("openB", tyUnit);
    
    [:: ("sendA", tyPlay); ("sendB", tyPlay)] ~> ("recvA", tyAns) dhid rps_comp;
    [:: ("sendA", tyPlay); ("sendB", tyPlay)] ~> ("recvB", tyAns) dhid rps_comp;
    [:: ("sendB", tyPlay); ("recvB", tyAns)] ~> ("valA", tyPlay) dvis rps_comp_inv_b;
    [:: ("recvA", tyAns)] ~> ("outA", tyAns) dvis id
].

Definition rpsReal_corr : rl :=
  [::
     inr ("inA", tyPlay);
     inr ("comB", tyPlay);
     [:: ("inA", tyPlay)] ~> ("comA", tyPlay) dhid id;
     [:: ("comA", tyPlay)] ~> ("committedA", tyUnit) dvis (fun _ => tt);
     [:: ("comB", tyPlay)] ~> ("committedB", tyUnit) dhid (fun _ => tt);
     [:: ("comA", tyPlay); ("committedB", tyUnit)] ~> ("openA", tyUnit) dhid (fun _ _ => tt);
     inr ("openB", tyUnit);
     [:: ("comA", tyPlay); ("openA", tyUnit)] ~> ("valA", tyPlay) dvis (fun x _ => x);
     [:: ("comB", tyPlay); ("openB", tyUnit)] ~> ("valB", tyPlay) dhid (fun x _ => x);
     [:: ("inA", tyPlay); ("valB", tyPlay)] ~> ("outA", tyAns) dvis rps_comp
                                            ].

Lemma rps_corr : rpsReal_corr ~~> rpsIdeal_corr.
  rewrite /rpsReal_corr /rpsIdeal_corr.
  simpl.
  autosubst_at leftc "comA" "committedA".
  autosubst_at leftc "comA" "openA".
  autosubst_at leftc "comA" "valA".
  remove_at leftc "comA".
  autosubst_at leftc "committedB" "openA".
  remove_at leftc "committedB".
  autosubst_at leftc "openA" "valA".
  remove_at leftc "openA".
  autosubst_at leftc "valB" "outA".
  remove_at leftc "valB".

  autosubst_at rightc "sendB" "recvA".
  autosubst_at rightc "sendB" "recvB".
  autosubst_at rightc "sendB" "valA".
  remove_at rightc "sendB".
  autosubst_at rightc "recvA" "outA".
  remove_at rightc "recvA".
  autosubst_at rightc "recvB" "valA".
  remove_at rightc "recvB".
  autosubst_at rightc "sendA" "valA".
  autosubst_at rightc "sendA" "outA".
  remove_at rightc "sendA".
  align.
  r_ext_at rightc "valA" (fun (x x0 : play) => ret x).
    intros; rewrite rps_comp_inv_bE //=.
    rewrite /lset //=.
  inp_str_at leftc "committedA" "inA" tyPlay.
  rewrite /lset //=.
  arg_move_at leftc "valA" "inA" 0.
  arg_move_at leftc "outA" "openB" 0.
  inp_str_at leftc "outA" "openB" tyUnit.
  rewrite /lset /=.
  arg_move_at leftc "outA" "inA" 0.
  reflexivity.
Qed.
  
  

     