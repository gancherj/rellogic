
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
From mathcomp Require Import fingroup finset. 
From mathcomp Require Import cyclic zmodp.

Require Import Posrat Premeas Meas Aux finfun_fixed String SSRString SeqOps RLems.
Require Import Logic Tacs.

Require Import FCG.

Section DDH.
  Context (G : finType) `{FinCyclicGroup G}.

  Inductive ty :=
  | tyUnit
  | tyZq
  | tyG
  | tyPair : ty -> ty -> ty.

  Fixpoint ty_enc (t : ty) : GenTree.tree (option bool) :=
    match t with
    | tyUnit => GenTree.Leaf None 
    | tyZq => GenTree.Leaf (Some false)
    | tyG => GenTree.Leaf (Some true)
    | tyPair t1 t2 => GenTree.Node 0 [:: ty_enc t1; ty_enc t2]
    end.

  Fixpoint ty_dec (t : GenTree.tree (option bool)) : ty :=
    match t with
      | GenTree.Leaf (Some false) => tyZq
      | GenTree.Leaf (Some true) => tyG
      | GenTree.Leaf None => tyUnit                                    
      | GenTree.Node _ (x :: y :: _) => tyPair (ty_dec x) (ty_dec y)
      | _ => tyZq
               end.
  Lemma ty_can : cancel ty_enc ty_dec.
    move => x.
    induction x; rewrite //=.
    rewrite IHx1 IHx2 //=.
  Qed.
  Canonical ty_eq := EqType ty (CanEqMixin ty_can).
  Canonical ty_ch := ChoiceType ty (CanChoiceMixin ty_can).

Definition q := order.

  Fixpoint denomTy (t : ty) : finType :=
    match t with
      | tyUnit => [finType of unit]
      | tyZq => [finType of 'Z_q]
      | tyG => G
      | tyPair t1 t2 => [finType of (denomTy t1) * (denomTy t2)]
                          end.

  Local Instance ty_type : type [eqType of ty].
   econstructor.
   instantiate (1 := denomTy).
   instantiate (1 := tyPair).
   done.
 Defined.


  Definition rl := rlist [choiceType of string] [choiceType of ty].


  Open Scope string_scope.


Definition ddh0 : rl :=
[:: [::] ~> ("samp", tyPair (tyPair tyG tyG) tyG)
    vis (x <- munif [finType of 'Z_q];
         y <- munif [finType of 'Z_q]; ret (exp x, exp y, exp (Zp_mul x y)))].

Definition ddh1 : rl :=
[:: [::] ~> ("samp",
 tyPair (tyPair tyG tyG) tyG)
    vis (x <- munif [finType of 'Z_q];
         y <- munif [finType of 'Z_q];
         z <- munif [finType of 'Z_q];
         ret (exp x, exp y, exp z))].

Definition ElGamal_real : rl :=
    [:: [::] ~> ("x", tyZq) hid (x <- munif [finType of 'Z_q]; ret x);
       [:: ("x", tyZq)] ~> ("pk", tyG) dvis ((fun x  => (exp x)%g));
       inr ("m", tyG);
       [::] ~> ("y", tyZq) hid (munif [finType of 'Z_q]);
       [:: ("x", tyZq); ("y", tyZq); ("pk", tyG); ("m", tyG)] ~> ("c", tyPair tyG tyG) dvis
                                                               (fun x y pk m => (exp y, (exp (Zp_mul x y)) * m))%fcg
                                                               ].

Definition ElGamal_ideal : rl :=
  [:: [::] ~> ("x", tyZq) hid (munif [finType of 'Z_q]);
     [:: ("x", tyZq)] ~> ("pk", tyG) dvis (fun x => exp x)%g;
    [::] ~> ("y", tyZq) hid (munif [finType of 'Z_q]);
    [::] ~> ("z", tyZq) hid (munif [finType of 'Z_q]);
    inr ("m", tyG);
    [:: ("y", tyZq); ("z", tyZq); ("pk", tyG); ("m", tyG)] ~> ("c", tyPair tyG tyG) dvis (fun y z _ m =>
                                                                               (exp y, (exp z))%g)].

Definition eg1 : rl :=
  [:: [::] ~> ("samp", tyPair (tyPair tyG tyG) tyG) hid (x <- munif [finType of 'Z_q]; y <- munif [finType of 'Z_q]; ret (exp x, exp y, exp (Zp_mul x y))%fcg);
     [:: ("samp", tyPair (tyPair tyG tyG) tyG)] ~> ("X", tyG) dhid (fun x => x.1.1);
     [:: ("samp", tyPair (tyPair tyG tyG) tyG)] ~> ("Y", tyG) dhid (fun x => x.1.2);
     [:: ("samp", tyPair (tyPair tyG tyG) tyG)] ~> ("Z", tyG) dhid (fun x => x.2);
     inr ("m", tyG);
     [:: ("X", tyG)] ~> ("pk", tyG) dvis id;
     [:: ("Y", tyG); ("Z", tyG); ("pk", tyG); ("m", tyG)] ~> ("c", tyPair tyG tyG) dvis (fun y z pk m => (y, z * m)%fcg)]. 

Definition eg1_factor : rl :=
  [:: inr ("samp", tyPair (tyPair tyG tyG) tyG); 
     [:: ("samp", tyPair (tyPair tyG tyG) tyG)] ~> ("X", tyG) dhid (fun x => x.1.1);
     [:: ("samp", tyPair (tyPair tyG tyG) tyG)] ~> ("Y", tyG) dhid (fun x => x.1.2);
     [:: ("samp", tyPair (tyPair tyG tyG) tyG)] ~> ("Z", tyG) dhid (fun x => x.2);
     inr ("m", tyG);
     [:: ("X", tyG)] ~> ("pk", tyG) dvis id;
     [:: ("Y", tyG); ("Z", tyG); ("pk", tyG); ("m", tyG)] ~> ("c", tyPair tyG tyG) dvis (fun y z pk m => (y, z * m)%fcg)]. 

Definition eg2 : rl :=
  [:: [::] ~> ("x", tyZq) hid (munif [finType of 'Z_q]);
     [:: ("x", tyZq)] ~> ("pk", tyG) dvis (fun x => exp x)%g;
    [::] ~> ("y", tyZq) hid (munif [finType of 'Z_q]);
    [::] ~> ("z", tyZq) hid (munif [finType of 'Z_q]);
    inr ("m", tyG);
    [:: ("y", tyZq); ("z", tyZq); ("pk", tyG); ("m", tyG)] ~> ("c", tyPair tyG tyG) dvis (fun y z _ m =>
                                                                               (exp y, (exp z) * m)%fcg)].


    Close Scope posrat_scope.
    Open Scope nat_scope.

  Arguments rbind [N T H ].
  
Lemma eg_step1 : ElGamal_real ~~> eg1.
  rewrite /ElGamal_real /eg1.
  simpl.
  unfold_bind0_at rightc "samp" "samp1" tyZq.
  unfold_at_with rightc "samp" (nil : seq (string * ty)).
  unfold_bind1_at rightc "samp" "samp2" tyZq.
  unfold_at rightc "samp".
  rewrite lift_det2.
  hid_weak_at rightc "samp1" "X".
  hid_weak_at rightc "samp2" "X".
  arg_move_at rightc "X" 2 0.
  subst_at rightc "samp" "X".
  hid_str_at rightc "samp" "X".
  hid_str_at rightc "samp2" "X".
  hid_weak_at rightc "samp1" "pk".
  arg_move_at rightc "pk" "X" 0.
  subst_at rightc "X" "pk".
  hid_str_at rightc "X" "pk".
  remove_at rightc "X".
  rename_at rightc "samp1" "x".
  hid_str_at rightc "x" "samp2".
  hid_weak_at rightc "samp2" "Y".
  hid_weak_at rightc "x" "Y".
  arg_move_at rightc "Y" "samp" 0.
  arg_move_at rightc "Y" "samp2" 1.
  subst_at rightc "samp" "Y".
  hid_str_at rightc "samp" "Y".
  hid_str_at rightc "x" "Y".
  hid_weak_at rightc "samp2" "c".
  arg_move_at rightc "c" "Y" 0.
  subst_at rightc "Y" "c".
  hid_str_at rightc "Y" "c".
  remove_at rightc "Y".
  rename_at rightc "samp2" "y".
  arg_move_at rightc "c" "Z" 0.
  hid_weak_at rightc "x" "c".
  hid_weak_at rightc "samp" "c".
  arg_move_at rightc "c" "Z" 0.
  subst_at rightc "Z" "c".
  hid_str_at rightc "Z" "c".
  remove_at rightc "Z".
  arg_move_at rightc "c" "y" 1.
  arg_move_at rightc "c" "x" 2.
  subst_at rightc "samp" "c".
  hid_str_at rightc "samp" "c".
  remove_at rightc "samp".
  r_move_at rightc "x" 0.
  r_move_at rightc "pk" 1.
  r_move_at rightc "m" 2.
  r_move_at rightc "y" 3.
  r_move_at rightc "c" 4.
  arg_move_at rightc "c" "x" 0.
  rewrite bind_ret.
  reflexivity.
Qed.


Lemma eg_factor_eq : r_rewr eg1 (eg1_factor ||| ddh0).
  r_move_at leftc 0 6.
  reflexivity.
Qed.

(* TODO here *)

Lemma eg_step2 : r_rewr (eg1_factor ||| ddh1) eg2.
  r_move_at leftc 6 0.
  unfold_bind0_at leftc "samp" "x" tyZq.
  unfold_at leftc "samp".
  unfold_bind1_at leftc "samp" "y" tyZq.
  unfold_at leftc "samp".
  unfold_bind2_at leftc "samp" "z" tyZq.
  r_weak "X" "samp".
  r_subst "samp" "X".
  r_str "X" "samp".
  r_str "X" "z".
  r_str "X" "y".
  r_subst "X" "pk".
  r_str "pk" "X".
  r_clean.
  r_str "y" "x".
  r_str "z" "x".
  r_str "z" "y".
  r_subst "Y" "c".
  r_subst "Z" "c".
  r_str "c" "Z".
  r_str "c" "Y".
  r_subst "samp" "c".
  r_str "c" "samp".
  r_clean.
  r_clean.
  r_clean.
  rewrite /eg2.
  r_str "c" "x".
  arg_focus "y".
  r_align.
  reflexivity.
Time Qed.

Lemma eg_step3 : r_rewr eg2 ElGamal_ideal.
  rewrite /eg2.
  simpl.
  r_move "z" 0.
  r_move "m" 1.
  r_move "c" 0.
  arg_focus "z".
  r_move "c" 1.

  have: ([:: ("z", tyZq); ("y", tyZq); ("pk", tyG); ("m", tyG)], true, ("c", tyPair tyG tyG)) =
        (("z", tyZq) :: ([::] ++ [:: ("y", tyZq); ("pk", tyG); ("m", tyG)]), true, ("c", tyPair tyG tyG)). 
   by done.
   move => h.
 rewrite (cast_existT h).

 have -> : h = erefl by apply eq_irrelevance.
 clear h.
 etransitivity.
 eapply rewr_bi_r.
 rewrite /dep_cast /eq_rect.
 apply: rewr_add_ch_fold.
 done.
 done.
 instantiate (1 := ("m", tyG)).
 done.
    
  r_ext "z" (fun m => (x <- munif [finType of 'Z_q]; ret (Zp_add x (Zp_opp (log m))))).
    intro m.
    rewrite -munif_bij.
    done.
    generalize (log m) => y.
    exists (fun x => Zp_add x y).
    move => x.
    rewrite -Zp_addA.
    rewrite Zp_addNz Zp_addC Zp_add0z //=.
    move => x.
    rewrite -Zp_addA.
    rewrite (Zp_addC y) Zp_addNz Zp_addC Zp_add0z //=.
  unfold_bind1 "z" "t" tyZq.
  r_subst "z" "c".
  r_str "c" "z".
  r_ext "c" (fun (x : 'Z_q) (x0 : G) (x1 : 'Z_q) (g : G) =>
           ret (exp x1, exp x)).
  intros.
  rewrite -{2}(log_exp x0).
  rewrite -Hop.
  rewrite -Zp_addA.
  rewrite Zp_addNz Zp_addC Zp_add0z //=.
 r_clean.
 r_rename "t" "z".
 arg_focus "y".
 arg_move "pk" "m".
 r_move "z" 0.
 r_move "m" 1.
 rewrite rewr_str_inp.
 rewrite /ElGamal_ideal.
 simpl.
 r_align.
 reflexivity.
Qed.

Lemma ElGamal_secure: r_rewr ddh0 ddh1 -> r_rewr ElGamal_real ElGamal_ideal.
  intro.
  etransitivity.
  apply eg_step1.
  etransitivity.
  apply eg_factor_eq.
  etransitivity.
  instantiate (1 := eg1_factor ||| ddh1).
  apply rewr_congr.
  rewrite /eg1_factor /ddh0.
  rewrite /Reaction.r_compat.
  simpl.
  intro.
  move/andP; elim.
  intro.
  rewrite mem_seq1; move/eqP => ->.
  done.
  rewrite /Reaction.r_compat /eg1_factor /ddh1.
  simpl.
  intro; move/andP; elim; intro; rewrite mem_seq1; move/eqP => ->; done.
  (* TODO: congr rule *)
  etransitivity.
  apply eg_step2.
  apply eg_step3.
Qed.
  

  