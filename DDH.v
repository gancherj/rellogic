
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
From mathcomp Require Import fingroup finset. 
From mathcomp Require Import cyclic zmodp.

Require Import Posrat Premeas Meas Aux finfun_fixed String SSRString SeqOps RLems.
Require Import Logic Tacs DerivedTacs.

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
  
Lemma eg_step1 : ElGamal_real <~~> eg1.
  rewrite /ElGamal_real /eg1.
  simpl.
  unfold_bind0_at rightc "samp" "samp1" tyZq.
  unfold_at rightc "samp".
  unfold_bind1_at rightc "samp" "samp2" tyZq.
  unfold_at rightc "samp".
  rewrite lift_det2.
  autosubst_at rightc "X" "pk".
  remove_at rightc "X".
  autosubst_at rightc "Y" "c".
  autosubst_at rightc "Z" "c".
  autosubst_at rightc "samp" "c".
  remove_at rightc "Y".
  remove_at rightc "Z".
  autosubst_at rightc "samp" "pk".
  hid_str_at rightc "samp2" "pk".
  hid_str_at rightc "samp1" "samp2".
  remove_at rightc "samp".
  rename_at rightc "samp1" "x".
  rename_at rightc "samp2" "y".
  align.
  arg_move_at rightc "c" "x" 0.
  rewrite bind_ret.
  reflexivity.
Qed.

Lemma eg_factor_eq : eg1 <~~> (eg1_factor ||| ddh0).
  r_move_at leftc 0 6.
  reflexivity.
Qed.

Lemma eg_step2 : (eg1_factor ||| ddh1) <~~> eg2.
  rewrite /rlist_comp_hide //= /eg2.

  unfold_bind0_at leftc "samp" "x" tyZq.
  unfold_at leftc "samp".
  unfold_bind1_at leftc "samp" "y" tyZq.
  unfold_at leftc "samp".
  unfold_bind2_at leftc "samp" "z" tyZq.
  unfold_at leftc "samp".

  autosubst_at leftc "X" "pk".
  remove_at leftc "X".
  autosubst_at leftc "samp" "pk".
  hid_str_at leftc "z" "pk".
  hid_str_at leftc "y" "pk".
  hid_str_at leftc "y" "z".
  hid_str_at leftc "x" "z".
  autosubst_at leftc "Y" "c".
  remove_at leftc "Y".
  autosubst_at leftc "Z" "c".
  autosubst_at leftc "samp" "c".
  remove_at leftc "Z".
  remove_at leftc "samp".
  hid_str_at leftc "x" "y".
  hid_str_at leftc "x" "c".
  align.
  arg_move_at leftc "c" "y" 0.
  reflexivity.
Qed.

Lemma eg_step3 : eg2 <~~> ElGamal_ideal.
  rewrite /eg2.
  simpl.
  rewrite /ElGamal_ideal.
  r_move "c" 0.
  r_move "pk" 1.
  r_move "z" 2.
  arg_move_at leftc "c" "z" 0.
  etransitivity.
  ensure_bi_r.
  Check rewr_add_ch_fold.
  r_move_at leftc "z" 0.
  apply: (rewr_add_ch_fold).
  done.
  done.
  instantiate (1 := ("m", tyG)).
  done.
  simpl.

  rewrite /lset /=.
  r_ext_at leftc "z" (fun m => (x <- munif [finType of 'Z_q]; ret (Zp_add x (Zp_opp (log m))))).
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
  unfold_bind1_at leftc "z" "t" tyZq.
  unfold_at leftc  "z".
  hid_weak_at leftc  "t" "c".
  arg_move_at leftc "c" "m" 1.
  arg_move_at leftc "c" "z" 0.
  subst_at leftc "z" "c".
  hid_str_at leftc "z" "c".
  remove_at leftc "z".
  r_ext_at leftc "c" (fun (x : 'Z_q) (x0 : G) (x1 : 'Z_q) (g : G) =>
           ret (exp x1, exp x)).
  intros.
  rewrite -{2}(log_exp x0).
  rewrite -Hop.
  rewrite -Zp_addA.
  rewrite Zp_addNz Zp_addC Zp_add0z //=.
 rename_at leftc "t" "z".
  r_move "c" 0.
  r_move_at leftc "z" 0.
  etransitivity.
  symmetry.
  apply: (rewr_add_ch_fold).
  done.
  done.
  done.
  simpl.
  align.
  arg_move_at leftc "c" "y" 0.
  arg_move_at leftc "c" "pk" 2.
  reflexivity.
Qed.

Lemma ElGamal_secure: ddh0 <~~> ddh1 -> ElGamal_real <~~> ElGamal_ideal.
  intro.
  etransitivity.
  apply eg_step1.
  etransitivity.
  apply eg_factor_eq.
  etransitivity.
  instantiate (1 := eg1_factor ||| ddh1).
  apply: rewr_congr.
  done.
  done.
  done.
  etransitivity.
  apply eg_step2.
  apply eg_step3.
Qed.
  

  