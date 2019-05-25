
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
From mathcomp Require Import fingroup finset. 
From mathcomp Require Import cyclic zmodp.

Require Import Posrat Premeas Meas Aux Reaction finfun_fixed String SSRString SeqOps.

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
       [:: ("x", tyZq)] ~> ("pk", tyG) dvis (fun x  => (exp x)%g);
       inr "m";
       [::] ~> ("y", tyZq) hid (munif [finType of 'Z_q]);
       [:: ("x", tyZq); ("y", tyZq); ("pk", tyG); ("m", tyG)] ~> ("c", tyPair tyG tyG) dvis
                                                               (fun x y pk m => (exp y, (exp (Zp_mul x y)) * m))%fcg
                                                               ].
Definition ElGamal_ideal : rl :=
  [:: [::] ~> ("x", tyZq) hid (munif [finType of 'Z_q]);
     [:: ("x", tyZq)] ~> ("pk", tyG) dvis (fun x => exp x)%g;
    [::] ~> ("y", tyZq) hid (munif [finType of 'Z_q]);
    [::] ~> ("z", tyZq) hid (munif [finType of 'Z_q]);
    inr "m";
    [:: ("y", tyZq); ("z", tyZq); ("pk", tyG); ("m", tyG)] ~> ("c", tyPair tyG tyG) dvis (fun y z _ m =>
                                                                               (exp y, (exp z))%g)].

Definition eg1 : rl :=
  [:: [::] ~> ("samp", tyPair (tyPair tyG tyG) tyG) hid (x <- munif [finType of 'Z_q]; y <- munif [finType of 'Z_q]; ret (exp x, exp y, exp (Zp_mul x y))%fcg);
     [:: ("samp", tyPair (tyPair tyG tyG) tyG)] ~> ("X", tyG) dhid (fun x => x.1.1);
     [:: ("samp", tyPair (tyPair tyG tyG) tyG)] ~> ("Y", tyG) dhid (fun x => x.1.2);
     [:: ("samp", tyPair (tyPair tyG tyG) tyG)] ~> ("Z", tyG) dhid (fun x => x.2);
     inr "m";
     [:: ("X", tyG)] ~> ("pk", tyG) dvis id;
     [:: ("Y", tyG); ("Z", tyG); ("pk", tyG); ("m", tyG)] ~> ("c", tyPair tyG tyG) dvis (fun y z pk m => (y, z * m)%fcg)]. 

Definition eg1_factor : rl :=
  [:: inr "samp"; 
     [:: ("samp", tyPair (tyPair tyG tyG) tyG)] ~> ("X", tyG) dhid (fun x => x.1.1);
     [:: ("samp", tyPair (tyPair tyG tyG) tyG)] ~> ("Y", tyG) dhid (fun x => x.1.2);
     [:: ("samp", tyPair (tyPair tyG tyG) tyG)] ~> ("Z", tyG) dhid (fun x => x.2);
     inr "m";
     [:: ("X", tyG)] ~> ("pk", tyG) dvis id;
     [:: ("Y", tyG); ("Z", tyG); ("pk", tyG); ("m", tyG)] ~> ("c", tyPair tyG tyG) dvis (fun y z pk m => (y, z * m)%fcg)]. 

Definition eg2 : rl :=
  [:: [::] ~> ("x", tyZq) hid (munif [finType of 'Z_q]);
     [:: ("x", tyZq)] ~> ("pk", tyG) dvis (fun x => exp x)%g;
    [::] ~> ("y", tyZq) hid (munif [finType of 'Z_q]);
    [::] ~> ("z", tyZq) hid (munif [finType of 'Z_q]);
    inr "m";
    [:: ("y", tyZq); ("z", tyZq); ("pk", tyG); ("m", tyG)] ~> ("c", tyPair tyG tyG) dvis (fun y z _ m =>
                                                                               (exp y, (exp z) * m)%fcg)].


    Close Scope posrat_scope.
    Open Scope nat_scope.

  Arguments rbind [N T H ].
  
Lemma eg_step1 : r_rewr ElGamal_real eg1.
  rewrite /ElGamal_real.
    admit.
Admitted.

Lemma eg_factor_eq : r_rewr eg1 (eg1_factor ||| ddh0).
  r_move 0 6.
  apply rewr_refl.
Qed.

Lemma eg_step2 : r_rewr (eg1_factor ||| ddh1) eg2.
  r_move 6 0.
  unfold_bind0 "samp" "x" tyZq.
  r_move "samp" 0.
  unfold_bind1 "samp" "y" tyZq.
  r_move "samp" 0.
  unfold_bind2 "samp" "z" tyZq.
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
  rewrite !lift_det3.
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
Qed.


Lemma eg_step3 : r_rewr eg2 ElGamal_ideal.
  rewrite /eg2.
  simpl.
  r_move "z" 0.
  r_move "m" 1.
  rewrite rewr_str_inp_inv.
  instantiate (1 := tyG).
  simpl.
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
  (* TODO: congr rule *)
  admit.
  etransitivity.
  apply eg_step2.
  apply eg_step3.
Admitted.
  

  