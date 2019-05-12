
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
From mathcomp Require Import fingroup finset. 
From mathcomp Require Import cyclic zmodp.

Require Import Posrat Premeas Meas Aux Reaction finfun_fixed String SSRString SeqOps.

Check rct.
Arguments rct [N T H].
Arguments drct [N T H].
Arguments lift_det [N T H].

Notation "G ~> c 'vis' D" := (inl (existT _ (G, true, c) D)) (at level 80).
(*
Notation "G ~> c 'vis' D" := (inl (rct G c true D)) (at level 80).

Notation "G ~> c 'dvis' D" := (inl (drct G c true D)) (at level 80).

Notation "G ~> c 'hid' D" := (inl (rct G c false D)) (at level 80).
Notation "G ~> c 'dhid' D" := (inl (drct G c false D)) (at level 80).
*)

Arguments Reaction [N T H].

Notation "G ~> c 'dvis' D" := (inl (existT (fun ns => Reaction ns.1.1 ns.2) (G%SEQ, true, c) (lift_det G c D))) (at level 80).

Notation "G ~> c 'hid' D" := (inl (existT _ (G, false, c) D)) (at level 80).

Notation "G ~> c 'dhid' D" := (inl (existT (fun ns => Reaction ns.1.1 ns.2) (G%SEQ, false, c) (lift_det G c D))) (at level 80).


Notation inp x := (inr _ _ x).

Section DDH.
  Context (G : finGroupType) (g : G).
  Definition q := order g.

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

  Fixpoint denomTy (t : ty) : finType :=
    match t with
      | tyUnit => [finType of unit]
      | tyZq => [finType of 'Z_q]
      | tyG => [finType of G]
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
[:: [::] ~> ("out", tyPair (tyPair tyG tyG) tyG)
    vis (x <- munif [finType of 'Z_q];
         y <- munif [finType of 'Z_q]; ret ((g ^+ x)%g, (g ^+ y)%g, (g ^+ (x * y))%g))].

Definition ddh1 : rl :=
[:: [::] ~> ("out",
 tyPair (tyPair tyG tyG) tyG)
    vis (x <- munif [finType of 'Z_q];
         y <- munif [finType of 'Z_q];
         z <- munif [finType of 'Z_q];
         ret ((g ^+ x)%g, (g ^+ y)%g, (g ^+ z)%g))].

  Definition pke : rl :=
    [:: [::] ~> ("x", tyZq) hid (x <- munif [finType of 'Z_q]; ret x);
       [:: ("x", tyZq)] ~> ("pk", tyG) dvis (fun x  => (g ^+ x)%g);
       [::] ~> ("y", tyZq) hid (munif [finType of 'Z_q]);
       inr "m";
       [:: ("x", tyZq); ("y", tyZq); ("pk", tyG); ("m", tyZq)] ~> ("c", tyPair tyG tyG) dvis
                                                               (fun x y pk m => (g ^+ y, g ^+ (x * y) * g ^+ m))%g
                                                               ].


  Definition pke1 : rl :=
    [:: [::] ~> ("tup", tyPair (tyPair tyG tyG) tyG) hid ((x <- munif [finType of 'Z_q];
                                                             y <- munif [finType of 'Z_q]; ret ((g ^+ x)%g, (g ^+ y)%g, (g ^+ (x * y))%g)));
       [:: ("tup", tyPair (tyPair tyG tyG) tyG)] ~> ("pk", tyG) dvis [ffun x => x.1.1];
       inr "m"%string;
       [:: ("tup", tyPair (tyPair tyG tyG) tyG); ("m", tyZq)] ~> ("c", tyPair tyG tyG) dvis
                                                              (fun t y => (t.1.2, t.2 * (g ^+ y))%g)
                                                              ].


  Notation "x1 ~~> x2" := (r_rewr x1 x2) (at level 40).

    Ltac r_swap from to := etransitivity; [apply rewr_perm; apply (Perm_swap from to) | idtac]; rewrite /swap /=.

    Ltac rct_swap from to := etransitivity; [apply (rewr_r_perm _ _ _ _ (Perm_swap from to _)) | idtac]; rewrite /swap /=.

    Ltac r_prod n := rewrite (rewr_prod _ _ n); [instantiate (1 := erefl) | done]; simpl.

    Ltac r_at n t := r_swap n 0%N; t; r_swap n 0%N.

    Ltac r_weak n t := rewrite (rewr_weak _ _ (n, t)); [idtac | done | done]; rewrite /=.

    Ltac r_subst := rewrite rewr_subst; rewrite /rct /drct /=.

    Ltac r_str := rewrite rewr_str /rct /=; [idtac | done].

    Lemma r_rewr_r (r1 r2 r3 : rl) : r2 ~~> r3 -> r1 ~~> r2 -> r1 ~~> r3.
      intro ; etransitivity.
      apply H0.
      done.
     Qed.

    
    
 

    Close Scope posrat_scope.
    Open Scope nat_scope.

  Lemma p1 : r_rewr pke pke1.
    rewrite /pke /pke1.
    rewrite bind_ret.
    r_swap 2 1.
    r_prod "tmp".
    r_swap 1 0.
    r_swap 3 1.
    rewrite lift_det1.
    r_weak "tmp" (tyPair tyZq tyZq).
    r_at 1 ltac:(rct_swap 1 0).
    r_subst.
    r_at 1 ltac:(r_str).

    r_swap 1 0.
    r_str.
    rewrite rewr_str /rct /=.
    rewrite rewr_subst.
    rewrite /rct /=.
    simpl.
    admit.
    done.
    simpl.
    rewrite /reaction_dep //=.
    simpl.
    rewrite (rewr_weak _ _ ("tmp", tyPair tyZq tyZq)).
    simpl.
    instantiate (1 := ("tmp", tyPair tyZq tyZq)).
    simpl.
    etransitivity.

    eapply rewr_subst.

    admit.
    done.
    simpl.

    simpl.
    etransitivity.


    soi
    simpl.


    Check rewr_subst.
    eapply (rewr_subst _ _ _ _ _ _ _ _ _ _).
    rewrite rewr_subst1.
    Check rewr_subst.
    have : [:: ("tmp", _) ~> ("x", tyZq) hid _] = drct [:: ("tmp", tyPair tyZq tyZq)] ("x", tyZq) false (fun a : 'Z_q * 'Z_q => ret a.1).
    rewrite rewr_subst.

    r_swap 2 1.
    r_swap 2 0.
    r_swap 4 1.
    r_swap 1 0.
    rct_swap 2 0.
    r_swap 1 0.
    rewrite rewr_subst.

    r_prod "tmp".

    r_swap 2 1.
    Check rewr_subst.



    Check rewr_trans.
    apply (rewr_trans _ _ _ _ _ ).
    etransitivity.
    apply (rewr_prod _ _ "tmp" _ _ _ _ erefl). 
    done.
    instantiate (1 := erefl).

    instantiate (1 := "tmp").
    done.
    instantiate (1 := erefl).
    simpl.

    rewrite /rct.
    rewrite /drct.
    simpl.
    simpl.


    r_swap 1%N 0%N.
    r_swap 4%N 0%N.

    rct_swap 1%N 0%N.

    r_swap 3%N 0%N.


    etransitivity.
    apply (rewr_r_perm _ _ _ _ (Perm_swap 1%N 0%N _)).
    simpl.
    rewrite /swap //=.
    rewrite /Reaction_Perm.
    simpl.
    rewrite /Perm_swap.
    simpl.
    rewrite /catA.

    apply (rewr_rperm_app _ _ _ _ _ _ (Perm_rot 3 _)).
    simpl.
    apply rewr_r_perm.
    Chec
    Check Perm_rot.
    instantiate (1 := Perm_rot 3).
    eapply rewr_r_perm.
    Check rewr_perm_r.
    have: Perm [:: ("x", tyZq); ("y", tyZq); ("pk", tyG); ("m", tyZq)]
               [:: ("pk", tyG); ("x", tyZq); ("y", tyZq); ("m", tyZq)].

    Check rewr_r_perm.
    r_swap 2
    Check rewr_subst.

    etransitivity.
    apply rewr_prod.
    instantiate (1 := "tmp").
    done.
    instantiate (1 := erefl).
    simpl.

    eapply r_rewr_r.

    eapply rewr_fold.
    done.
    done.

    rewrite /reaction_bind.
    simpl.
    rewrite !measE.
    simpl.

    Check rewr_subst.

    Check rewr_prod.

    done.
    simpl.
    simpl.
    simpl.

    
    apply perm_cons.

    etransitivity; apply rewr_perm; first by apply perm_swap.

    etransitivity.
    apply rewr_perm.
    apply perm_skip.
    apply perm_swap.
    Check perm_swap.
    eapply rewr_ext.
    instantiate (1 := (rct [::] ("x", tyZq) false 
    simpl.
    eapp
    rewrite ret_bind.
 jkkkkkkkkkkkkkkkk   etransitivity.



  Check
  Check (rlist string ty).
  Definition 

  Check [finType of 'Z_q].
  Check rlist.
  Definition ddh0
  Check 
  Check (fun i => g ^+ i)%g.
  Check commute.
  Check cyclic.
  Check cyclicGroupType.
Check cyclic.
