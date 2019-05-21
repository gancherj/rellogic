
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
From mathcomp Require Import fingroup finset. 
From mathcomp Require Import cyclic zmodp.

Require Import Posrat Premeas Meas Aux Reaction finfun_fixed String SSRString SeqOps.

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
       [:: ("tup", tyPair (tyPair tyG tyG) tyG)] ~> ("pk", tyG) dvis (fun x => x.1.1);
       inr "m"%string;
       [:: ("tup", tyPair (tyPair tyG tyG) tyG); ("m", tyZq)] ~> ("c", tyPair tyG tyG) dvis
                                                              (fun t y => (t.1.2, t.2 * (g ^+ y))%g)
                                                              ].

    Close Scope posrat_scope.
    Open Scope nat_scope.

  Arguments rbind [N T H ].
  
  Lemma p1 : r_rewr pke pke1.
    rewrite /pke /pke1.
    r_subst "pk" "c".
    r_str "c" "pk".

    unfold_bind "x" "t" tyZq.
    r_subst "x" "pk".
    r_str "pk" "x".

    r_subst "x" "c".
    r_str "c" "x".
    r_clean.
    r_ext (fun x x0 x1 =>
             z <- ret (g ^+ (x * x0))%g; ret ((g ^+ x0)%g, z * g ^+ x1)%g).
        intros; msimp; done.
    simpl.
    unfold_bind "c" "tmp" tyG.



    unfold_bind3 "c" "tmp" tyG.
    simpl.


    r_subst "x" "c".
    r_str "c" "x".
    r_clean.


    r_rename "t" "x".
    r_str "c" "pk".

    rewrite 
     
    
    Check lift_bind.

    lift_bind0 "x" "t" tyZq.



      
    etransitivity.
    apply rewr_ext.
    set Goal0 := 3.
    instantiate (1 := (rbind nil ("t", tyZq) ("x", tyZq) (munif [finType of 'Z_q]) (fun x => ret x))).
    simpl.
    done.

    apply lift_bind.
    apply: lift_bind.
    

    Ltac lift_bind0 m n t :=
      r_move m 0%N;
      etransitivity; [ apply rewr_ext; 
    match goal with
    | [ |- React_eq _ _ _ (_, _, ?to).2 (mbind ?m ?k) _] => apply: (@lift_bind t _ m k n)
                                                                                          end | idtac].

    lift_bind0 "x" "t" tyZq.
                                                                                                       end.
    lift_bind1 "x" "t" tyZq.
    etransitivity.
    apply rewr_ext.

    lift_bind1 "x" "t" tyZq.
    r_unfold1 tyZq "t".
    rewrite bind_ret.
    simpl.
    r_move "y" 1.
    r_prod "tmp".
    r_swap 1 0.
    r_ext (fun a : 'Z_q * 'Z_q => (x <- ret a.1; ret x)).
    intros; msimp.
    done.
    r_unfold1 tyZq "t".
    r_swap 1 0.
    rct_swap 1 0.
    r_swap 2 1.
    r_str.

    r_swap 
    r_swap 2 1.
    r_swap 
    etransitivity.
    apply rewr_ext.
    Check lift_bind1.

    apply: (@lift_bind1 _ _ _ ("tmp", tyPair tyZq tyZq) tyZq ("x", tyZq) _ _ "t").
    apply 
    r_unfold1 tyZq "t".
    etransitivity.
    apply rewr_ext.
    lift_bind1 tyZq "t".
    r_unfold1 tyZq "t".
    simpl.
    r_at 1 ltac:(rct_swap 1 0).
    r_swap 1 0.
    Check rewr_str.
    r_swap 2 1.
    r_str.

    rewrite rewr_str; last first.
    done.
    simpl.
    simpl.
    admit.
    simpl.
    simpl.

    admit.

    
    rewrite rewr_str; last first.
    done.
    last 
    Check rewr_str.
    Check r_str.
    r_str.
    r_at 1 ltac:(r_str).

    simpl.
    rewrite /rct.
    lift_bind1 tyZq "t".
    r_unfold.
    simpl.

    etransitivity.
    eapply rewr_unfold.
    done.
    done.

    etransitivity; [apply rewr_ext; lift_bind1 tyZq "t" | idtac].
    etransitivity.
    apply rewr_ext.
    lift_bind1 tyZq "t".
    match goal with
    | [ |- React_eq _ _ (?from :: nil, _, _).1.1 ?to (fun arg => mbind ?m ?k) _] => apply (@lift_bind1 from _ to "t" _ _)

     (* apply (@lift_bind1 from tyZq to "t" _ _)*)
                                                                   end.

    apply (@lift_bind1 ("tmp", tyPair tyZq tyZq) tyZq ("x", tyZq) "t" _ _) => h.
    simpl.
    
    simpl.
    apply h.
    eapply (@lift_bind1 _ _ ).
    Check lift_bind1.
    simpl.
    eapply (lift_bind1 _ _ _).
    instantiate (1 := rbind _ ("t", tyZq) ("x", tyZq) (fun a : 'Z_q * 'Z_q => _) _).
    simpl.
    Show Existentials.
    intro.
    instantiate (3 := (fun x : 'Z_q * 'Z_q => ret x.1)).
    Unshelve.
    r_ext (rbind (fun a : 'Z_q * 'Z_q => ret a.1) (fun a : 'Z_q => fun _ => ret a)).
    etransitivity.
    apply rewr_ext.
    
    apply lift_bind1.
    h
    
    Check lift_bind1.
    eapply (lift_bind1 _ _ (tyZq, "t")).
    eapply lift_bind1.

    erewrite lift_bind1.
    Check reaction_bind.
    rewrite 
    intros; try msimp.

    rewrite /React_eq; simpl.
    etransitivity.
    apply rewr_ext.
    instantiate (1 := (fun a => ret a.1)).

    kk
    Check rewr_ext.
    match goal with
    | [ |- r_rewr (inl (existT _ ?p _) :: _) _] => eapply (rewr_ext _ _ _ p _ (fun a => ret a.1))
                                                  end.
    apply (rewr_ext _ _ _ _ _ (fun a => _)).
    instantiate (1 := (fun a => ret a.1)).
    inst
    r_swap 3 1.
    rewrite lift_det1.
    r_weak "tmp" (tyPair tyZq tyZq).
    r_at 1 ltac:(rct_swap 1 0).
    r_subst.
    r_swap 1 0; r_str.
    rewrite !lift_det1.
    r_

    r_str.
    r_str_inv.
    r_swap 4 1.
    r_str_inv.
    etransitivity; [
    match goal with 
    | [ |- r_rewr  (_ :: inl (existT _ (_, _, ?n) _) :: _) _ ] => apply (rewr_str_inv _ _ n); done
                                                                end | idtac].

    apply (rewr_str_inv _ _ ("x", tyZq)); done.
    done.
    done.
    done.
    eapply rewr_str_inv.
    erewrite rewr_str_inv.
    admit.
    done.
    simpl.
    done.
    instantiate (1 := ("x", tyZq)).
    done.
    etransitivity.
    Check rewr_str_inv.
    erewrite rewr_str_inv.
    etransitivity; [apply rewr_str; done | idtac].
    rewrite rewr_str; [idtac | done | done].

    etransitivity.
    eapply rewr_str.
    simpl.
    done.
    done.

    eapply rewr_str.
    Check
    r_rename "ldjf" "tup".
    etransitivity; [apply (rewr_rename _ _ _ "tmp" "tup"); done | idtac]; simpl.
    Check (rewr_rename _ _ _ "tmp" "tup").
    rewrite (rewr_rename _ _ _ "tmp" "tup").

    r_rename "tmp" "tup".
    etransitivity.
    apply (rewr_rename _ _ _ "tmp" "tup").
    done.
    simpl.

    simpl.
    
    Qed.

    r_at 1 ltac:(r_str).
    r_swap 1 0.
    r_swap 5 1.
    r_weak "tmp" (tyPair tyZq tyZq).
    r_swap 1 0.



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
