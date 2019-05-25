(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* Type classes and theory for groups, including finite cyclic groups. *)

Set Implicit Arguments.

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
From mathcomp Require Import finset. 
From mathcomp Require Import zmodp.

(* with a fixed generator *)
Class FinCyclicGroup (T : finType) :=
  {
    order : nat;
    log : T -> 'Z_order;
    exp : 'Z_order -> T;
    fcg_op : T -> T -> T;
    Hop : {morph exp : x y / Zp_add x y >-> fcg_op x y};
    exp_log : cancel exp log;
    log_exp : cancel log exp
                 }.

Infix "*" := fcg_op : fcg_scope.
Delimit Scope fcg_scope with fcg.
Local Open Scope fcg_scope.


Section FCGLems.
  Context (T : finType) `{FinCyclicGroup T}.
  Definition ident : T := exp 0%R.
  Definition inverse (x : T) := exp (Zp_opp (log x)).
  Lemma mulgA : forall (x y z : T),
      x * (y * z) = (x * y) * z.
    intros.
    rewrite -(log_exp x) -(log_exp y) -(log_exp z).
    rewrite -!Hop.
    rewrite Zp_addA.
    done.
  Qed.

  Lemma mulgC : forall (x y : T),
      x * y = y * x.
    intros.
    rewrite -(log_exp x) -(log_exp y) -!Hop Zp_addC //=.
  Qed.

  Lemma mulg0 : forall x,
      x * ident = x.
    intro; rewrite /ident -(log_exp x) -Hop.
    rewrite Zp_addC Zp_add0z //=.
  Qed.

  Lemma mul0g : forall x,
      ident * x = x.
    intro; rewrite /ident -(log_exp x) -Hop.
    rewrite  Zp_add0z //=.
  Qed.

  Lemma mulg_inv : forall x,
      x * (inverse x) = ident.
    intro; rewrite /ident -(log_exp x).
    rewrite /inverse.
    rewrite exp_log.
    rewrite -Hop.
    rewrite Zp_addC.
    rewrite Zp_addNz.
    done.
  Qed.

  Lemma mul_invg : forall x,
      (inverse x) * x = ident.
    intro; rewrite /ident -(log_exp x).
    rewrite /inverse.
    rewrite exp_log.
    rewrite -Hop.
    rewrite Zp_addNz.
    done.
  Qed.

  Lemma exp_inj : injective exp.
    move => x y.
    move/eqP => h.
    apply/eqP.
    apply/contraT => hc.
    rewrite -(exp_log x) -(exp_log y) in hc.
    rewrite (eqP h) in hc.
    rewrite eq_refl in hc.
    done.
  Qed.

  Lemma ident_unique : forall x y,
      x * y = y ->
      x = ident.
    intros.
    have: x * y * (inverse y) = ident.
    rewrite H0 mulg_inv //=.
    move => <-.
    rewrite -mulgA mulg_inv mulg0 //=.
  Qed.
    
End FCGLems.


