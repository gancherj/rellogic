

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
From mathcomp Require Import fingroup finset. 
From mathcomp Require Import cyclic zmodp.




Inductive Perm {A : Type} : list A -> list A -> Type :=
| perm_nil: Perm nil nil
| perm_skip x l l' : Perm l l' -> Perm (x::l) (x::l')
| perm_swap x y l : Perm (y::x::l) (x::y::l)
| perm_trans l l' l'' :
    Perm l l' -> Perm l' l'' -> Perm l l''.

Lemma Perm_refl {A} (xs : list A) : Perm xs xs.
  induction xs.
  apply perm_nil.
  apply perm_skip; done.
Defined.

Hint Resolve Perm_refl.

Lemma Perm_sym {A} (xs ys : list A) : Perm xs ys -> Perm ys xs.
  elim.
  done.
  intros; apply perm_skip.
  apply X.
  intros; apply perm_swap.
  intros; eapply perm_trans.
  apply X0.
  done.
Defined.

Lemma Perm_rcons {A} (xs : list A) x : Perm (x :: xs) (rcons xs x).
  induction xs.
  simpl.
  done.
  simpl.
  eapply perm_trans.
  apply perm_swap.
  apply perm_skip.
  done.
Defined.

Lemma Perm_cats0 {A} (xs : list A) : Perm xs (xs ++ nil).
  induction xs.
  done.
  simpl; apply perm_skip.
  apply IHxs.
Defined.


Lemma Perm_middle {A} (xs ys : list A) x : Perm (x :: xs ++ ys) (xs ++ (x :: ys)).
  induction xs.
  simpl.
  done.
  simpl.
  eapply perm_trans.
  apply perm_swap.
  apply perm_skip.
  apply IHxs.
Defined.

Fixpoint rot_rcons {A} (n : nat) (xs : list A) :=
  match n, xs with
    | 0, _ => xs
    | S n, (x :: xs) => rot_rcons n (rcons xs x)
    | _, _ => xs
                end.

Lemma Perm_rot {A} n (xs : list A) : Perm xs (rot_rcons n xs).
  move: xs; induction n.
  simpl.
  done.
  simpl.
  induction xs.
  done.
  eapply perm_trans.
  apply Perm_rcons.
  apply IHn.
Defined.


Lemma Perm_cat_sym {A} (xs ys : list A) : Perm (xs ++ ys) (ys ++ xs).
  move: ys; induction xs.
  simpl.
  induction ys.
  done.
  simpl.
  apply perm_skip.
  apply IHys.
  intro; apply Perm_sym.
  move: (Perm_middle ys xs a) => h.
  apply Perm_sym in h.
  eapply perm_trans.
  apply h.
  have -> : (a :: xs) ++ ys = a :: xs ++ ys by done.
  apply perm_skip.
  apply Perm_sym; apply IHxs.
Defined.


Fixpoint Perm_size {A} {xs ys : list A} (H : Perm xs ys) {struct H} :=
  match H with
    | perm_nil => 0
    | perm_skip _ _ _ pf => S (Perm_size pf)
    | perm_swap _ _ pf => 0
    | perm_trans _ _ _ pf1 pf2 => S (Perm_size pf1 + Perm_size pf2)
                                    end.


(* split the sequence in two; the nth element will be the head of the second list *)
Fixpoint seq_split {A} (n : nat) (xs : seq A) : seq A * seq A :=
  match n, xs with
    | 0, xs => (nil, xs) 
    | (S n), (x :: xs) => let p := seq_split n xs in (x :: p.1, p.2)
    | (S n), nil => (nil, nil)
                      end.

Lemma seq_splitE  {A} n (xs : seq A) : (seq_split n xs).1 ++ (seq_split n xs).2 = xs.
  move: xs; induction n.
  done.
  induction 0.
  done.
  simpl.
  rewrite -{3}(IHn xs) //=.
Defined.

Lemma Perm_cat2l {A} (l l0 l1 : list A) :
  Perm l0 l1 -> Perm (l ++ l0) (l ++ l1).
  intro; induction l.
  simpl.
  apply X.
  simpl; apply perm_skip.
  apply IHl.
Defined.

(*
Lemma perm_eq_swap {A : eqType} from to (xs : list A) : perm_eq xs (swap from to xs).
  rewrite /swap.
  remember (seq_split from xs) as p1; destruct p1.
  destruct l0.
  done.
  move: (seq_splitE from xs) => <-. 
  rewrite -Heqp1 //=.
  destruct (from <= to).
  remember (seq_split (to - from) l0) as p2; destruct p2.
  move: (seq_splitE (to - from) l0) => <-.
  rewrite -Heqp2 //=.
  rewrite perm_cat2l.
  have -> : s :: l1 ++ l2 = [:: s] ++ l1 ++ l2 by done.
  rewrite perm_catCA; done.

  remember (seq_split to l) as p2; destruct p2.
  move: (seq_splitE to l) => <-.
  rewrite -Heqp2 //=.
  rewrite -catA.
  rewrite perm_cat2l.
  have -> : l2 ++ s :: l0 = l2 ++ [:: s] ++ l0 by done.
  rewrite perm_catCA; done.
Qed.
*)



Definition swap {A} (from to : nat) (xs : list A) : list A :=
  match (seq_split from xs) with
  | (tl, (x :: hd)) =>
    if from <= to then
    match (seq_split (to - from) hd) with
      | (hd0, hd1) => tl ++ hd0 ++ [:: x] ++ hd1
                         end
    else
      match (seq_split to tl) with
      | (tl0, tl1) => tl0 ++ [:: x] ++ tl1 ++ hd
      end
  | _ => xs
           end.



Lemma Perm_swap {A} from to (xs : list A) : Perm xs (swap from to xs).
  rewrite /swap.
  remember (seq_split from xs) as p1; destruct p1.
  destruct l0.
  done.
  move: (seq_splitE from xs) => <-. 
  rewrite -Heqp1 //=.
  destruct (from <= to).
  remember (seq_split (to - from) l0) as p2; destruct p2.
  move: (seq_splitE (to - from) l0) => <-.
  rewrite -Heqp2 //=.
  apply Perm_cat2l.
  apply Perm_middle.

  remember (seq_split to l) as p2; destruct p2.
  move: (seq_splitE to l) => <-.
  rewrite -Heqp2 //=.
  clear.
  induction l1.
  simpl.
  apply Perm_sym.
  apply Perm_middle.
  simpl.
  apply perm_skip.
  apply IHl1.
Defined.

Lemma Perm_map {A B} (f : A -> B) (xs ys : list A)  :
  Perm xs ys -> Perm (map f xs) (map f ys).
  elim.
  simpl.
  done.
  simpl.
  intros.
  apply perm_skip.
  apply X.
  intros; simpl.
  apply perm_swap.
  intros; simpl in *.
  eapply perm_trans.
  apply X.
  apply X0.
Defined.

Lemma Perm_mem {A : eqType} (xs ys : seq A) :
  Perm xs ys -> forall x, (x \in xs) = (x \in ys).
  intro.
  induction X.
  done.
  intro; rewrite !in_cons.
  destruct (eqVneq x0 x).
  subst.
  rewrite eq_refl //=.
  rewrite (negbTE i) //=.
  intros; simpl; rewrite !in_cons //=.
  destruct (x0 == y); destruct (x0 == x); destruct (x0 \in l); done.
  intros.
  rewrite -IHX2 //=.
Qed.