

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


Lemma Perm_swap_irrel {A} from to (xs : list A) : Perm xs (swap from to xs).
  apply Perm_swap.
Qed.


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

Fixpoint ofind {A} (xs : seq A) (f : A -> bool) : option nat :=
  match xs with
    | nil => None
    | x :: xs' =>
      if f x then Some 0%N else
        match ofind xs' f with
          | Some n => Some (S n)
          | None => None
        end
          end.

Fixpoint ofind_val {A} (xs : seq A) (f : A -> bool) : option A :=
  match xs with
    | nil => None
    | x :: xs' =>
      if f x then Some x else
        match ofind_val xs' f with
          | Some x => Some x
          | None => None
        end
          end.

Fixpoint prefix {A : eqType} (xs ys : seq A) : bool :=
  match xs with
    | nil => true
    | x :: xs' =>
      match ys with
      | nil => false
      | y :: ys' =>
        if x == y then prefix xs' ys' else false
      end
        end.
                      
Lemma prefixP {A : eqType} (xs ys : seq A) : prefix xs ys -> {zs | ys = xs ++ zs}.
  move: ys.
  induction xs.
  simpl.
  intros; exists ys; done.
  induction ys.
  done.
  simpl.
  destruct (eqVneq a a0).
  subst.
  rewrite eq_refl.
  intro h; destruct (IHxs _ h).
  subst.
  exists x.
  done.
  rewrite (negbTE i).
  done.
Defined.

Lemma prefix_cat {A : eqType} (xs ys : seq A) : prefix xs (xs ++ ys).
  induction xs.
  done.
  simpl.
  rewrite eq_refl.
  done.
Defined.

Fixpoint extract_right_cat {A : eqType} (xs ys : seq A) : option (seq A) :=
  match xs, ys with
  | nil, nil => Some nil
  | (x :: xs), nil => None
  | nil, y :: ys => Some (y :: ys)
  | (x :: xs), (y :: ys) =>
    if x == y then
      extract_right_cat xs ys
    else
      None
  end.

Lemma extract_right_catP {A : eqType} (xs ys : seq A) zs :
  extract_right_cat xs ys = Some zs ->
  ys = xs ++ zs.
  move: ys; induction xs.
  induction ys.
  simpl.
  intro H; injection H; done.
  simpl.
  intro H; injection H; done.
  induction ys.
  simpl.
  done.
  simpl.
  destruct (eqVneq a a0).
  subst.
  rewrite eq_refl.
  move/IHxs.
  move => ->; done.
  rewrite (negbTE i).
  done.
Qed.

Definition extract_cons {A : eqType} (a : A) (xs : seq A) : option (seq A).
  destruct xs.
  apply None.
  apply (if a == s then Some xs else None).
Defined.

Lemma extract_consP {A : eqType} (a : A) xs ys :
  extract_cons a xs = Some ys -> xs = a :: ys.
  induction xs.
  done.
  simpl.
  destruct (eqVneq a a0).
  destruct e.
  rewrite eq_refl.
  intro h; injection h.
  move => ->.
  done.
  rewrite (negbTE i); done.
Qed.


Definition extract_right_cons_cat {A : eqType} (h : A) (xs ys : seq A) : option (seq A) :=
  match extract_cons h ys with
    | None => None
    | Some ys' =>
      extract_right_cat xs ys'
                        end.

Lemma extract_right_cons_catP {A : eqType} (h : A) xs ys zs :
  extract_right_cons_cat h xs ys = Some zs ->
  ys = h :: xs ++ zs.
  rewrite /extract_right_cons_cat.
  remember (extract_cons h ys) as o; destruct o; symmetry in Heqo.
  apply extract_consP in Heqo.
  rewrite Heqo.
  move/extract_right_catP.
  move => ->.
  done.
  done.
Qed.

Lemma orP_sumbool {b1 b2 : bool} : (b1 || b2) -> {b1} + {b2}.
  destruct b1.
  intro; apply left; apply is_true_true.
  destruct b2.
  intros; apply right; apply is_true_true.
  done.
Qed.

Lemma Perm_rem_cat_l {A : eqType} (xs ys : seq A) x : x \in ys ->
                                                            Perm (xs ++ ys) ((x :: xs) ++ (rem x ys)).
  move: x ys.
  induction xs.
  simpl.
  induction ys.
  done.
  simpl.
  destruct (eqVneq a x).
  subst.
  rewrite eq_refl.
  intros; apply Perm_refl.
  rewrite (negbTE i).
  intros.
  eapply perm_trans; last first.
  apply Perm_sym.
  apply perm_swap.
  apply perm_skip.
  apply IHys.
  rewrite in_cons in H.
  rewrite eq_sym (negbTE i) in H; done.
  intros; simpl.
  eapply perm_trans; last first.
  apply perm_swap.
  apply perm_skip.
  apply IHxs.
  done.
Qed.