
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat .
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap tuple.

Require Import Premeas Meas Posrat Aux finfun_fixed .

Definition seq_subset {A : eqType} (xs ys : list A) :=
  all (fun x => x \in ys) xs.

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
Qed.

Hint Resolve Perm_refl.

Lemma perm_eq_size {A} (xs ys : list A) : Perm xs ys -> size xs = size ys.
  elim.
  done.
  simpl; intros.
  rewrite H //=.
  done.
  intros.
  rewrite H //=.
Qed.

Lemma Perm_symm {A} (xs ys : list A) : Perm xs ys -> Perm ys xs.
  elim.
  apply perm_nil.
  intros; apply perm_skip.
  done.
  intros; apply perm_swap.
  intros; eapply perm_trans.
  apply X0.
  done.
Qed.

Theorem Perm_middle A : forall (l1 l2:list A) a,
  Perm (a :: l1 ++ l2) (l1 ++ a :: l2).
  admit.
Admitted.

Lemma Perm_rot {A} (xs : list A) n :
  Perm xs (rot n xs).
  admit.
Admitted.

Class type (T : Type) :=
  {
    terr : T;
    tprod : T -> T -> T;
    tproj : T -> option (T * T);
    _ : forall t1 t2, tproj (tprod t1 t2) = Some (t1, t2)
                                                 }.
    

Section RDef.
  Context (N : choiceType) (T : choiceType) `{type T}.


  Fixpoint Reaction (ns : list N) (n : N) :=
    match ns with
      | nil => meas T
      | n' :: ns' => T -> Reaction ns' n
                                   end.

  Fixpoint detReaction (ns : list N) (n : N) : Type :=
    match ns with
      | nil => T
      | n' :: ns' => T -> detReaction ns' n
                                   end.

  Fixpoint lift_det ns n (r : detReaction ns n) {struct ns} : Reaction ns n.
  destruct ns; simpl in *.
  apply (ret r).
  apply (fun a => lift_det _ _ (r a)).
  Defined.

  Fixpoint rbind {ns} {n n'} (r : Reaction ns n) (k : T -> Reaction ns n') {struct ns} : Reaction ns n'.
    destruct ns; simpl in *.
    apply (mbind r k).
    apply (fun t1 => rbind _ _ _ (r t1) (k t1)).
  Defined.

  Fixpoint detReaction_subst {ns} {n n'} (r : detReaction ns n) (k : Reaction (n :: ns) n') {struct ns} : Reaction (n :: ns) n'.
    destruct ns; simpl in *.
    apply (fun _ => (k r)).
    apply (fun t1 => detReaction_subst _ _ _ (r t1) (k t1)).
  Defined.

  Fixpoint React_eq {ns n} (r1 r2 : Reaction ns n) {struct ns} : Prop.
  destruct ns; simpl in *.
  apply (r1 = r2).
  apply (forall x, React_eq _ _ (r1 x) (r2 x)).
  Defined.


  Definition Reaction_Perm {t1 t2 t'} (r : Reaction t1 t') : Perm t1 t2 -> Reaction t2 t'.
    intro HR.
    induction HR; simpl in *.
    apply r.
    apply (fun x => IHHR (r x)).
    apply (fun x y => r y x).
    apply IHHR2; apply IHHR1; apply r.
  Defined.

  Definition Reaction_prod {ns} {n n'} t (k1 : Reaction ns n) (k2 : Reaction ns n') : (Reaction ns t) * (detReaction (t :: ns) n) * (detReaction (t :: ns) n').
  induction ns; simpl in *.
  apply (x <- k1; y <- k2; ret (tprod x y), fun t => match (tproj t) with | Some p => p.1 | None => terr end,
                   fun t => match (tproj t) with | Some p => p.2 | None => terr end).                                                                         
  set ih := fun t => IHns (k1 t) (k2 t).
  apply (fun t => (ih t).1.1, fun t => (ih t).1.2, fun t => (ih t).2).
  Defined.

Definition reaction :=
  { ns : (list N * bool * N) & Reaction ns.1.1 ns.2 }.

Definition reaction_eq (r1 r2 : reaction) : Prop.
destruct r1, r2.
case (eqVneq x x0).
intro; subst.
apply (React_eq r r0).
intro; apply False.
Defined.

Definition reaction_perm (r : reaction) {ns} (Hp : Perm (tag r).1.1 ns) : reaction.
destruct r; simpl in *.
econstructor.
instantiate (1 := (ns, x.1.2, x.2)).
simpl.
eapply (Reaction_Perm r Hp).
Defined.

Definition rct {ns n} b (r : Reaction ns n) : reaction := existT _ (ns, b, n) r.
Definition drct {ns n} b (r : detReaction ns n) : reaction := existT _ (ns, b, n) (lift_det _ _ r).

Definition reaction_prod (r1 r2 : reaction) (n : N) : (tag r1).1.1 = (tag r2).1.1 -> reaction * reaction * reaction.
intro.
destruct r1, r2; simpl in *.
rewrite H0 in r.
move: (Reaction_prod n r r0) => p.
apply (rct false p.1.1, drct x.1.2 p.1.2, drct x0.1.2 p.2).
Defined.

Definition reaction_bind (r : reaction) n (b : bool) (k : T -> Reaction (tag r).1.1 n) : reaction.
    destruct r; simpl in *.
    econstructor.
    instantiate (1 := (x.1.1, b, n)); simpl.
    eapply rbind.
    apply r.
    apply k.
Defined.

Definition reaction_weak (r : reaction) (n : N) : reaction.
destruct r.
econstructor.
instantiate (1 := (n :: x.1.1, x.1.2, x.2)).
simpl.
apply (fun _ => r).
Defined.

Definition reaction_dep (r : reaction) (n : N) := n \in (tag r).1.1.


Definition rlist := list (reaction + N).

  Fixpoint RHiddens (r : rlist) :=
    match r with
      | nil => nil
      | inr _ :: rs => RHiddens rs
      | inl (existT p _) :: rs =>
        if p.1.2 then RHiddens rs else p.2 :: RHiddens rs
                                                       end.

Fixpoint ROutputs (r : rlist) :=
    match r with
      | nil => nil
      | inr _ :: rs => ROutputs rs
      | inl (existT p _) :: rs =>
        if p.1.2 then p.2 :: ROutputs rs else ROutputs rs
                                                       end.

  Fixpoint RInputs (r : rlist) :=
    match r with
    | nil => nil
    | inr n :: rs => n :: RInputs rs
    | inl _ :: rs => RInputs rs
                             end.

  Definition RChans r := RHiddens r ++ ROutputs r ++ RInputs r.

  Definition rlist_nub (r : rlist) :=
    filter (fun p =>
              match p with
                | inl _ => true
                | inr i => i \notin (ROutputs r) end) r.

  Definition rlist_comp (r1 r2 : rlist) := rlist_nub (r1 ++ r2).

  Definition use_dominates (rs : rlist) (h : N) (c : N) :=
    all (fun ri =>
           match ri with
             | inl r => (h \in ((tag r).1.1)) ==> (c \in ((tag r).1.1))
             | inr _ => true end) rs.
  
  Inductive r_rewr : rlist -> rlist -> Prop :=
  | rewr_refl : forall r, r_rewr r r
  | rewr_trans : forall r1 r2 r3, r_rewr r1 r2 -> r_rewr r2 r3 -> r_rewr r1 r3
  | rewr_perm : forall r1 r2, Perm r1 r2 -> r_rewr r1 r2
  | rewr_ext : forall r1 r2 rs, reaction_eq r1 r2 -> r_rewr (inl r1 :: rs) (inl r2 :: rs)
  | rewr_r_perm : forall rs r {ns} (H : Perm _ ns), r_rewr (inl r :: rs) (inl (reaction_perm r H) :: rs)
  | rewr_unfold : forall rs r n (k : T -> Reaction (tag r).1.1 n) (b : bool) ,
      (tag r).2 \notin RChans rs ->
      (tag r).1.2 = false ->
      r_rewr (inl (reaction_bind r n b k) :: rs) 
             (inl r :: inl (@rct ((tag r).2 :: (tag r).1.1) _ b k) :: rs)
  | rewr_fold : forall rs r n (k : T -> Reaction (tag r).1.1 n) (b : bool) ,
      (tag r).2 \notin RChans rs ->
      (tag r).1.2 = false ->
      r_rewr (inl r :: inl (@rct ((tag r).2 :: (tag r).1.1) _ b k) :: rs)
             (inl (reaction_bind r n b k) :: rs) 
  | rewr_subst : forall (rs : rlist) ns b1 b2 h f (r : detReaction ns h) (k : Reaction (h :: ns) f),
      r_rewr (inl (drct b1 r) :: inl (rct b2 k) :: rs)
             (inl (drct b1 r) :: inl (rct b2 (detReaction_subst r k)) :: rs)
  | rewr_weak : forall (rs : rlist) (r : reaction) (r' : reaction), 
      reaction_dep r (tag r').2 ->
      r_rewr (inl r :: inl r' :: rs)
             (inl (reaction_weak r (tag r').2) :: inl r' :: rs)
  | rewr_str : forall (rs : rlist) ns h f b (k : Reaction ns f),
      h \in RHiddens rs ->
      r_rewr (inl (@rct (h :: ns) _ b (fun _ => k)) :: rs)
             (inl (rct b k) :: rs)
  | rewr_dep : forall (rs : rlist) (r : reaction) (n : N),
      (tag r).1.2 = false ->
      use_dominates rs (tag r).2 n ->
      r_rewr (inl r :: rs)
             (inl (reaction_weak r n) :: rs)
  | rewr_comp : forall r1 r2 r3, r_rewr r1 r2 -> r_rewr (rlist_comp r1 r3) (rlist_comp r2 r3)
  | rewr_prod : forall rs (r1 r2 : reaction) n (H : (tag r1).1.1 = (tag r2).1.1),
      n \notin RChans rs ->
      let p := reaction_prod r1 r2 n H in
      r_rewr (inl r1 :: inl r2 :: rs) (inl p.1.1 :: inl p.1.2 :: inl p.2 :: rs)
  | rewr_unprod : forall rs (r1 r2 : reaction) n (H : (tag r1).1.1 = (tag r2).1.1),
      n \notin RChans rs ->
      let p := reaction_prod r1 r2 n H in
      r_rewr (inl p.1.1 :: inl p.1.2 :: inl p.2 :: rs) (inl r1 :: inl r2 :: rs).
  End RDef.

Add Parametric Relation (N T : choiceType) `{type T} : (@rlist N T) (@r_rewr N T _)
    reflexivity proved by (@rewr_refl _ _ _)
    transitivity proved by (@rewr_trans _ _ _) as r_rewr_rel.

Arguments r_rewr [N T H].

Section RLems.
  Context (N T : choiceType) `{type T}.

  Lemma rewr_rot : forall n (rs : rlist N T), r_rewr rs (rot n rs).
    intros.
    apply rewr_perm.
    apply Perm_rot.
  Qed.

End RLems.


