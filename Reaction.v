
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat .
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap tuple.

Require Import Premeas Meas Posrat Aux finfun_fixed SeqOps.



Class type (T : eqType) :=
  {
    denomT : T -> finType;
    tprod : T -> T -> T;
    Hprod : forall t1 t2, denomT (tprod t1 t2) = [finType of (denomT t1) * (denomT t2)]
                                               }.

Section RDef.
  Context (N : choiceType) (T : choiceType) `{type T}.

  Fixpoint Reaction (ns : list (N * T)) (n : N * T) :=
    match ns with
      | nil => meas (denomT n.2)
      | n' :: ns' => (denomT n'.2 -> Reaction ns' n)
                                   end.

  Fixpoint detReaction (ns : list (N * T)) (n : N * T) : Type :=
    match ns with
      | nil => (denomT n.2)
      | n' :: ns' => (denomT n'.2 -> detReaction ns' n)
                                   end.

  Fixpoint lift_det ns n (r : detReaction ns n) {struct ns} : Reaction ns n.
  destruct ns; simpl in *.
  apply (ret r).
  apply (fun a => lift_det _ _ (r a)).
  Defined.

  Fixpoint rbind {ns} {n n'} (r : Reaction ns n) (k : denomT n.2 -> Reaction ns n') {struct ns} : Reaction ns n'.
    destruct ns; simpl in *.
    apply (mbind r k).
    apply (fun t1 => rbind _ _ _ (r t1) (fun x => k x t1)).
  Defined.

  Fixpoint detReaction_subst {ns} {n n'} (r : detReaction ns n) (k : Reaction (n :: ns) n') {struct ns} : Reaction (n :: ns) n'.
    destruct ns; simpl in *.
    apply (fun _ => (k r)).
    intros x y.
    apply (detReaction_subst _ _ n' (r y) (fun z => k z y) x).
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

  Definition Reaction_prod {ns} {n n'} t (k1 : Reaction ns n) (k2 : Reaction ns n') : (Reaction ns (t, tprod n.2 n'.2)) * (detReaction ((t, tprod n.2 n'.2) :: ns) n) * (detReaction ((t, tprod n.2 n'.2) :: ns) n').
  induction ns; simpl in *.
  rewrite !Hprod //=.
  apply (k1 ** k2, fst, snd).
  rewrite !Hprod //= in IHns.
  set ih := fun t => IHns (k1 t) (k2 t).
  split.
  split.
  apply (fun t => (ih t).1.1).
  rewrite Hprod //=.
  apply (fun p x => (ih x).1.2 p).
  rewrite Hprod //=.
  apply (fun p x => (ih x).2 p).
  Defined.

Definition reaction :=
  { ns : (list (N * T) * bool * (N * T)) & Reaction ns.1.1 ns.2 }.

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
apply (existT _ (_, false, _) p.1.1, existT (fun ns => Reaction ns.1.1 ns.2) (_,x.1.2,_) (lift_det _ _ p.1.2), existT (fun ns => Reaction ns.1.1 ns.2) (_, x0.1.2, _) (lift_det _ _ p.2)).
Defined.

Definition reaction_bind (r : reaction) n (b : bool) (k : denomT (tag r).2.2 -> Reaction (tag r).1.1 n) : reaction.
    destruct r; simpl in *.
    econstructor.
    instantiate (1 := (x.1.1, b, n)); simpl.
    eapply rbind.
    apply r.
    apply k.
Defined.

Definition reaction_weak (r : reaction) (n : N * T) : reaction.
destruct r.
econstructor.
instantiate (1 := (n :: x.1.1, x.1.2, x.2)).
simpl.
apply (fun _ => r).
Defined.

Definition reaction_dep (r : reaction) (n : N) := n \in map fst (tag r).1.1.


Definition rlist := list (reaction + N).

  Fixpoint RHiddens (r : rlist) : seq N :=
    match r with
      | nil => nil
      | inr _ :: rs => RHiddens rs
      | inl (existT p _) :: rs =>
        if p.1.2 then RHiddens rs else p.2.1 :: RHiddens rs
                                                       end.

Fixpoint ROutputs (r : rlist) : seq N:=
    match r with
      | nil => nil
      | inr _ :: rs => ROutputs rs
      | inl (existT p _) :: rs =>
        if p.1.2 then p.2.1 :: ROutputs rs else ROutputs rs
                                                       end.

  Fixpoint RInputs (r : rlist) : seq N:=
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
             | inl r => (h \in map fst ((tag r).1.1)) ==> (c \in map fst ((tag r).1.1))
             | inr _ => true end) rs.

  Check @rct.

  Inductive r_rewr : rlist -> rlist -> Prop :=
  | rewr_refl : forall r, r_rewr r r
  | rewr_trans : forall r1 r2 r3, r_rewr r1 r2 -> r_rewr r2 r3 -> r_rewr r1 r3
  | rewr_perm : forall rs rs', Perm rs rs' -> r_rewr rs rs'
  | rewr_r_perm : forall rs r {ns} (H : Perm _ ns), r_rewr (inl r :: rs) (inl (reaction_perm r H) :: rs)
  | rewr_unfold : forall rs r n (k : (denomT (tag r).2.2 -> Reaction (tag r).1.1 n)) (b : bool) ,
      (tag r).2.1 \notin RChans rs ->
      (tag r).1.2 = false ->
      r_rewr (inl (reaction_bind r n b k) :: rs) 
             (inl r :: inl (@rct ((tag r).2 :: (tag r).1.1) _ b k) :: rs)
  | rewr_fold : forall rs (r : reaction) n (k : denomT (tag r).2.2 -> Reaction (tag r).1.1 n) (b : bool) ,
      (tag r).2.1 \notin RChans rs ->
      (tag r).1.2 = false ->
      r_rewr (inl r :: inl (@rct ((tag r).2 :: (tag r).1.1) _ b k) :: rs)
             (inl (reaction_bind r n b k) :: rs) 
  | rewr_subst : forall (rs : rlist) ns b1 b2 h f (r : detReaction ns h) (k : Reaction (h :: ns) f),
      r_rewr (inl (drct b1 r) :: inl (rct b2 k) :: rs)
             (inl (drct b1 r) :: inl (rct b2 (detReaction_subst r k)) :: rs)
  | rewr_str : forall (rs : rlist) ns h f b (k : Reaction ns f),
      h.1 \in RHiddens rs ->
      r_rewr (inl (@rct (h :: ns) _ b (fun _ => k)) :: rs)
             (inl (rct b k) :: rs)
  | rewr_weak : forall n (rs : rlist) (r : reaction) (r' : reaction), 
      n \in (tag r).1.1 ->
      reaction_dep r' (tag r).2.1 ->
      r_rewr (inl r :: inl r' :: rs)
             (inl r :: inl (reaction_weak r' n) :: rs) 
  | rewr_dep : forall (rs : rlist) (r : reaction) (n : N * T),
      (tag r).1.2 = false ->
      use_dominates rs (tag r).2.1 n.1 ->
      r_rewr (inl r :: rs)
             (inl (reaction_weak r n) :: rs)
  | rewr_comp : forall r1 r2 r3, r_rewr r1 r2 -> r_rewr (rlist_comp r1 r3) (rlist_comp r2 r3)
  | rewr_prod : forall n rs (r1 r2 : reaction) (H : (tag r1).1.1 = (tag r2).1.1),
      n \notin RChans rs ->
      let p := reaction_prod r1 r2 n H in
      r_rewr (inl r1 :: inl r2 :: rs) (inl p.1.1 :: inl p.1.2 :: inl p.2 :: rs)
  | rewr_unprod : forall rs (r1 r2 : reaction) n (H : (tag r1).1.1 = (tag r2).1.1),
      n \notin RChans rs ->
      let p := reaction_prod r1 r2 n H in
      r_rewr (inl p.1.1 :: inl p.1.2 :: inl p.2 :: rs) (inl r1 :: inl r2 :: rs).
  End RDef.

Add Parametric Relation (N T : choiceType) `{type T} : (@rlist N T _) (@r_rewr N T _)
    reflexivity proved by (@rewr_refl _ _ _)
    transitivity proved by (@rewr_trans _ _ _) as r_rewr_rel.

Arguments r_rewr [N T H].

Section RLems.
  Context (N T : choiceType) `{type T}.

  Lemma rewr_rot : forall n (rs : rlist N T), r_rewr rs (rot_rcons n rs).
    intros.
    apply rewr_perm.
    apply Perm_rot.
  Qed.

    Lemma lift_det1 (n : N * T) b h (f : denomT n.2 -> denomT h.2) :
      existT (fun (ns : seq (N * T) * bool * (N * T)) => Reaction N T ns.1.1 ns.2) ([:: n], b, h) (fun x => ret (f x)) =
      existT (fun ns => Reaction N T ns.1.1 ns.2) ([:: n], b, h) (lift_det _ _ [:: n] h f).
      done.
    Qed.


    Lemma rewr_subst1 (rs : rlist N T) ns b1 b2 h f (r : detReaction N T ns h) (k : Reaction N T (h :: ns) f):
    r_rewr (inl (existT _ (_, b1, _) (lift_det _ _ _ _ r)) :: inl (existT (fun ns => Reaction N T ns.1.1 ns.2) (_, b2, _) k) :: rs)
           (inl (existT _ (_, b1, _) (lift_det _ _ _ _ r)) :: inl (existT (fun ns => Reaction N T ns.1.1 ns.2) (_, b2, _) (detReaction_subst _ _ r k)) :: rs).
      apply rewr_subst.
    Qed.

End RLems.


