
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

  Definition subst_arg (ns : list (N * T)) (n n' : N) : list (N * T) :=
  map (fun a => if a.1 == n then (n', a.2) else a) ns.

  Definition React_subst_arg {ns f} (r : Reaction ns f) (n n' : N) : Reaction (subst_arg ns n n') f.
  induction ns.
  apply r.
  simpl in *.
  destruct (a.1 == n).
  simpl in *.
  apply (fun x => IHns (r x)).
  apply (fun x => IHns (r x)).
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

Definition reaction_subst_n (r : reaction) (n n' : N) : reaction.
destruct r.
econstructor.
instantiate (1 := (subst_arg x.1.1 n n', x.1.2, x.2)).
simpl in *.
apply React_subst_arg.
apply r.
Defined.

Definition reaction_dep (r : reaction) (n : N) := n \in map fst (tag r).1.1.

Definition rlist := list (reaction + N).

Definition rlist_subst_n (r : rlist) (n n' : N) : rlist :=
  map (fun a => match a with | inr m => inr m | inl r => inl (reaction_subst_n r n n') end) r.

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

    Definition chan_of (x : reaction + N) :=
      match x with
        | inr a => a
        | inl (existT t _) => t.2.1
                                end.

  Definition RChans (r : rlist) : seq N:=
    map chan_of r.

  Definition rlist_nub (r : rlist) :=
    filter (fun p =>
              match p with
                | inl _ => true
                | inr i => i \notin (ROutputs r) end) r.

  Definition rlist_comp (r1 r2 : rlist) := rlist_nub (r1 ++ r2).
  Definition rlist_hide (rs : rlist) (i : N -> bool) : rlist :=
    map (fun r =>
           match r with
           | inl (existT (a, b, c) r) => if i c.1 then inl (existT (fun ns => Reaction ns.1.1 ns.2) (a, false, c) r) else inl (existT (fun ns => Reaction ns.1.1 ns.2) (a, b, c) r) 
           | inr m => inr m end) rs.                                                                                            
  Definition rlist_comp_hide (r1 r2 : rlist) := rlist_hide (rlist_comp r1 r2) (fun n => (n \in RChans r1) && (n \in RChans r2)).

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
      (tag r).2.1 != n.1 ->
      (tag r).1.2 = false ->
      r_rewr (inl (reaction_bind r n b k) :: rs) 
             (inl r :: inl (@rct ((tag r).2 :: (tag r).1.1) _ b k) :: rs)

  | rewr_fold : forall rs (r : reaction) n (k : denomT (tag r).2.2 -> Reaction (tag r).1.1 n) (b : bool) ,
      (tag r).2.1 \notin RChans rs ->
      (tag r).2.1 != n.1 ->
      (tag r).1.2 = false ->
      r_rewr (inl r :: inl (@rct ((tag r).2 :: (tag r).1.1) _ b k) :: rs)
             (inl (reaction_bind r n b k) :: rs) 
  | rewr_subst : forall (rs : rlist) ns b1 b2 h f (r : detReaction ns h) (k : Reaction (h :: ns) f),
      r_rewr (inl (drct b1 r) :: inl (rct b2 k) :: rs)
             (inl (drct b1 r) :: inl (rct b2 (detReaction_subst r k)) :: rs)
  | rewr_str : forall (rs : rlist) (r : reaction) ns b f (k : Reaction ns f),
      (all (fun x => x \in ns) (tag r).1.1) ->
      r_rewr (inl (@rct ((tag r).2 :: ns) _ b (fun _ => k)) :: inl r :: rs)
             (inl (rct b k) :: inl r :: rs)
  | rewr_str_inv : forall (rs : rlist) (r : reaction) ns b f (k : Reaction ns f),
      (tag r).1.2 = false ->
      (all (fun x => x \in ns) (tag r).1.1) ->
      r_rewr (inl (rct b k) :: inl r :: rs)
             (inl (@rct ((tag r).2 :: ns) _ b (fun _ => k)) :: inl r :: rs)
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
      r_rewr (inl p.1.1 :: inl p.1.2 :: inl p.2 :: rs) (inl r1 :: inl r2 :: rs)
  | rewr_remove : forall rs (r : reaction),
      (tag r).1.2 = false ->
      (tag r).2.1 \notin RChans rs ->
      r_rewr (inl r :: rs) rs
  | rewr_add : forall rs (r : reaction),
      (tag r).1.2 = false ->
      (tag r).2.1 \notin RChans rs ->
      r_rewr rs (inl r :: rs) .
  End RDef.

Add Parametric Relation (N T : choiceType) `{type T} : (@rlist N T _) (@r_rewr N T _)
    reflexivity proved by (@rewr_refl _ _ _)
    transitivity proved by (@rewr_trans _ _ _) as r_rewr_rel.

Arguments r_rewr [N T H].

Arguments rct [N T H].
Arguments drct [N T H].
Arguments lift_det [N T H].

Arguments Reaction [N T H].

Notation "G ~> c 'vis' D" := (inl (existT _ (G, true, c) D)) (at level 80).

Notation "G ~> c 'dvis' D" := (inl (existT (fun ns => Reaction ns.1.1 ns.2) (G%SEQ, true, c) (lift_det G c D))) (at level 80).

Notation "G ~> c 'hid' D" := (inl (existT _ (G, false, c) D)) (at level 80).

Notation "G ~> c 'dhid' D" := (inl (existT (fun ns => Reaction ns.1.1 ns.2) (G%SEQ, false, c) (lift_det G c D))) (at level 80).

Section RLems.

  Context (N T : choiceType) `{type T}.



  Lemma rewr_rot : forall n (rs : rlist N T), r_rewr rs (rot_rcons n rs).
    intros.
    apply rewr_perm.
    apply Perm_rot.
  Qed.

    Lemma lift_det0  b h (f : denomT h.2) :
      existT (fun (ns : seq (N * T) * bool * (N * T)) => Reaction ns.1.1 ns.2) (nil, b, h) (ret f) =
      existT (fun (ns : seq (N * T) * bool * (N * T)) => Reaction ns.1.1 ns.2) (nil, b, h) (lift_det nil h f).
      done.
    Qed.

    Lemma lift_det1 (n : N * T) b h (f : denomT n.2 -> denomT h.2) :
      existT (fun (ns : seq (N * T) * bool * (N * T)) => Reaction ns.1.1 ns.2) ([:: n], b, h) (fun x => ret (f x)) =
      existT (fun ns => Reaction ns.1.1 ns.2) ([:: n], b, h) (lift_det  [:: n] h f).
      done.
    Qed.

    Lemma lift_det2 (n n' : N * T) b h (f : denomT n.2 -> denomT n'.2 -> denomT h.2) :
      existT (fun (ns : seq (N * T) * bool * (N * T)) => Reaction ns.1.1 ns.2) ([:: n; n'], b, h) (fun x y => ret (f x y)) =
      existT (fun ns => Reaction ns.1.1 ns.2) ([:: n; n'], b, h) (lift_det  [:: n; n'] h f).
      done.
    Qed.

    Lemma lift_det3 (n n' n'' : N * T) b h (f : denomT n.2 -> denomT n'.2 -> denomT n''.2 -> denomT h.2) :
      existT (fun (ns : seq (N * T) * bool * (N * T)) => Reaction ns.1.1 ns.2) ([:: n; n'; n''], b, h) (fun x y z => ret (f x y z)) =
      existT (fun ns => Reaction ns.1.1 ns.2) ([:: n; n'; n''], b, h) (lift_det  [:: n; n'; n''] h f).
      done.
    Qed.


    Arguments RChans [N T H].
    Arguments ROutputs [N T H].
    Arguments RInputs [N T H].
    Arguments RHiddens [N T H].
    Arguments chan_of [N T H].

    Definition mutual_disjoint3 {A : eqType} (xs ys zs : list A) :=
      forall x, [/\ ~~ ((x \in xs) && (x \in ys)), 
                    ~~ ((x \in ys) && (x \in zs)) &
                    ~~ ((x \in zs) && (x \in xs)) ].

    Definition r_wf (r : rlist N T) := uniq (RChans r).
    Lemma r_wf_cons r x : r_wf (x :: r) = ((chan_of x \notin RChans r) && (r_wf r)).
      rewrite /r_wf.
      destruct x; rewrite //=.
    Qed.

    Lemma skip_subseq {A : eqType} (xs ys : seq A) x :
      subseq (x :: xs) (x :: ys) = subseq xs ys.
      simpl.
      rewrite eq_refl.
      done.
    Qed.

    Lemma RInputs_subseq (r : rlist N T) : subseq (RInputs r) (RChans r).
      apply/subseqP.
      exists (map (fun x => match x with | inl _ => false | inr a => true end) r).
      rewrite /RChans !size_map //=.
      induction r.
      done.
      simpl.
      destruct a.
      done.
      simpl.
      rewrite IHr //=.
    Qed.

    Lemma ROutputs_subseq (r : rlist N T) : subseq (ROutputs r) (RChans r).
      apply/subseqP.
      exists (map (fun x => match x with | inl (existT p _) => p.1.2 | inr a => false end) r).
      rewrite /RChans !size_map //=.
      induction r.
      done.
      simpl.
      destruct a.
      destruct r0.
      destruct (x.1.2).
      simpl.
      rewrite IHr //=.
      done.
      done.
    Qed.

    Lemma RHiddens_subseq (r : rlist N T) : subseq (RHiddens r) (RChans r).
      apply/subseqP.
      exists (map (fun x => match x with | inl (existT p _) => ~~ p.1.2 | inr a => false end) r).
      rewrite /RChans !size_map //=.
      induction r.
      done.
      simpl.
      destruct a.
      destruct r0.
      destruct (x.1.2).
      simpl.
      rewrite IHr //=.
      simpl.
      rewrite IHr //=.
      done.
    Qed.

    Lemma sub_mem_notin {A : eqType} (xs ys : mem_pred A) x  : {subset xs <= ys} -> x \notin ys -> x \notin xs.
      intros.
      remember (x \in xs) as h; destruct h; symmetry in Heqh.
      apply H0 in Heqh.
      rewrite Heqh in H1.
      done.
      done.
    Qed.

    Definition r_compat (r1 r2 : rlist N T) :=
      forall x, (x \in RChans r1) && (x \in RChans r2) ->
                                                        [|| ((x \in RInputs r1) && (x \in ROutputs r2)) |
                                                         ((x \in RInputs r2) && (x \in ROutputs r1))]. 

    Lemma chan_of_reaction_perm (r : reaction N T) {ns} (HP : Perm (tag r).1.1 ns) :
      chan_of (inl (reaction_perm N T r HP)) = chan_of (inl r).
      rewrite /reaction_perm.
      destruct r.
      done.
    Qed.

    Lemma chan_of_reaction_bind (r : reaction N T) n b k :
      chan_of (inl (reaction_bind _ _ r n b k)) = n.1.
      rewrite /reaction_bind.
      destruct r; done.
    Qed.


    Lemma chan_of_reaction_weak (r : reaction N T) n:
      chan_of (inl (reaction_weak _ _ r n)) = chan_of (inl r).
      rewrite /reaction_weak; destruct r; done.
    Qed.

    Lemma RChans_perm_mem (r : rlist N T) r' : Perm r r' -> RChans r =i RChans r'.
      intro X; induction X.
      done.
      simpl.
      destruct x.
      destruct r.
      move => z; rewrite !in_cons IHX //=.
      move => z; rewrite !in_cons IHX //=.
      simpl.
      destruct y.
      destruct r.
      destruct x.
      destruct r0.
      move => z; rewrite !in_cons. 
      simpl.
      destruct (z == x0.2.1); destruct (z == x.2.1); destruct (z \in RChans l); done.
      move => z; rewrite !in_cons //=. 
      destruct (z == x0.2.1); destruct (z == s); destruct (z \in RChans l); done.
      destruct x.
      destruct r.
      move => z; rewrite !in_cons //=.  
      destruct (z == x.2.1); destruct (z == s); destruct (z \in RChans l); done.
      move => z; rewrite !in_cons //=. 
      destruct (z == s0); destruct (z == s); destruct (z \in RChans l); done.
      move => z; rewrite -IHX2; done.
    Qed.

    Ltac destructb tm :=
      let x := fresh "b" in
      let h := fresh "Hb" in
      remember tm as x eqn:h; rewrite -?h;
      destruct x.


    Lemma Perm_wf (r : rlist N T) r' : Perm r r' -> r_wf r = r_wf r'.
      intro X; induction X.
      done.
      rewrite !r_wf_cons IHX.
      rewrite (RChans_perm_mem _ _ X).
      bool_congr.
      rewrite !r_wf_cons //=.
      rewrite !in_cons !negb_or.
      rewrite eq_sym.
      destructb (chan_of x != chan_of y); destructb (chan_of y \in RChans l); destructb (chan_of x \in RChans l); done.
      rewrite -IHX2 //=.
    Qed.

    Lemma trythis (r : rlist N T) r' :
      r_wf r -> r_rewr r r' -> r_wf r'.
      intros.
      move: H0.
      induction H1.
      done.
      intro; apply IHr_rewr2.
      apply IHr_rewr1.
      done.
      intros; rewrite -(Perm_wf _ _ X) //=.
      rewrite !r_wf_cons.
      rewrite chan_of_reaction_perm.
      done.
      intro.
      rewrite !r_wf_cons !in_cons //=.
      destruct r.
      simpl in *.
      rewrite (negbTE H0) orbF.
      rewrite r_wf_cons //= in H3.
      rewrite H1 //=.
      intro.
      rewrite r_wf_cons chan_of_reaction_bind.
      rewrite !r_wf_cons //= in H3.
      destruct r; simpl in *.
      move/and3P: H3; elim => [h1 h2 h3].
      rewrite h2 h3 //=.
      rewrite !r_wf_cons //.
      rewrite !r_wf_cons //.
      rewrite !r_wf_cons //.
      rewrite !r_wf_cons.
      rewrite /RChans.
      rewrite !map_cons.
      rewrite !chan_of_reaction_weak.
      done.
      rewrite !r_wf_cons chan_of_reaction_weak //=.
      admit. (* comp *)
      rewrite !r_wf_cons.
      rewrite /p //=.
      admit.
      admit.
      rewrite r_wf_cons; move/andP; elim; done.
      intro; rewrite r_wf_cons H2 andbT.
      destruct r; simpl in *.
      done.
   Admitted.
End RLems.


Notation "x1 ~~> x2" := (r_rewr x1 x2) (at level 40).

    Ltac r_swap from to := etransitivity; [apply rewr_perm; apply (Perm_swap from to) | idtac]; rewrite /swap /=.

    Ltac rct_swap from to := etransitivity; [apply (rewr_r_perm _ _ _ _ (Perm_swap from to _)) | idtac]; rewrite /swap /=.

    Ltac r_prod n := rewrite (rewr_prod _ _ n); [instantiate (1 := erefl) | done]; simpl.

    Ltac r_at n t := r_swap n 0%N; t; r_swap n 0%N.

    Ltac r_weak n t := rewrite (rewr_weak _ _ (n, t)); [idtac | done | done]; rewrite /=.

    Ltac r_subst := rewrite rewr_subst; rewrite /rct /drct /=.

    Ltac r_str := rewrite rewr_str /rct /=; [idtac | done].

    Lemma r_rewr_r {N} {T : choiceType} `{type T} (r1 r2 r3 : rlist N T) : r2 ~~> r3 -> r1 ~~> r2 -> r1 ~~> r3.
      intro ; etransitivity.
      apply H1.
      done.

    
     Qed.