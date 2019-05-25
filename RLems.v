

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
From mathcomp Require Import fingroup finset. 
From mathcomp Require Import cyclic zmodp.

Require Import Posrat Premeas Meas Aux Reaction finfun_fixed String SSRString SeqOps.



Section Theory.

  Context (N T : choiceType) `{type T}.

  Lemma rewr_rot : forall n (rs : rlist N T), r_rewr rs (rot_rcons n rs).
    intros.
    apply rewr_perm.
    apply Perm_rot.
  Qed.

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
      rewrite r_wf_cons //=.
      (*
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
*)
   Admitted.
    End Theory.

Arguments r_wf [N T H].