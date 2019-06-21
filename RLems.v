

From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
From mathcomp Require Import fingroup finset. 
From mathcomp Require Import cyclic zmodp.

Require Import Posrat Premeas Meas Aux SeqOps Logic Tacs.

Section Theory.

  Context (N T : choiceType) `{type T}.

  SearchAbout List.nth_error.

  Lemma rewr_rot : forall n (rs : rlist N T), r_rewr rs (rot_rcons n rs).
    intros.
    apply rewr_bi_r.
    apply rewr_perm.
    apply Perm_rot.
  Qed.

  Fixpoint RChans_wf (rs : rlist N T) :=
    match rs with
    | nil => true
    | (r :: rs) => all (fun x => x \in RSeqs _ _ rs) (RArgs _ _ [:: r]) && RChans_wf rs
                       end.

  Lemma RSeqs_remove (rs : rlist N T) i :
    RSeqs _ _ (remove rs i) = remove (RSeqs _ _ rs) i.
    move: rs.
    induction i.
    induction rs; done.
    induction rs.
    done.
    simpl.
    rewrite IHi //=.
  Qed.

  Lemma RSeqs_insert (rs : rlist N T) i x :
    RSeqs _ _ (insert rs i x) = insert (RSeqs _ _ rs) i (chan_of x).
    move: rs; induction i; induction rs.
    done.
    done.
    done.
    simpl.
    rewrite IHi //=.
 Qed.

  Lemma size_RSeqs (rs : rlist N T) :
    size (RSeqs _ _ rs) = size rs.
    induction rs; rewrite //=.
    rewrite IHrs //=.
  Qed.

  Lemma RSeqs_lset (rs : rlist N T) i r :
    RSeqs _ _ (lset rs i r) = lset (RSeqs _ _ rs) i (chan_of r).
    move: rs; induction i; induction rs.
    rewrite /lset //=.
    simpl.
    rewrite /lset //=.
    rewrite RSeqs_insert //=.
    done.
    simpl.
    rewrite /lset //=.
    rewrite !ltSnSn.
    rewrite size_RSeqs.
    destruct (i < size rs).
    simpl.
    rewrite RSeqs_insert //=.
    rewrite RSeqs_remove //=.
    done.
  Qed.


  Lemma RChans_wfP (rs : rlist N T) :
    RChans_wf rs ->
    RChans rs =i RSeqs _ _ rs.
    induction rs.
    done.
    simpl.
    move/andP; elim => h1 h2.
    rewrite /RChans //=.
    destruct a.
    destruct r.
    simpl in *.
    rewrite /RArgs //= in h1.
    move => z.
    rewrite in_cons mem_cat /RArgs //=.
    rewrite !in_cons.
    case (eqVneq z x.2.1).
    move => ->.
    rewrite eq_refl //=.
    intro hneq.
    rewrite (negbTE hneq) //=.
    rewrite mem_cat.
    remember (z \in [seq i.1 | i <- x.1.1]) as b; symmetry in Heqb; rewrite Heqb; destruct b.
    simpl.
    rewrite orbT //=.
    move: (allP h1 z).
    rewrite cats0 Heqb; move/(_ is_true_true) => -> //=.
    simpl.
    rewrite -{2}IHrs.
    rewrite /RChans /RArgs mem_cat //=.
    done.
    simpl.
    move => a.
    rewrite !in_cons.
    case (eqVneq a p.1).
    move => -> //= ; rewrite eq_refl //=.
    move => hc; rewrite (negbTE hc) //= -IHrs /RChans //=.
  Qed.
      
    


  Lemma RChans_eqP (i : nat) (rs rs' : rlist N T) :
    RChans_wf rs ->
    RChans_wf rs' ->
    size rs = i ->
    size rs' = i ->
    (forall n c, List.nth_error rs n = Some c -> exists c', List.nth_error rs' n = Some c' /\ chan_of c = chan_of c') ->
    RChans rs =i RChans rs'.
    move: rs rs'; induction i.
    move => rs rs'.
    move => _ _.
    move/size0nil => ->.
    move/size0nil => ->.
    done.
    move => rs rs' Hrs Hrs'.
    destruct rs as [| r rs].
    done.
    destruct rs' as [| r' rs'].
    done.
    simpl.
    move/eqP; rewrite /eq_op //=; move/eqP => h1.
    move/eqP; rewrite /eq_op //=; move/eqP => h2.
    intros.
    move => a.
    rewrite !RChans_wfP //=.
    have: chan_of r = chan_of r'.
    move: (H0 0 r).
    move/(_ erefl).
    elim => r''.
    simpl.
    elim.
    inj.
    done.
    move => ->.
    rewrite !in_cons.
    rewrite -!RChans_wfP //=.
    erewrite IHi.
    apply: erefl.
    move/andP: Hrs; elim; done.
    move/andP: Hrs'; elim; done.
    done.
    done.
    intros.
    move: (H0 (S n) c).
    simpl.
    move/(_ H1).
    done.
    move/andP: Hrs'; elim; done.
    move/andP: Hrs; elim; done.
Qed.

  Lemma notin_removeP {A : eqType} (xs : seq A) i x :
    x \notin xs -> x \notin (remove xs i).
    move: xs; induction i; induction xs.
    done.
    simpl.
    rewrite in_cons negb_or; move/andP; elim; done.
    done.
    simpl.
    rewrite !in_cons !negb_or; move/andP; elim => h1 h2.
    rewrite IHi //=.
    rewrite h1 //=.
  Qed.

  Lemma notin_insert {A : eqType} (xs : seq A) i x y :
    y \notin xs -> y != x -> y \notin (insert xs i x).
    move: xs; induction i; induction xs.
    simpl.
    rewrite mem_seq1 //=.
    simpl.
    rewrite in_cons negb_or; move/andP; elim => h1 h2 h3.
    rewrite !in_cons.
    rewrite (negbTE h1) (negbTE h2) (negbTE h3) //=.
    simpl.
    rewrite mem_seq1 //=.
    simpl.
    rewrite !in_cons !negb_or; move/andP; elim => h1 h2 h3; apply/andP; split.
    done.
    apply IHi; done.
  Qed.

  Lemma notin_lset {A : eqType} (xs : seq A) i x y :
    y \notin xs -> y != x -> y \notin (lset xs i x).
    intros.
    rewrite /lset.
    destruct (i < size xs).
    apply notin_insert.
    apply notin_removeP; done.
    done.
    done.
 Qed.

Lemma rewr_add_ch_fold : forall (rs : rlist N T) (G1 G2 : seq (N * T)) (h : N * T) (r : Reaction G1 h) (n : N * T) (k : denomT h.2 -> Reaction (G1 ++ G2) n) m b,
      h.1 \notin RChans rs ->
      h.1 != n.1 ->
      m \in G2 ->
      r_rewr_bi
        [:: G1 ~> h hid r,
           inl (existT (fun ns => Reaction ns.1.1 ns.2) (h :: G1 ++ G2, b, n) k) & rs ]
        [:: (m :: G1) ~> h hid (fun _ => r),
           inl (existT (fun ns => Reaction ns.1.1 ns.2) (h :: G1 ++ G2, b, n) k) & rs].
  intros.


  eapply rewr_bi_trans.
  apply rewr_bi_sym.
  apply: rewr_fold; done.

  eapply rewr_bi_trans.
  Check rewr_add_ch.
  apply: (rewr_add_ch _ _ _ 0 m).
  apply: erefl.
  rewrite mem_cat H2 //= orbT //=.
  
  rewrite /lset //=.
  rewrite insert_0.

  have -> :
    (existT (fun ns : seq (N * T) * bool * (N * T) => Reaction ns.1.1 ns.2) 
            (m :: G1 ++ G2, b, n) (fun _ : denomT m.2 => rbind G1 G2 h n r k)) =
    (existT (fun ns : seq (N * T) * bool * (N * T) => Reaction ns.1.1 ns.2) 
          ((m :: G1) ++ G2, b, n) (rbind (m :: G1) G2 h n (fun _ => r) (fun m _ => k m))).
  unlock rbind; done.

  eapply rewr_bi_trans.
  apply rewr_fold; done.

  eapply rewr_bi_trans.
  apply rewr_perm; apply perm_swap.
  simpl.

  eapply rewr_bi_trans.
  Check rewr_r_perm.
  apply: (rewr_r_perm 0 _ _ (Perm_swap 1 0 _)).
  simpl.
  apply: erefl.
  rewrite /lset //=.


  eapply rewr_bi_trans.
  r_ext_at leftc 0 (fun (_ : denomT m.2) => k).
  clear.

      move: G2 h n k.
      induction G1.
      simpl.
      induction G2.
      done.
      simpl.
      intros.
      eapply IHG2.
      apply x.
      simpl.
      intros.
      eapply IHG1.
      done.

  rewrite /lset /=.

  rewrite /swap /=.
  Check rewr_add_ch_rev.
  apply: (rewr_add_ch_rev _ _ _ 0 m).
  done.
  apply: erefl.
  rewrite in_cons mem_cat H2 !orbT //=.
  rewrite /lset //=.
  r_move_at leftc 0 1.
  reflexivity.
Qed.

  (*

  Lemma fold_bind00 : forall (rs : rlist N T) (h : N * T) (m : meas (denomT h.2)) (n : N * T) (k : denomT h.2 -> meas (denomT n.2)) (b : bool) ,
      h.1 \notin RChans rs ->
      h.1 != n.1 ->
      r_rewr [:: nil ~> h hid m, inl (existT (fun ns => Reaction ns.1.1 ns.2) (h :: nil, b, n) k) & rs]
             ((inl (existT (fun ns => Reaction ns.1.1 ns.2) (nil, b, n) (x <- m; k x))) :: rs).
    intros.
    etransitivity.
    apply rewr_bi_l.
    apply: rewr_fold.
    done.
    done.
    simpl; reflexivity.
  Qed.

  Lemma fold_bind01 : forall (rs : rlist N T) (h : N * T) (m : meas (denomT h.2)) (y : (N * T)) (n : N * T) (k : denomT h.2 -> denomT y.2 -> meas (denomT n.2)) (b : bool) ,
      h.1 \notin RChans rs ->
      h.1 != n.1 ->
      r_rewr [:: nil ~> h hid m, inl (existT (fun ns => Reaction ns.1.1 ns.2) (h :: y :: nil, b, n) k) & rs]
             ((inl (existT (fun ns => Reaction ns.1.1 ns.2) (y :: nil, b, n) (fun y => x <- m; k x y))) :: rs).
  intros.
  etransitivity.
  apply rewr_bi_l.
  apply: rewr_fold.
  done.
  done.
  simpl.
  reflexivity.
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
      (*
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
*)
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

Arguments r_wf [N T H].

*)
    End Theory.