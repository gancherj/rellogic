

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

  Definition RChans_defined (rs : rlist N T) :=
    all (fun r => all (fun x => x \in RSeqs _ _ rs) (RArgs _ _ [:: r])) rs.

  Definition R_wf (rs : rlist N T) :=
    uniq (RSeqs _ _ rs) && RChans_defined rs. 

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




  rewrite /swap /=.
  r_ext_at leftc 0 (fun (_ : denomT m.2) => k).
  clear.
      simpl.
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
  etransitivity.
  apply: (rewr_add_ch_rev _ _ _ 0 m).
  done.
  apply: erefl.
  rewrite in_cons mem_cat H2 !orbT //=.
  rewrite /lset //=.

  r_move_at leftc 0 1.
  reflexivity.
Qed.

    End Theory.