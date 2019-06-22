
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat .
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap tuple.

Require Import Premeas Meas Posrat Aux finfun_fixed SeqOps Logic.
Require List.


Ltac list_in :=
  match goal with
    | [ |- @List.In _ ?x nil] => fail "not found"
    | [ |- @List.In _ ?x (?x :: ?xs)] => left; done
    | [ |- @List.In _ ?x (?y :: ?xs)] => right; list_in
                                                  end.



Add Parametric Relation (N T : choiceType) `{type T} : (@rlist N T _) (@r_rewr N T _)
    reflexivity proved by (@rewr_refl _ _ _)
    transitivity proved by (@rewr_trans _ _ _) as r_rewr_rel.

Add Parametric Relation (N T : choiceType) `{type T} : (@rlist N T _) (@r_rewr_bi N T _)
    reflexivity proved by (@rewr_bi_refl _ _ _)
    symmetry proved by (@rewr_bi_sym _ _ _)
    transitivity proved by (@rewr_bi_trans _ _ _) as r_rewr_bi_rel.

Arguments r_rewr [N T H].
Arguments r_rewr_bi [N T H].
Arguments rct [N T H].
Arguments drct [N T H].
Arguments rbind [N T H ].
Arguments lift_det [N T H].
Arguments Reaction [N T H].
Arguments RChans [N T H].
Arguments ROutputs [N T H].
Arguments RInputs [N T H].
Arguments RHiddens [N T H].
Arguments chan_of [N T H].

Notation "x1 ~~> x2" := (r_rewr x1 x2) (at level 40).
Notation "x1 <~~> x2" := (r_rewr_bi x1 x2) (at level 40).



Notation "G ~> c 'vis' D" := (inl (existT (fun ns => Reaction ns.1.1 ns.2) (G, true, c) D)) (at level 80).

Notation "G ~> c 'hid' D" := (inl (existT (fun ns => Reaction ns.1.1 ns.2) (G, false, c) D)) (at level 80).

Notation "G ~> c 'dvis' D" := (inl (existT (fun ns => Reaction ns.1.1 ns.2) (G%SEQ, true, c) (lift_det G c D))) (at level 80).


Notation "G ~> c 'dhid' D" := (inl (existT (fun ns => Reaction ns.1.1 ns.2) (G%SEQ, false, c) (lift_det G c D))) (at level 80).


Notation "x ||| y" := (rlist_comp_hide _ _ x y) (at level 40).
Notation "x |||v y" := (rlist_comp _ _ x y) (at level 40).

(* General Tactics *)

Ltac Tac_iter xs k :=
  match xs with
    | nil => idtac
    | (?x :: ?xs') => (k x); Tac_iter xs' k
                                      end.

Ltac hd xs :=
  match xs with
    | nil => fail "no head of nil"
    | (?x :: ?xs) => x
                       end.

Ltac tail xs :=
  match xs with
    | nil => nil
    | (?x :: ?xs) => xs
                       end.

Close Scope posrat_scope.
Open Scope nat_scope.

Section Lems.
  Context {N T : choiceType} `{type T}.

    Local Notation "G ~> c b D" := (inl (existT (fun ns => Reaction ns.1.1 ns.2) (G, b, c) D)) (at level 80, c at level 9, b at level 9).

   Lemma rewr_r_r (rs rs' rs'' : rlist N T) :
     rs' <~~> rs'' -> rs ~~> rs' -> rs ~~> rs''.
     intros; etransitivity.
     apply H1.
     apply rewr_bi_r.
     apply H0.
   Qed.
      
   Lemma rewr_r_l (rs rs' rs'' : rlist N T) :
     rs' <~~> rs'' -> rs ~~> rs'' -> rs ~~> rs'.
     intros; etransitivity.
     apply H1.
     apply rewr_bi_l.
     apply H0.
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

    Lemma lift_bind (n : N) t f (m : meas (denomT t)) (k : denomT t -> meas (denomT f.2)) :
      @React_eq _ _ _ nil f (mbind m k) (rbind nil nil (n,t) f m k).
      unlock rbind.
      rewrite /rbind //=.
    Qed.

    Lemma lift_bind1 (p : N * T) (n : N) t f (m : denomT p.2 -> meas (denomT t)) (k : denomT p.2 -> denomT t -> meas (denomT f.2)) :
      @React_eq _ _ _ [:: p] f (fun x => mbind (m x) (k x))
                               (rbind [:: p] nil (n,t) f m (fun n2 p2 => k p2 n2)).
      unlock rbind.
      rewrite /rbind //=.
    Qed.

    Lemma lift_bind2 (p1 p2 : N * T) (n : N) t f (m : denomT p1.2 -> denomT p2.2 -> meas (denomT t)) (k : denomT p1.2 -> denomT p2.2 -> denomT t -> meas (denomT f.2)) :
      @React_eq _ _ _ [:: p1; p2] f (fun x y => mbind (m x y) (k x y))
                               (rbind [:: p1; p2] nil (n,t) f m (fun n2 p1 p2 => k p1 p2 n2)).
      unlock rbind.
      rewrite /rbind //=.
    Qed.

    (* **** reverse lemmas **** *)

    Lemma rewr_add_ch_rev (rs : rlist N T) b g f (r : Reaction g f) n (c : N * T):
      n < size rs ->
      List.nth_error rs n = Some ((c :: g) ~> f b (fun _ => r)) ->
      c \in g ->
      rs <~~> lset rs n (g ~> f b r).
      intros.
      symmetry.
      have heq: rs = lset (lset rs n (g ~> f b r)) n (c :: g ~> f b (fun _ => r)).
        rewrite lset_lset //=; apply lset_nth_error; done.
      rewrite {2}heq.
      apply rewr_add_ch.
      rewrite nth_error_lset.
      rewrite eq_refl.
      done.
      done.
      done.
    Qed.
    (* rewr_fold_rev *)

    Lemma ltn_pred n m :
      (n < m.-1) = (n.+1 < m).
      move: n; induction m.
      simpl.
      done.
      simpl.
      intro.
      rewrite ltSnSn //=.
    Qed.

    Lemma rewr_subst_rev (rs : rlist N T) pos1 pos2 ns ns' b1 b2 h f (r : detReaction N T ns h) k :
      pos2 != pos1 ->
      pos2 < size rs ->
      List.nth_error rs pos1 = Some (ns ~> h b1 (lift_det ns h r)) ->
      List.nth_error rs pos2 = Some (h :: ns ++ ns' ~> f b2 (detReaction_subst N T r k)) ->
      rs <~~> lset rs pos2 (h :: ns ++ ns' ~> f b2 k).
      intros; symmetry.
      have h1: rs = lset (lset rs pos2 (h :: ns ++ ns' ~> f b2 k)) pos2 (h :: ns ++ ns' ~> f b2 (detReaction_subst N T r k)).
        rewrite lset_lset.
        apply lset_nth_error.
        done.
        done.
        done.
      rewrite {2}h1.
      apply: rewr_subst.
      instantiate (2 := pos1).
      rewrite nth_error_lset.
      rewrite (negbTE H0).
      apply H2.
      done.
      rewrite nth_error_lset.
      rewrite eq_refl //=.
      done.
      Qed.

    Check rewr_ch_trans.

    Lemma rewr_ch_trans_rev (rs : rlist N T) pos1 pos2 n g1 g2 f1 f2 (d : Reaction g1 f1) (d' : Reaction g2 f2) b1 b2 :
      pos2 < size rs ->
      pos2 != pos1 ->
      List.nth_error rs pos1 = Some (g1 ~> f1 b1 d) ->
      List.nth_error rs pos2 = Some (n :: g2 ~> f2 b2 (fun _ => d')) ->
      n \in g1 -> f1 \in g2 ->
      rs <~~> lset rs pos2 (g2 ~> f2 b2 d').
      intros.
      symmetry.
      have heq: rs = lset (lset rs pos2 (g2 ~> f2 b2 d')) pos2 (n :: g2 ~> f2 b2 (fun _ => d')).
        rewrite lset_lset.
        rewrite -lset_nth_error.
        done.
        done.
        apply H3.
        done.
      rewrite {2}heq.
      apply: (rewr_ch_trans _ _ _ pos1 pos2).
      rewrite nth_error_lset.
      rewrite (negbTE H1).
      apply H2.
      done.
      rewrite nth_error_lset.
      rewrite eq_refl.
      done.
      done.
      done.
      done.
  Qed.

    Check rewr_hid_ws.

    Lemma rewr_hid_ws_rev (rs : rlist N T) pos1 pos2 g1 g2 h d c (d' : Reaction g2 c) b :
      pos2 != pos1 ->
      pos2 < size rs ->
      List.nth_error rs pos1 = Some (g1 ~> h false d) ->
      List.nth_error rs pos2 = Some (h :: g2 ~> c b (fun _ => d')) ->
      all (fun x => x \in g2) g1 ->
      rs <~~> lset rs pos2 (g2 ~> c b d').
      intros; symmetry.
      have h1 : rs = lset (lset rs pos2 (g2 ~> c b d')) pos2 (h :: g2 ~> c b (fun _ => d')).
        rewrite lset_lset.
        apply lset_nth_error.
        done.
        apply H3.
        done.
      rewrite {2}h1.
      apply: rewr_hid_ws.
      rewrite nth_error_lset.
      instantiate (3 := pos1).
      rewrite (negbTE H0).
      apply H2.
      done.
      rewrite nth_error_lset.
      rewrite eq_refl //=.
      done.
      done.
    Qed.

    Check rewr_addrem.

    Lemma rewr_addrem_rev (rs : rlist N T) h g1 (r : Reaction g1 h) pos:
    pos < size rs ->
    all (fun x => x \in RChans rs) (map fst g1) ->
    h.1 \notin RChans rs ->
    rs <~~> insert rs pos (g1 ~> h false r).
      intros; symmetry.
      Check rewr_addrem.
      have heq: rs = remove (insert rs pos (g1 ~> h false r)) pos.
        rewrite remove_insert //=.
      rewrite {2}heq.
      apply: rewr_addrem.
      rewrite nth_error_insert_same.
      apply: erefl.
      slia.
      apply/allP => x Hx.
      rewrite remove_insert.
      apply (allP H1); done.
      done.
      rewrite remove_insert.
      done.
      done.
   Qed.

    Check rewr_fold.

    Lemma rewr_fold_rev (rs : rlist N T) g1 g2 h (r : Reaction g1 h) n (k : denomT h.2 -> Reaction (g1 ++ g2) n) b :
      h.1 \notin RChans rs ->
      h.1 != n.1 ->
      [:: g1 ~> h false r, h :: g1 ++ g2 ~> n b k & rs]
        <~~>
        ((g1 ++ g2 ~> n b rbind g1 g2 h n r k) :: rs).
      intros; symmetry; apply: rewr_fold; done.
    Qed.

End Lems.

(*  **** STRUCTURAL TACTICS **** *)
Definition leftc := false.
Definition rightc := true.

Ltac get_rs_at x :=
  match x with
  | leftc =>
    match goal with
    | [ |- @r_rewr _ _ _ ?rs _] => rs
    | [ |- @r_rewr_bi _ _ _ ?rs _] => rs
    end
  | rightc =>
    match goal with
    | [ |- @r_rewr _ _ _ _ ?rs ] => rs
    | [ |- @r_rewr_bi _ _ _ _ ?rs ] => rs
    end
      end
.


  (* n may be either a nat or a name; if a nat, just return the nat; if something else, find the index of the reaction with the corresponding name *)
  Ltac pos_of_at a n :=
    match (type of n) with
    | nat => n
    | _ =>
      let rs := get_rs_at a in
      let i := eval compute in (ofind rs (fun m => chan_of m == n)) in
        match i with
            | Some ?a => a
            | None => fail "sequent not found: " n
                            end 
             end.

Ltac get_tag_at_rec n rs :=
  match n with
  | 0%N => match rs with
           | (inl (@existT _ _ ?p _) :: _) => p
                                                end
  | S ?n' =>
    match rs with
    | (_ :: ?rs') => get_tag_at_rec n' rs'
    end
  end.
      
  
Ltac get_tag_at a x :=
  let n := pos_of_at a x in
  let rs := get_rs_at a in
  get_tag_at_rec n rs.

Ltac get_dist_at_rec n rs :=
  match n with
  | 0%N => match rs with
           | (inl (@existT _ _ _ ?D) :: _) => D
           end
  | S ?n' =>
    match rs with
    | (_ :: ?rs') => get_dist_at_rec n' rs'
    end
  end.

Ltac get_dist_at a x :=
  let n := pos_of_at a x in
  let rs := get_rs_at a in
  get_dist_at_rec n rs.

      
Ltac get_args_at a n :=
  let p := get_tag_at a n in
  match p with
  | (?ns, _, _) => ns
                end.

Ltac get_bool_at a n :=
  let p := get_tag_at a n in
  match p with
  | (_, ?b, _) => b
                end.


Ltac get_val_at a n :=
  let p := get_tag_at a n in
  match p with
  | (_, _, ?v) => v
                end.


  (* n may be either a nat or a name; if a nat, return the nat; if something else, find the index of the argument that matches the name in the first reaction *)
  Ltac arg_idx_of_at a y n :=
    match (type of n) with
    | nat => n
    | _ =>
      let args := get_args_at a y in
      let i := eval compute in (ofind args (fun p => p.1 == n)) in
            match i with
                | Some ?a => a
                | None => fail "argument not found: " n
                                end
             end.

  Ltac ensure_bi_r :=
    match goal with
      | [ |- @r_rewr _ _ _ _ _ ] => apply rewr_bi_r
      | _ => idtac
               end.

  Ltac ensure_not_bi :=
    match goal with
      | [ |- @r_rewr_bi _ _ _ _ _ ] => fail "Tactic not supported in bidirectional mode."
      | _ => idtac end.

  Ltac apply_bi_at a t :=
    match a with
    | leftc =>
      etransitivity; [ensure_bi_r; t | ]
    | rightc =>
      etransitivity; [ | ensure_bi_r; symmetry; t]
                 end.

(* REWRITING TACTICS *)

  (* move 'from' to 'to' *)
  Ltac r_move_at a from to :=
   let i := pos_of_at a from in 
   let j := pos_of_at a to in
   apply_bi_at a ltac:(apply rewr_perm; apply (Perm_swap_irrel i j)); rewrite /swap /=.

  Ltac r_move from to := r_move_at leftc from to.
  Ltac r_move_r from to := r_move_at rightc from to.

  Ltac ensure_val_at a x n :=
    let v := get_val_at a x in
    match v with
      | (n, _) => idtac 
      | _ => r_move_at a x n
                       end.

  (* add/remove duplicate channels *)

  Arguments rewr_add_ch [N T H rs b].
  Arguments rewr_add_ch_rev [N T H rs b].
  (* a = leftc or rightc
     pos = name /idx of sequent to be manipulated
     n, ty : channel to add *)
  Ltac add_ch_at a pos n ty :=
    let i := pos_of_at a pos in
    let g := get_args_at a i in
    apply_bi_at a ltac:(eapply (rewr_add_ch g _ _ i (n, ty)); done); simpl.

  (* a = leftc or rightc
     pos = name/idx of sequent to be manipulated

     channel to remove must be first! *)
  Ltac rem_ch_at a pos :=
    let i := pos_of_at a pos in
    let c_g := get_args_at a i in
    let c := hd c_g in
    let g := tail c_g in
    apply_bi_at a ltac:(apply: (rewr_add_ch_rev g _ _ i c); [done | apply : erefl | done]); simpl.

  (*

  Ltac arg_move n from to := arg_move_at leftc n from to.
  Ltac arg_move_r n from to := arg_move_at rightc n from to.

  Ltac arg_focus n x := arg_move n x 0%N.
  Ltac arg_focus_r n x := arg_move_r n x 0%N.
*)

  Check rewr_r_perm.
  Arguments rewr_r_perm [N T H rs].
  Ltac arg_move_at a n from to :=
    let ai := pos_of_at a n in
    let i := arg_idx_of_at a n from in
    let j := arg_idx_of_at a n to in
    apply_bi_at a ltac:(apply: (rewr_r_perm ai _ _ (Perm_swap i j _)); apply : erefl); rewrite /swap /lset /=.


  Arguments rewr_ext [N T H rs].
  Check rewr_ext.
  Ltac r_ext_at a m tm :=
    let i := pos_of_at a m in
    apply_bi_at a ltac:(apply: (rewr_ext i); [ apply: erefl | instantiate (1 := tm) ]); unfold lset; simpl.

  Check lift_bind.
  Check lift_bind1.
  Ltac unfold_bind0_at a n midn midty :=
    let i := pos_of_at a n in
    apply_bi_at a ltac:(apply: (rewr_ext i); [apply : erefl | apply: (lift_bind midn midty)]); rewrite /lset //=.


  Ltac unfold_bind1_at a n midn midty :=
    let i := pos_of_at a n in
    apply_bi_at a ltac:(apply: (rewr_ext i); [apply : erefl | apply: (lift_bind1 _ midn midty)]); rewrite /lset //=.

  Ltac unfold_bind2_at a n midn midty :=
    let i := pos_of_at a n in
    apply_bi_at a ltac:(apply: (rewr_ext i); [apply : erefl | apply: (lift_bind2 _ _ midn midty)]); rewrite /lset //=.


  Check rewr_fold.
    Arguments rewr_fold [N T H rs].

    (* requires the sampling sequence is first, the sequence that uses the sampling is second, and the arguments of the second sequence is lined up with the sampling sequent ( with the first arg being the sampled value) *)
    Ltac fold_at a :=
      apply_bi_at a ltac:(apply: rewr_fold_rev; [done | done]); unlock rbind; simpl.

    (* g0 = first half of partition of context *)
  Ltac unfold_at_with a g0 :=
    apply_bi_at a ltac:(apply: (rewr_fold g0); [done | done ]); unfold lset_seq; simpl.

  (* unfold an rbind at n1, place at n1 *)
  Ltac unfold_at a n :=
    r_move_at a n 0%N;
    let d := get_dist_at a 0%N in
    match d with
    | rbind ?g _ _ _ _ _ => unfold_at_with a g
                                           end.
    Arguments rewr_pair [N T H rs].

  (* p is a name. needs to be fresh *)
  Ltac pair_at a n0 n1 p :=
    let i := pos_of_at a n0 in
    let j := pos_of_at a n1 in
    apply_bi_at a ltac:(apply: (rewr_pair i j p); [apply: erefl | apply : erefl | done | done]); unfold eq_rect_r; simpl; unfold eq_rect_r; unfold remove2; simpl.

    Arguments rewr_subst [N T H rs].

    (* substitute n0 in n1. note that the arguments of n1 MUST be n0 :: args of n0 *)
    Ltac subst_at a n0 n1 :=
      let i := pos_of_at a n0 in
      let j := pos_of_at a n1 in
      apply_bi_at a ltac:(apply: (rewr_subst i j); [apply: erefl | apply: erefl]); rewrite /lset /=.

    Arguments rewr_hid_ws [N T H rs].

    (* add n0 to n1 *)
    Ltac hid_weak_at a n0 n1 :=
      let i := pos_of_at a n0 in
      let j := pos_of_at a n1 in
      apply_bi_at a ltac:(apply: (rewr_hid_ws i j); [apply: erefl | apply: erefl| done]); rewrite /lset /=.
      
    (* remove n0 from n1 *)
    Ltac hid_str_at a n0 n1 :=
      arg_move_at a n1 n0 0; (* n0 must be at head of arguments to n1 *)
      let i := pos_of_at a n0 in
      let j := pos_of_at a n1 in
      apply_bi_at a ltac:(apply: (rewr_hid_ws_rev _ i j); [done | done | apply: erefl | apply: erefl | done]); rewrite /lset /=.

    
    Arguments rewr_addrem [N T H rs].

    Ltac remove_at a n :=
      let i := pos_of_at a n in
      apply_bi_at a ltac:(apply: (rewr_addrem i); [apply: erefl | done | done]); simpl.

    Arguments rewr_rename [N T H rs].

    Ltac rename_at a n n' :=
      apply_bi_at a ltac:(apply: (rewr_rename n n'); done); simpl.
                       

    (* TODO: all the corresponding inverse tactics *)



    Arguments rewr_ch_trans [N T H rs].

    Ltac trans_at a n0 n1 n ty :=
      let i := pos_of_at a n0 in
      let j := pos_of_at a n1 in
      apply_bi_at a ltac:(apply: (rewr_ch_trans i j (n, ty)); [apply: erefl | apply: erefl | done | done]); rewrite /lset; simpl.

    Check rewr_ch_trans_rev.
    Arguments rewr_ch_trans_rev [N T H rs].
    Ltac trans_rev_at a n0 n1 n :=
      let i := pos_of_at a n0 in
      let j := pos_of_at a n1 in
      arg_move_at a n1 n 0%N;
      apply_bi_at a ltac:(apply: (rewr_ch_trans_rev i j); [ done | done | apply: erefl | apply: erefl | done | done]); rewrite /lset /=.
                       
    (* asymmetric tactics *)

    Arguments rewr_str [N T H rs].

    (* Thing to get rid of must be in head of context in n *)
    Ltac str_at a n :=
      let i := pos_of_at a n in
      etransitivity; [apply: (rewr_str i); [apply: erefl | done] |]; unfold lset; simpl.


    Arguments rewr_str_inp [N T H rs].
    Ltac inp_str_at a n i_n i_ty :=
      let i := pos_of_at a n in
      etransitivity; [apply: (rewr_str_inp i (i_n, i_ty)); [simpl; apply: erefl | done] |]; simpl.
