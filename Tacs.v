
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat .
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap tuple.

Require Import Premeas Meas Posrat Aux finfun_fixed SeqOps Logic.

Add Parametric Relation (N T : choiceType) `{type T} : (@rlist N T _) (@r_rewr N T _)
    reflexivity proved by (@rewr_refl _ _ _)
    transitivity proved by (@rewr_trans _ _ _) as r_rewr_rel.

Add Parametric Relation (N T : choiceType) `{type T} : (@rlist N T _) (@r_rewr_bi N T _)
    reflexivity proved by (@rewr_bi_refl _ _ _)
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


  Lemma rewr_subst_eq (rs : rlist N T) (ns ns2 ns' : seq (N * T)) (b1 b2 : bool) (h f : N * T) (r : detReaction N T ns h) (k : Reaction ns2 f) (k' : Reaction (h :: ns ++ ns') f) :
  existT (fun ns => Reaction ns.1.1 ns.2) (ns2, b2, f) k =
  existT (fun ns => Reaction ns.1.1 ns.2) (h :: ns ++ ns', b2, f) k' -> 
  r_rewr_bi [:: ns ~> h b1 (lift_det ns h r), ns2 ~> f b2 k & rs]
            [:: ns ~> h b1 lift_det ns h r, h :: ns ++ ns' ~> f b2 detReaction_subst N T r k' & rs].
    intro.
    rewrite H0.
    apply rewr_subst.
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


    Lemma lift_bind t f (m : meas (denomT t)) (k : denomT t -> meas (denomT f.2)) (n : N) :
      @React_eq _ _ _ nil f (mbind m k) (rbind nil nil (n,t) f m k).
      rewrite /rbind //=.
    Qed.


    Check rbind.

    Lemma lift_bind1 (p : N * T) t f (n : N) (m : denomT p.2 -> meas (denomT t)) (k : denomT p.2 -> denomT t -> meas (denomT f.2)) :
      @React_eq _ _ _ [:: p] f (fun x => mbind (m x) (k x))
                               (rbind [:: p] nil (n,t) f m (fun n2 p2 => k p2 n2)).
      rewrite /rbind //=.
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
  Ltac r_idx_of_at a n :=
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

Ltac get_tag_at a n :=
  match n with
    | 0 => 
        let rs := get_rs_at a in
        match rs with
        | (inl (@existT _ _ ?p _) :: _) => p
                                            end
    | S 0 =>
        let rs := get_rs_at a in
        match rs with
        | (_ :: inl (@existT _ _ ?p _) :: _) => p
                                            end
    | _ => fail "get_tag_at needs more cases than 0 & 1"
          end.
      
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
  Ltac arg_idx_of_at a n :=
    match (type of n) with
    | nat => n
    | _ =>
      let args := get_args_at a 0 in
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

(* REWRITING TACTICS *)

  (* move 'from' to 'to' *)
  Ltac r_move_at a from to :=
   let i := r_idx_of_at a from in 
   let j := r_idx_of_at a to in
   match a with
     | leftc => 
        etransitivity; [ensure_bi_r; apply rewr_perm; apply (Perm_swap_irrel i j) | idtac]; rewrite /swap /=
     | rightc =>                                                                                                  
       eapply rewr_r_l; [apply rewr_perm; apply (Perm_swap_irrel i j) | idtac]; rewrite /swap /=
                                                                                                     end.

  Ltac r_move from to := r_move_at leftc from to.
  Ltac r_move_r from to := r_move_at rightc from to.

  Ltac arg_move_at a n from to :=
    r_move_at a n 0%N;
    let i := arg_idx_of_at a from in
    let j := arg_idx_of_at a to in
    match a with
      | leftc =>
        etransitivity; [ensure_bi_r; apply (rewr_r_perm _ _ _ _ (Perm_swap i j _)) | idtac]; unfold swap; simpl
      | rightc =>
        eapply rewr_r_l ; [ apply (rewr_r_perm _ _ _ _ (Perm_swap i j _)) | idtac]; unfold swap; simpl
                                                                                          end.

  Ltac arg_move n from to := arg_move_at leftc n from to.
  Ltac arg_move_r n from to := arg_move_at rightc n from to.

  Ltac arg_focus n x := arg_move n x 0%N.
  Ltac arg_focus_r n x := arg_move_r n x 0%N.
    
  Ltac r_prod_at a x y n :=
    r_move_at a x 0%N;
    r_move_at a y 0%N;
    match a with
    | leftc =>
      etransitivity; [ensure_bi_r; apply: (rewr_pair _ _ n); done | simpl]; unfold eq_rect_r; simpl
    | rightc =>
      eapply rewr_r_l; [apply: (rewr_pair _ _ n); done | simpl]; unfold eq_rect_r; simpl
                         end.

  Ltac r_prod x y n := r_prod_at leftc x y n.
  Ltac r_prod_r x y n := r_prod_at rightc x y n.



    Ltac r_weak_ n t := rewrite (rewr_weak _ _ (n, t)); [idtac | done | done]; rewrite /=.

    (* weaken reaction n1, which uses reaction n2, by arg 'n' of type t (which must be in n2) *)
    Ltac r_weak_by n1 n2 n t :=
      r_move n1 0%N;
      r_move n2 1%N;
      r_weak_ n t.

    (* find arg in n2 that does not appear in n1 *)
    Ltac r_find_weak n1 n2 k :=
      r_move n1 0%N;
      r_move n2 1%N;
      let args1 := get_args_at leftc 0 in
      let args2 := get_args_at leftc (S 0) in
      let chk := eval compute in (n2 \in map fst args1) in
        match chk with
        | false => fail "reaction value " n2 " not found in " n1
        | true => 
        let x := eval compute in (ofind_val args2 (fun x => x \notin args1)) in
        k x
        end.

    (* TODO: The below one only works for the general weak rule which holds for everything; I need to implement a rule that uses rewr_hid_ws *)
    Ltac r_weak n1 n2 :=
      ensure_not_bi;
      r_find_weak n1 n2
        ltac:(fun p =>
           let j := eval compute in p in
           match j with
           | Some ?p1p2 => r_weak_by n1 n2 constr:(p1p2.1) constr:(p1p2.2); r_weak n1 n2
           | None => idtac                                                             
           | _ => idtac "hello" j
                    end).


    Ltac ensure_arg_prefix_at a n ns ctr :=
      match ns with
      | nil => idtac
      | (?x :: ?xs) =>
        arg_move_at x n x ctr; ensure_arg_prefix_at x n xs (S ctr)
                                          end.

(* Perform a rewrite on the args of n, that they're equal to ns. Used for extracting out a concat and so on. *)
Ltac rewrite_args_at a n ns :=
  let heq := fresh "heq" in
  r_move_at a n 0%N;
  let ns_old := get_args_at a 0 in
  let b := get_bool_at a 0 in
  let val := get_val_at a 0 in
  assert (heq : (ns_old, b, val) = (ns, b, val)) ; [ done | rewrite (cast_existT heq); have -> : heq = erefl by apply eq_irrelevance; clear heq]; try clear heq; unfold dep_cast; unfold eq_rect .
  

  (*

    Ltac r_subst x y :=
      r_weak y x;
      r_move y 0%N;
      let a := get_args1 in
      let ys := eval compute in (map fst a) in
      ensure_arg_prefix ys 0%N;
      arg_focus x;
      r_move x 0%N; 
      let b := get_args1 in
      let xs := eval compute in (map fst b) in
      rewrite ?lift_det0 ?lift_det1 ?lift_det2 ?lift_det3;
      let h := get_val0 in
      let zs := eval compute in (extract_right_cons_cat h a b) in
      match zs with
          | None => fail "subst failure"
          | Some ?z =>
            etransitivity; [ apply rewr_bi_r; apply: (rewr_subst_eq _ _ _ z); apply erefl | idtac]; simpl
                                                                                         end.

    Ltac r_str_ := etransitivity; [apply rewr_str; done | idtac].

    (* drop n2 from n1 *)
    Ltac r_str n1 n2 :=
      r_move n1 0%N;
      r_move n2 1%N;
      arg_focus n2;
      r_str_.

    Ltac r_str_inp n1 n2 :=
      r_move n1 0%N;
      r_move n2 1%N;
      arg_focus n2;
      rewrite rewr_str_inp.

    Ltac r_weakstr n1 n2 :=
      r_weak n1 n2;
      r_str n1 n2.

    (* rename : rename x to y; requires x is a hidden action *)
    Ltac r_rename x y := etransitivity; [apply (rewr_rename _ _ _ x y); done | idtac]; simpl.

    (* ext : operates on the first reaction. *)
    Ltac r_ext m tm :=
      r_move m 0%N;
      etransitivity; [apply rewr_bi_r; apply rewr_ext; instantiate (1 := tm); rewrite /React_eq //= | idtac].

  Arguments rbind [N T H ].

  (* if 'm' is a bind, lift the bind to fresh arg 'n' of type 't' *)
    Ltac unfold_bind0 n midn midty :=
    match goal with
    | [ |- @r_rewr _ _ _ (inl (existT _ (_, _, ?to) (mbind ?m ?k)) :: ?rs) _] =>
      etransitivity; [
        apply rewr_bi_r; apply: (@rewr_ext _ _ _ _ _ _ _ _ (rbind nil nil (midn, midty) to _ _)); done | idtac]
    end;
    etransitivity; [ apply rewr_bi_r; apply rewr_fold; done | idtac]; rewrite /rct /=.

    Ltac unfold_bind1 n midn midty :=
    match goal with
    | [ |- @r_rewr _ _ _ (inl (existT _ (?ns, _, ?to) (fun x => mbind ?m ?k)) :: ?rs) _] =>
      etransitivity; [
        apply rewr_bi_r; apply: (@rewr_ext _ _ _ _ _ _ _ _ (rbind ns nil (midn, midty) to _ _)); done | idtac]
    end;
    etransitivity; [ apply rewr_bi_r; apply rewr_fold; done | idtac]; rewrite /rct /=.

    Ltac unfold_bind2 n midn midty :=
    match goal with
    | [ |- @r_rewr _ _ _ (inl (existT _ (?ns, _, ?to) (fun x y => mbind ?m ?k)) :: ?rs) _] =>
      etransitivity; [
        apply rewr_bi_r; apply: (@rewr_ext _ _ _ _ _ _ _ _ (rbind ns nil (midn, midty) to _ _)); done | idtac]
    end;
    etransitivity; [ apply rewr_bi_r; apply rewr_fold; done | idtac]; rewrite /rct /=.

    Ltac unfold_bind3 n midn midty :=
    match goal with
    | [ |- @r_rewr _ _ _ (inl (existT _ (?ns, _, ?to) (fun x y z => mbind ?m ?k)) :: ?rs) _] =>
      etransitivity; [
        apply rewr_bi_r; apply: (@rewr_ext _ _ _ _ _ _ _ _ (rbind ns nil (midn, midty) to _ _)); done | idtac]
    end;
    etransitivity; [ apply rewr_bi_r; apply rewr_fold; done | idtac]; rewrite /rct /=.

    Ltac unfold_bind4 n midn midty :=
    match goal with
    | [ |- @r_rewr _ _ _ (inl (existT _ (?ns, _, ?to) (fun x y z w => mbind ?m ?k)) :: ?rs) _] =>
      etransitivity; [
        apply rewr_bi_r; apply: (@rewr_ext _ _ _ _ _ _ _ _ (rbind ns nil (midn, midty) to _ _)); done | idtac]
    end;
    etransitivity; [ apply rewr_bi_r; apply rewr_fold; done | idtac]; rewrite /rct /=.

    Ltac unfold_bind n midn midty :=
    r_move n 0%N;
    match goal with
    | [ |- @r_rewr _ _ _ (inl (existT _ (?ns, _, ?to) _) :: _) _] =>
      match ns with
        | nil => unfold_bind0 n midn midty
        | _ :: nil => unfold_bind1 n midn midty
        | _ :: _ :: nil => unfold_bind2 n midn midty
        | _ :: _ :: _ :: nil => unfold_bind3 n midn midty
      end
        end.

      


    (* remove redundant 'm' *)
    Ltac r_remove m :=
      r_move m 0%N;
      etransitivity; [apply rewr_bi_r; apply (rewr_addrem _ _); done | idtac]; simpl.

    Ltac r_clean :=
      match goal with
      | [ |- @r_rewr _ _ _ ?rs _ ] =>
        let p := eval compute in (ofind_val (RHiddens rs) (fun n => n \notin RArgs _ _ rs) ) in
            match p with
              | Some ?n => r_remove n
              | _ => fail "no more to clean"
            end
              end.

    Ltac r_align_rec rs c :=
      match rs with
        | nil => idtac
        | ?r :: ?rs' =>
          r_move (chan_of r) c;
          r_align_rec rs' (S c)
                      end.

    Ltac r_align :=
      match goal with
      | [ |- @r_rewr _ _ _ _ ?rs] => r_align_rec rs 0%N
                                                 end.
        
                  

  (* TODO: fold *)

  (* TODO: dep *)

  (* TODO: comp? *)

  (* TODO: unprod *)

  (* TODO: add *)
*)