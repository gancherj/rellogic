
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat .
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap tuple.

Require Import Premeas Meas Posrat Aux finfun_fixed SeqOps.

Definition dep_cast {A} {B : A -> Type} {x y : A}  (z : B x) (heq : x = y) : B y.
  rewrite -heq; apply z.
Defined.

Lemma cast_existT : forall {A} {P : A -> Type} {x1} {x2} (heq : x1 = x2) (p : P x1),
    existT P x1 p = existT P x2 (dep_cast p heq).
intros.
destruct heq.
simpl.
done.
Qed.


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

  Fixpoint lift_det {ns n} (r : detReaction ns n) {struct ns} : Reaction ns n.
  destruct ns; simpl in *.
  apply (ret r).
  apply (fun a => lift_det _ _ (r a)).
  Defined.

  Definition rbind {ns} {ns'} {n n'} (r : Reaction ns n) (k : denomT n.2 -> Reaction (ns ++ ns') n') : Reaction (ns ++ ns') n'.
    induction ns; simpl in *.
    induction ns'; simpl in *.
    apply (mbind r k).
    intro; apply IHns'.
    apply (fun n2 => k n2 X).
    intro; apply IHns.
    apply r; apply X.
    apply (fun n2 => k n2 X).
  Defined.


  Fixpoint detReaction_subst {ns ns'} {n n'} (r : detReaction ns n) (k : Reaction (n :: (ns ++ ns')) n')  {struct ns}
    : Reaction (n :: (ns ++ ns')) n'.
    induction ns.
    simpl in *.
    apply (fun _ => (k r)).
    simpl in *.
    intros x y.
    apply (detReaction_subst _ _ _ _  (r y) (fun z => k z y) x).
  Defined.

  Fixpoint React_eq ns n (r1 r2 : Reaction ns n) {struct ns} : Prop.
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

  Definition React_subst_val {ns f} (r : Reaction ns f) (n n' : N) : Reaction ns (if f.1 == n then n' else f.1, f.2).
  induction ns.
  apply r.
  simpl in *.
  destruct (f.1 == n).
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

  Definition Reaction_pair {ns} {n n'} t (k1 : Reaction ns n) (k2 : Reaction ns n') : (Reaction ns (t, tprod n.2 n'.2)) * (detReaction ((t, tprod n.2 n'.2) :: ns) n) * (detReaction ((t, tprod n.2 n'.2) :: ns) n').
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
Definition drct {ns n} b (r : detReaction ns n) : reaction := existT _ (ns, b, n) (lift_det r).

Definition reaction_pair (r1 r2 : reaction) (n : N) : (tag r1).1.1 = (tag r2).1.1 -> reaction * reaction * reaction.
intro.
destruct r1, r2; simpl in *.
rewrite H0 in r.
move: (Reaction_pair n r r0) => p.
apply (existT _ (_, false, _) p.1.1, existT (fun ns => Reaction ns.1.1 ns.2) (_,x.1.2,_) (lift_det p.1.2), existT (fun ns => Reaction ns.1.1 ns.2) (_, x0.1.2, _) (lift_det  p.2)).
Defined.

Definition reaction_weak (r : reaction) (n : N * T) : reaction.
    destruct r.
    econstructor.
    instantiate (1 := (n :: x.1.1, x.1.2, x.2)).
    simpl.
    apply (fun _ => r).
Defined.

Definition reaction_subst_arg (r : reaction) (n n' : N) : reaction.
    destruct r.
    econstructor.
    instantiate (1 := (subst_arg x.1.1 n n', x.1.2, x.2)).
    simpl in *.
    apply React_subst_arg.
    apply r.
Defined.

Definition reaction_subst (r : reaction) (n n' : N) : reaction.
    destruct r.
    econstructor.
    instantiate (1 := (subst_arg x.1.1 n n', x.1.2, (if x.2.1 == n then n' else x.2.1, x.2.2))).
    simpl.
    apply React_subst_arg.
    apply React_subst_val.
    apply r.
Defined.

Definition reaction_dep (r : reaction) (n : N) := n \in map fst (tag r).1.1.

Definition rlist := list (reaction + N).

Definition rlist_subst_arg (r : rlist) (n n' : N) : rlist :=
  map (fun a => match a with | inr m => inr m | inl r => inl (reaction_subst_arg r n n') end) r.

Definition rlist_subst (r : rlist) (n n': N) : rlist :=
  map (fun a => match a with | inr m => inr (if m == n then n' else m) | inl r => inl (reaction_subst r n n') end) r.

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

  Definition RArgs (r : rlist) : seq N :=
    flatten (map (fun x =>
                    match x with
                      | inl r => map fst (tag r).1.1
                      | inr _ => nil end) r).

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
    Definition r_compat (r1 r2 : rlist) :=
      forall x, (x \in RChans r1) && (x \in RChans r2) ->
                                                        [|| ((x \in RInputs r1) && (x \in ROutputs r2)) |
                                                         ((x \in RInputs r2) && (x \in ROutputs r1))]. 

  Definition rlist_nub_hide (r : rlist) (chans1 chans2 : seq N) : rlist :=
    pmap (fun rct =>
            match rct with
            | inl (existT (a,b,c) r) => if (c.1 \in chans1) && (c.1 \in chans2) then
                                          Some (inl (existT (fun ns => Reaction ns.1.1 ns.2) (a, false, c) r)) else
                                          Some rct
            | inr i => if (i \in chans1) && (i \in chans2) then None else Some (inr i)
                                                                               end) r.
  Definition rlist_comp_hide r1 r2 :=
    let c1 := RChans r1 in
    let c2 := RChans r2 in
    (rlist_nub_hide r1 c1 c2) ++ (rlist_nub_hide r2 c1 c2).

  Definition use_dominates (rs : rlist) (h : N) (c : N) :=
    all (fun ri =>
           match ri with
             | inl r => (h \in map fst ((tag r).1.1)) ==> (c \in map fst ((tag r).1.1))
             | inr _ => true end) rs.

Notation "G ~> c b D" := (inl (existT (fun ns => Reaction ns.1.1 ns.2) (G, b, c) D)) (at level 80, c at level 9, b at level 9).

Inductive r_rewr_bi : rlist -> rlist -> Prop :=
| rewr_bi_trans : forall r1 r2 r3, r_rewr_bi r1 r2 -> r_rewr_bi r2 r3 -> r_rewr_bi r1 r3
| rewr_bi_sym : forall r1 r2, r_rewr_bi r1 r2 -> r_rewr_bi r2 r1
| rewr_perm : forall rs rs', Perm rs rs' -> r_rewr_bi rs rs'
| rewr_add_ch : forall c rs f g (r : Reaction g f) b,
    c \in g ->
    r_rewr_bi ((g ~> f b r) :: rs)
              (((c :: g) ~> f b (fun _ => r)) :: rs)
| rewr_r_perm : forall rs r {ns} (H : Perm _ ns), r_rewr_bi (inl r :: rs) (inl (reaction_perm r H) :: rs)
| rewr_ext : forall rs G c b (k k' : Reaction G c),
      React_eq _ _ k k' ->
      r_rewr_bi ((G ~> c b k) :: rs)
             ((G ~> c b k') :: rs)
  | rewr_fold : forall rs G1 G2 h (r : Reaction G1 h) n (k : (denomT h.2 -> Reaction (G1 ++ G2) n)) (b : bool) ,
      h.1 \notin RChans rs ->
      h.1 != n.1 ->
      r_rewr_bi (((G1 ++ G2) ~> n b (rbind r k)) :: rs)
                ((G1 ~> h false r) :: ((h :: (G1 ++ G2)) ~> n b k) :: rs)
  | rewr_pair : forall n rs (r1 r2 : reaction) (H : (tag r1).1.1 = (tag r2).1.1),
      n \notin RChans rs ->
      let p := reaction_pair r1 r2 n H in
      r_rewr_bi (inl r1 :: inl r2 :: rs) (inl p.1.1 :: inl p.1.2 :: inl p.2 :: rs)
  | rewr_subst : forall (rs : rlist) ns ns' b1 b2 h f (r : detReaction ns h) (k : Reaction (h :: (ns ++ ns')) f), 
      r_rewr_bi
        [:: (ns ~> h b1 (lift_det r)), (h :: (ns ++ ns') ~> f b2 k) & rs]
        [:: (ns ~> h b1 (lift_det r)), (h :: (ns ++ ns') ~> f b2 (detReaction_subst r k)) & rs]
  | rewr_hid_ws :
      forall g1 g2 h (d : Reaction g1 h) c (d' : Reaction (g1 ++ g2) c) b rs,
        r_rewr_bi
         [:: (g1 ~> h false d), ((h :: (g1 ++ g2)) ~> c b (fun _ => d')) & rs] 
         [:: (g1 ~> h false d), (((g1 ++ g2)) ~> c b d') & rs] 
  | rewr_addrem :
      forall rs h g1 (r : Reaction g1 h),
        all (fun x => x \in RChans rs) (map fst g1) ->
        h.1 \notin RChans rs ->
        r_rewr_bi
          ((g1 ~> h false r) :: rs)
          (rs).

  Inductive r_rewr : rlist -> rlist -> Prop :=
  | rewr_bi_r : forall r1 r2, r_rewr_bi r1 r2 -> r_rewr r1 r2
  | rewr_bi_l : forall r1 r2, r_rewr_bi r1 r2 -> r_rewr r2 r1
  | rewr_refl : forall r, r_rewr r r
  | rewr_trans : forall r1 r2 r3, r_rewr r1 r2 -> r_rewr r2 r3 -> r_rewr r1 r3
  | rewr_weak : forall n (rs : rlist) (r : reaction) (r' : reaction), 
      n \in (tag r).1.1 ->
      reaction_dep r' (tag r).2.1 ->
      r_rewr (inl r' :: inl r :: rs)
             (inl (reaction_weak r' n) :: inl r :: rs) 
  | rewr_str : forall (rs : rlist) (r : reaction) ns b f (k : Reaction ns f) n,
      (all (fun x => x \in ns) (tag r).1.1) ->
      n = (tag r).2 ->
      r_rewr (inl (existT (fun ns => Reaction ns.1.1 ns.2) (n :: ns, b, _) (fun _ => k)) :: inl r :: rs)
             (inl (existT (fun ns => Reaction ns.1.1 ns.2) (ns, b, _) k) :: inl r :: rs)
  | rewr_str_inp : forall (rs : rlist) (i : N) ns b f (k : Reaction ns f) t,
      r_rewr (inl (existT (fun ns => Reaction ns.1.1 ns.2) ((i, t) :: ns, b, _) (fun _ => k)) :: inr i :: rs)
             (inl (existT (fun ns => Reaction ns.1.1 ns.2) (ns, b, _) k) :: inr i :: rs)
  | rewr_rename : forall rs n n',
      n \notin RInputs rs ->
      n \notin ROutputs rs ->
      n' \notin RChans rs ->
      n' \notin RArgs rs ->
      r_rewr rs (rlist_subst rs n n')
  | rewr_congr : forall rs1 rs2 rs3,
      r_compat rs3 rs1 ->
      r_compat rs3 rs2 ->
      r_rewr (rlist_comp_hide rs3 rs1) (rlist_comp_hide rs3 rs2).

End RDef.

Add Parametric Relation (N T : choiceType) `{type T} : (@rlist N T _) (@r_rewr N T _)
    reflexivity proved by (@rewr_refl _ _ _)
    transitivity proved by (@rewr_trans _ _ _) as r_rewr_rel.

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


Notation "G ~> c 'vis' D" := (inl (existT (fun ns => Reaction ns.1.1 ns.2) (G, true, c) D)) (at level 80).

Notation "G ~> c 'dvis' D" := (inl (existT (fun ns => Reaction ns.1.1 ns.2) (G%SEQ, true, c) (lift_det G c D))) (at level 80).

Notation "G ~> c 'hid' D" := (inl (existT (fun ns => Reaction ns.1.1 ns.2) (G, false, c) D)) (at level 80).

Notation "G ~> c 'dhid' D" := (inl (existT (fun ns => Reaction ns.1.1 ns.2) (G%SEQ, false, c) (lift_det G c D))) (at level 80).

Notation "x1 ~~> x2" := (r_rewr x1 x2) (at level 40).

Notation "x ||| y" := (rlist_comp_hide _ _ x y) (at level 40).
Notation "x |||v y" := (rlist_comp _ _ x y) (at level 40).

Section Liftings.
  Context {N T : choiceType} `{type T}.

Notation "G ~> c b D" := (inl (existT (fun ns => Reaction ns.1.1 ns.2) (G, b, c) D)) (at level 80, c at level 9, b at level 9).

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

End Liftings.


Ltac get_rs :=
  match goal with
  | [ |- @r_rewr _ _ _ ?rs _] => rs
                                   end.

  (* n may be either a nat or a name; if a nat, just return the nat; if something else, find the index of the reaction with the corresponding name *)
  Ltac r_idx_of n :=
    match (type of n) with
    | nat => n
    | _ =>
      let rs := get_rs in
      let i := eval compute in (ofind rs (fun m => chan_of m == n)) in
        match i with
            | Some ?a => a
            | None => fail "sequent not found: " n
                            end 
             end.

Ltac get_args0 :=
    match goal with
    | [ |- @r_rewr _ _ _ (inl ?r :: _) _ ] => constr:((tag r).1.1)
        end.

Ltac get_args1 :=
    match goal with
    | [ |- @r_rewr _ _ _ (_ :: (inl ?r) :: _) _ ] => constr:((tag r).1.1)
        end.

  (* n may be either a nat or a name; if a nat, return the nat; if something else, find the index of the argument that matches the name in the first reaction *)
  Ltac arg_idx_of n :=
    match (type of n) with
    | nat => n
    | _ =>
      let args := get_args0 in
      let i := eval compute in (ofind args (fun p => p.1 == n)) in
            match i with
                | Some ?a => a
                | None => fail "argument not found: " n
                                end
             end.

  (* move 'from' to 'to' *)
  Ltac r_move from to :=
   let i := r_idx_of from in 
   let j := r_idx_of to in
   etransitivity; [apply rewr_bi_r; apply rewr_perm; apply (Perm_swap_irrel i j) | idtac]; rewrite /swap /=.

  (* move arguments 'from' to 'to'  in the first reaction *)
  Ltac arg_move from to :=
   let i := arg_idx_of from in 
   let j := arg_idx_of to in
   etransitivity; [apply rewr_bi_r; apply (rewr_r_perm _ _ _ _ (Perm_swap i j _)) | idtac]; rewrite /swap /=.

    (* move 'n' to front arg *)
  Ltac arg_focus n :=
    let i := arg_idx_of n in
    arg_move i 0%N.

  (* if x and y have the same arguments, take their product and name it n *)
  Ltac r_prod x y n := r_move x 0%N; r_move y 0%N; etransitivity; [
                     apply rewr_bi_r; apply: (rewr_pair _ _ n); done | simpl].

  (* move 'n' (name or index) to 0 and execute t, and move it back *)
    Ltac r_at n t := r_move n 0%N; t; r_move n 0%N.

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
      let args1 := get_args0 in
      let args2 := get_args1 in
      let chk := eval compute in (n2 \in map fst args1) in
        match chk with
        | false => fail "reaction value " n2 " not found in " n1
        | true => 
        let x := eval compute in (ofind_val args2 (fun x => x \notin args1)) in
        k x
        end.

    Ltac r_weak n1 n2 :=
      r_find_weak n1 n2
        ltac:(fun p =>
           let j := eval compute in p in
           match j with
           | Some ?p1p2 => r_weak_by n1 n2 constr:(p1p2.1) constr:(p1p2.2); r_weak n1 n2
           | None => idtac                                                             
           | _ => idtac "hello" j
                    end).


    Ltac ensure_arg_prefix ns ctr :=
      match ns with
      | nil => idtac
      | (?x :: ?xs) =>
        arg_move x ctr; ensure_arg_prefix xs (S ctr)
                                          end.

    (* substute f`/eterministic x into y *)
Ltac get_val0 :=
  match goal with
  | [ |- r_rewr (inl ?r :: _) _] => constr:((tag r).2)
                                           end.

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