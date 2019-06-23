
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat finfun.
From mathcomp Require Import bigop ssralg div ssrnum ssrint.
From mathcomp Require Import fingroup finset. 
From mathcomp Require Import cyclic zmodp.

Require Import Posrat Premeas Meas Aux Logic finfun_fixed String SSRString SeqOps RLems Tacs DerivedTacs Aux.

Section BijectiveDec.
  Definition bij_dec {S T : finType} (f : S -> T) :=
    [forall t : T, [exists s : S, f s == t]] &&
    [forall s1 : S, [forall s2 : S, (f s1 == f s2) ==> (s1 == s2)]].

  Definition dec_inv_f {S T : finType} (f : {f : {ffun S -> T} | bij_dec f}) : {ffun T -> S}.
    destruct f as [f Hf].
    move/andP: Hf.
    elim.
    move => h1 h2.
    move/forallP: h1 => h1.
    apply ([ffun x => xchoose (existsP (h1 x))]).
  Defined.

  Lemma dec_inv_cancel_f_l {S T : finType} (f : {f : {ffun S -> T} | bij_dec f}) : cancel (val f) (dec_inv_f f).
    move => x.
    destruct f as [f Hf].
    rewrite /dec_inv_f.
    rewrite /and_rect.
    destruct (elimTF andP Hf).
    simpl.
    rewrite ffunE.
    move: (xchooseP (existsP (elimTF forallP i (f x)))).
    intro.
    move/forallP: i0.
    move/(_ x).
    move/forallP.
    move/(_ (xchoose (existsP (elimTF forallP i (f x))))).
    move/implyP => h.
    rewrite eq_sym in xchooseP.
    symmetry; apply/eqP; apply h; done.
  Qed.

  Lemma dec_inv_cancel_f_r {S T : finType} (f : {f : {ffun S -> T} | bij_dec f}) : cancel (dec_inv_f f) (val f).
    move => x.
    destruct f as [f Hf].
    simpl.
    rewrite /and_rect.
    destruct (elimTF andP Hf).
    rewrite ffunE.
    move: (xchooseP (existsP (elimTF forallP i x))).
    move/eqP.
    done.
  Qed.

  Definition dec_inv_bij_dec {S T : finType} (f : {f : {ffun S -> T} | bij_dec f}) : bij_dec (dec_inv_f f).
    apply/andP; split.
    apply/forallP => x.
    apply/existsP; exists ((val f) x).
    rewrite dec_inv_cancel_f_l; done.
    apply/forallP => x; apply/forallP => y; apply/implyP => h.
    move: (dec_inv_cancel_f_r f x) => h1.
    move: (dec_inv_cancel_f_r f y) => h2.
    rewrite -h1 -h2.
    rewrite (eqP h) //=.
  Qed.

  Definition dec_inv {S T : finType} (f : {f : {ffun S -> T} | bij_dec f}) : {f : {ffun T -> S} | bij_dec f}.
    exists (dec_inv_f f).
    apply dec_inv_bij_dec.
  Defined.
  

  Lemma bij_dec_bij {S T : finType} (f : S -> T) : (bij_dec f) -> (bijective f).
    move/andP; elim => h1 h2.
    move/forallP: h1 => h1.
    move/forallP: h2 => h2.
    exists (fun x => xchoose (existsP (h1 x))).
    move => x.
    move: (xchooseP (existsP (h1 (f x)))) => h.
    apply/eqP.
    move/forallP: (h2 (xchoose (existsP (h1 (f x))))).
    move/(_ x).
    move/implyP.
    move => h3.
    apply (h3 h).
    move => x.
    move: (xchooseP (existsP (h1 x))); move/eqP => ->; done.
  Qed.

  Lemma dec_inv_cancel_r {S T : finType} (f : {f : {ffun S -> T} | bij_dec f}) : cancel (val (dec_inv f)) (val f).
    move => x.
    simpl.
    rewrite dec_inv_cancel_f_r //=.
  Qed.

  Lemma dec_inv_cancel_l {S T : finType} (f : {f : {ffun S -> T} | bij_dec f}) : cancel (val f) (val (dec_inv f)).
    move => x.
    simpl.
    rewrite dec_inv_cancel_f_l //=.
  Qed.

End BijectiveDec.

Section OT.
  Context (D: finType).
  Definition TDP :=
    { x: {ffun D -> D} | bij_dec x}.
  Definition inv_tdp : TDP -> TDP := fun f => dec_inv f. (* this function is inefficient *)
  Context (B : D -> bool).

  Inductive ty :=
  | tyD
  | tyTDP
  | tyBool
  | tyPair : ty -> ty -> ty.


  Fixpoint ty_enc (t : ty) : GenTree.tree (option bool) :=
    match t with
    | tyD => GenTree.Leaf None 
    | tyTDP => GenTree.Leaf (Some false)
    | tyBool => GenTree.Leaf (Some true)
    | tyPair t1 t2 => GenTree.Node 0 [:: ty_enc t1; ty_enc t2]
    end.

  Fixpoint ty_dec (t : GenTree.tree (option bool)) : ty :=
    match t with
      | GenTree.Leaf (Some false) => tyTDP
      | GenTree.Leaf (Some true) => tyBool
      | GenTree.Leaf None => tyD                                    
      | GenTree.Node _ (x :: y :: _) => tyPair (ty_dec x) (ty_dec y)
      | _ => tyD
               end.
                          
  Lemma ty_can : cancel ty_enc ty_dec.
    move => x.
    induction x; rewrite //=.
    rewrite IHx1 IHx2 //=.
  Qed.
  Canonical ty_eq := EqType ty (CanEqMixin ty_can).
  Canonical ty_ch := ChoiceType ty (CanChoiceMixin ty_can).

  Fixpoint denomTy (t : ty) : finType :=
    match t with
      | tyD => D
      | tyTDP => [finType of TDP]
      | tyBool => [finType of bool]
      | tyPair t1 t2 => [finType of (denomTy t1) * (denomTy t2)]
                          end.

  Local Instance ty_type : type [eqType of ty].
   econstructor.
   instantiate (1 := denomTy).
   instantiate (1 := tyPair).
   done.
 Defined.

  Definition rl := rlist [choiceType of string] [choiceType of ty].

  Open Scope string_scope.

  Definition OT_real :=
    [::
       inr ("m", tyPair tyBool tyBool);
       inr ("i", tyBool);
       [::] ~> ("p", tyTDP) hid (munif [finType of TDP]);
       [::] ~> ("y", tyPair tyD tyD) hid ((munif D) ** (munif D));
       [:: ("i", tyBool); ("N2Rf", tyTDP); ("y", tyPair tyD tyD)] ~> ("z", tyPair tyD tyD) dhid
                                (fun i f y => if i then (y.1, sval f y.2) else (sval f y.1, y.2));
       [:: ("N2Tz", tyPair tyD tyD); ("p", tyTDP); ("m", tyPair tyBool tyBool)] ~> ("x", tyPair tyBool tyBool) dhid
                                (fun z f m => (xorb m.1 (B( sval (inv_tdp f) z.1)), xorb m.2 (B (sval (inv_tdp f) z.2))));
       [:: ("N2Rx", tyPair tyBool tyBool); ("i", tyBool); ("y", tyPair tyD tyD)] ~> ("o", tyBool) dvis
                                (fun x i y => if i then xorb (B y.2) x.2 else xorb (B y.1) x.1);
       [:: ("i", tyBool)] ~> ("leakRRi", _) dvis id;
       [:: ("p", tyTDP)] ~> ("T2Nf", _) dhid id;
       [:: ("T2Nf", tyTDP)] ~> ("N2Rf", _) dhid id;
       [:: ("T2Nf", tyTDP)] ~> ("leakRNf", _) dvis id;
       [:: ("N2Rf", tyTDP)] ~> ("leakRRf", _) dvis id;
       [:: ("y", tyPair tyD tyD)] ~> ("leakRRy", _) dvis id;
       [:: ("z", tyPair tyD tyD)] ~> ("R2Nz", _) dhid id;
       [:: ("R2Nz", tyPair tyD tyD)] ~> ("N2Tz", _) dhid id;
       [:: ("R2Nz", tyPair tyD tyD)] ~> ("leakRNz", _) dvis id;
       [:: ("x", tyPair tyBool tyBool)] ~> ("T2Nx", _) dhid id;
       [:: ("T2Nx", tyPair tyBool tyBool)] ~> ("N2Rx", _) dhid id;
       [:: ("T2Nx", tyPair tyBool tyBool)] ~> ("leakRNx", _) dvis id;
       [:: ("T2Nx", tyPair tyBool tyBool)] ~> ("leakRRx", _) dvis id].

  Lemma OT_real_valid : R_wf _ _ OT_real.
    done.
  Qed.

  Definition OT_ideal :=
    [::
       inr ("m", tyPair tyBool tyBool);
       inr ("i", tyBool);
       [:: ("T2Fm", tyPair tyBool tyBool); ("R2Fi", tyBool)] ~> ("F2Ro", tyBool) dhid (fun m i => if i then m.2 else m.1);
       [:: ("F2Ro", tyBool)] ~> ("o", _) dvis id;
       [:: ("m", tyPair tyBool tyBool)] ~> ("T2Fm", _) dhid id;
       [:: ("i", tyBool)] ~> ("R2Fi", _) dhid id;
       [:: ("i", tyBool)] ~> ("leakIRi", _) dvis id;
       [:: ("F2Ro", tyBool)] ~> ("leakIRo", _) dvis id].

  Definition OT_ideal_clean :=
    [::
       inr ("m", tyPair tyBool tyBool);
       inr ("i", tyBool);
       [:: ("m", tyPair tyBool tyBool); ("i",tyBool)] ~> ("o", tyBool) dvis (fun m i => if i then m.2 else m.1);
       [:: ("i", tyBool)] ~> ("leakIRi", _) dvis id;
       [:: ("m", tyPair tyBool tyBool); ("i", tyBool)] ~> ("leakIRo", tyBool) dvis (fun m i => if i then m.2 else m.1)].
       
  Lemma OT_ideal_valid : R_wf _ _ OT_ideal.
    done.
  Qed.

  Lemma OT_ideal_1 : OT_ideal <~~> OT_ideal_clean.
  rewrite /OT_ideal.
  simpl.
  autosubst_at leftc "R2Fi" "F2Ro".
  remove_at leftc "R2Fi".
  autosubst_at leftc "F2Ro" "leakIRo".
  autosubst_at leftc "F2Ro" "o".
  remove_at leftc "F2Ro".
  autosubst_at leftc "T2Fm" "leakIRo".
  autosubst_at leftc "T2Fm" "o".
  remove_at leftc "T2Fm".
  reflexivity.
  Qed.

  Definition OT_real_clean := [:: inr ("m", tyPair tyBool tyBool); inr ("i", tyBool);
      [::] ~> ("p", tyTDP) hid munif [finType of TDP];
      [::] ~> ("y", tyPair tyD tyD) hid munif D ** munif D;
      [:: ("p", tyTDP); ("i", tyBool); ("y", tyPair tyD tyD)] ~> ("z", tyPair tyD tyD)
      hid (fun (x : _) (x0 : _) (x1 : _) =>
           ret (if x0 then (x1.1, sval x x1.2) else (sval x x1.1, x1.2)));
      [:: ("z", tyPair tyD tyD); ("p", tyTDP); ("m", tyPair tyBool tyBool)] ~>
      ("x", tyPair tyBool tyBool)
      hid (fun (x : _) (x0 : _) (x1 : _) =>
           ret (xorb x1.1 (B (sval (inv_tdp x0) x.1)), xorb x1.2 (B (sval (inv_tdp x0) x.2))));
      [:: ("x", tyPair tyBool tyBool); ("i", tyBool); ("y", tyPair tyD tyD)] ~> 
      ("o", tyBool)
      vis (fun (x : _) (x0 : _) (x1 : _) =>
           ret (if x0 then xorb (B x1.2) x.2 else xorb (B x1.1) x.1));
      [:: ("i", tyBool)] ~> ("leakRRi", tyBool) vis [eta mret];
      [:: ("p", tyTDP)] ~> ("leakRNf", tyTDP) vis [eta mret];
      [:: ("p", tyTDP)] ~> ("leakRRf", tyTDP) vis [eta mret];
      [:: ("y", tyPair tyD tyD)] ~> ("leakRRy", tyPair tyD tyD) vis [eta mret];
      [:: ("z", tyPair tyD tyD)] ~> ("leakRNz", tyPair tyD tyD) vis [eta mret];
      [:: ("x", tyPair tyBool tyBool)] ~> ("leakRNx", tyPair tyBool tyBool) vis [eta mret];
      [:: ("x", tyPair tyBool tyBool)] ~> ("leakRRx", tyPair tyBool tyBool) vis [eta mret]].


  Definition OT_1 : OT_real <~~> OT_real_clean.
    rewrite /OT_real.
    simpl.
    autosubst_at leftc "T2Nf" "N2Rf".
    autosubst_at leftc "T2Nf" "leakRNf".
    remove_at leftc "T2Nf".
    autosubst_at leftc "N2Rf" "leakRRf".
    autosubst_at leftc "N2Rf" "z".
    remove_at leftc "N2Rf".
    autosubst_at leftc "R2Nz" "N2Tz".
    autosubst_at leftc "R2Nz" "leakRNz".
    remove_at leftc "R2Nz".
    autosubst_at leftc "N2Tz" "x".
    remove_at leftc "N2Tz".
    autosubst_at leftc "T2Nx" "N2Rx".
    autosubst_at leftc "T2Nx" "leakRNx".
    autosubst_at leftc "T2Nx" "leakRRx".
    remove_at leftc "T2Nx".
    autosubst_at leftc "N2Rx" "o".
    remove_at leftc "N2Rx".
    reflexivity.
  Qed.

  Goal OT_real_clean <~~> [::].
    rewrite /OT_real_clean.
    simpl.
    autosubst_at leftc "x" "o". 
    autosubst_at leftc "z" "o". 
    r_ext_at leftc "o" (fun (f : TDP) (i : bool) (y : D * D) (m : bool * bool) => ret (if i then m.2 else m.1)).
    move => f i y m.
    destruct i.
    simpl.
    unfold inv_tdp.
    rewrite /inv_tdp.
    rewrite dec_inv_cancel_l.
    generalize (B y.2).
    generalize (m.2).
    induction 0; induction 0; done.
    rewrite dec_inv_cancel_l.
    generalize (B y.1).
    generalize (m.1).
    induction 0; induction 0; done.
