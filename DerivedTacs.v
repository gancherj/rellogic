
From mathcomp Require Import ssreflect ssrfun ssrbool ssrint eqtype ssrnat seq choice fintype rat .
From mathcomp Require Import bigop ssralg div ssrnum ssrint finset ssrnum ssrnat finmap tuple.

Require Import Premeas Meas Posrat Aux finfun_fixed SeqOps Logic Tacs.

(* keep running t1 until t1 produces None; running t2 from output of t1 *)
Ltac do_until t1 t2 :=
  let x := t1 tt in
  let y := eval simpl in x in
  match y with
    | Some ?a => t2 tt a; do_until t1 t2
    | None => idtac
    | (Some ?a) => t2 tt a; do_until t1 t2 
                end.

Definition onth_error {A} (xs : seq A) (n : option nat) :=
  match n with
  | None => None
  | Some n => List.nth_error xs n
                             end.

Ltac find_trans_at a n1 n2 :=
  let a1 := get_args_at a n1 in
  let a2 := get_args_at a n2 in
  let c := eval compute in (ofind a1 (fun x => x \notin a2)) in
  let o := eval compute in (onth_error a1 c) in
  o.
  

Ltac trans_fill a n1 n2 :=
  do_until ltac:(fun t => find_trans_at a n1 n2) ltac:(fun t nty => match nty with
                                               | @pair _ _ ?n ?ty => trans_at a n1 n2 n ty
                                                                       end).

Ltac align_for_subst_rec a xs n2 i :=
  match xs with
    | nil => idtac
    | ?x :: ?xs' =>
      arg_move_at a n2 x i; align_for_subst_rec a xs' n2 (S i)
                                                end.
  

Ltac align_for_subst a n1 n2 :=
  let a1 := get_args_at a n1 in
  let a2 := get_args_at a n2 in
  arg_move_at a n2 n1 0%N;
  let args := eval compute in (map fst a1) in
  align_for_subst_rec a args n2 1%N.
  
           
Ltac autosubst_at a n1 n2 :=
  trans_fill a n1 n2;
  align_for_subst a n1 n2;
  subst_at a n1 n2;
  let b := get_bool_at a n1 in
  let b := eval compute in b in
  match b with
    | false => hid_str_at a n1 n2
    | _ => idtac
             end.

Check RHiddens.
Arguments RHiddens [N T H].

Ltac find_clean_at a :=
  let rs := get_rs_at a in
  let c := eval compute in (ofind (RHiddens rs) (fun x => x \notin RArgs _ _ rs)) in
  c. 

Ltac clean_at a :=
  let rs := get_rs_at a in
  do_until ltac:(fun _ => find_clean_at a) ltac:(fun _ i => remove_at a i).
  
Ltac align_rec rs c :=
  match rs with
    | nil => idtac
    | ?r :: ?rs' =>
      try r_move_at leftc (chan_of r) c;
      align_rec rs' (S c)
                end.
      

Ltac align :=
      let rs := get_rs_at rightc in
      align_rec rs 0%N.
  