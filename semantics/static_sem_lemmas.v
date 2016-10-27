(*

  Copyright 2016 University of Luxembourg

  This file is part of our formalization of Platzer's
    "A Complete Uniform Substitution Calculus for Differential Dynamic Logic"
  available here: http://arxiv.org/pdf/1601.06183.pdf (July 27, 2016).
  We refer to this formalization as DdlCoq here.

  DdlCoq is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  DdlCoq is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with DdlCoq.  If not, see <http://www.gnu.org/licenses/>.

  authors:
    Vincent Rahli
    Marcus Völp
    Ivana Vukotic

 *)


Require Export static_sem.
Require Export dynamic_semantics.
Require Export terms_util2.
Require Export list_util.


(**

 This file implements some additional lemmas which we used in order
 to prove static semantic lemmas.

 *)


Lemma equal_states_upto_prop1 :
  forall v s1 s2 vs,
    equal_states_except s1 s2 vs
    -> not (List.In v vs)
    -> s1 v = s2 v.
Proof.
  introv h1 h2; auto.
Qed.

Lemma ex_derive_all_n_id : ex_derive_all_n (fun x => x).
Proof.
  introv.
  apply ex_derive_n_id.
Qed.

Definition unary2vec (f : R -> R) : Vector.t R 1%nat -> R :=
  fun v : Vector.t R 1%nat =>
    match v with
    | Vector.cons x 0 Vector.nil => f x
    | _ => R0
    end.

Definition id_vec : Vector.t R 1%nat -> R :=
  unary2vec (fun x => x).

Lemma ex_partial_derive_st_func_id_vec : ex_partial_derive_st_func id_vec.
Proof.
  introv d; introv.
  unfold id_vec, unary2vec.
  apply (Vector.caseS' ts).
  introv; simpl.

  clear ts.

  apply (@Vector.case0
                T
                (fun t =>
                   (forall t0 : T, Vector.In t0 (Vector.cons T h 0 t) -> ex_all_partial_derive_st (fun s : state => G s t0)) ->
                   ex_all_partial_derive_st
                     (fun s : state =>
                        match Vector.map (G s) t return R with
                        | @Vector.nil _ => G s h
                        | @Vector.cons _ _ _ _ => R0
                        end))).
  simpl.
  clear t.
  introv ih.

  pose proof (ih h) as q; clear ih.
  autodimp q hyp.
  repeat constructor.
Qed.

Lemma ex_partial_derive_st_func_sub_id_vec : smooth_fun_T id_vec.
Proof.
  introv d; introv.
  unfold id_vec, unary2vec.
  apply (Vector.caseS' ts).
  introv; simpl.

  clear ts.

  apply (@Vector.case0
                T
                (fun t =>
                   (forall t0 w l',
                       Vector.In t0 (Vector.cons T h 0 t)
                       -> sublist (w :: l') (v :: l)
                       -> ex_partial_derive (fun s : state => G s t0) w l') ->
                   ex_partial_derive
                     (fun s : state =>
                        match Vector.map (G s) t return R with
                        | @Vector.nil _ => G s h
                        | @Vector.cons _ _ _ _ => R0
                        end) v l)).
  simpl.
  clear t.
  introv ih; introv; simpl in *.

  apply ih; auto; try (apply sublist_refl).
  repeat constructor.
Qed.

Definition interp_fun_id : interpretation_function 1%nat :=
  MkInterpFun 1%nat id_vec ex_partial_derive_st_func_sub_id_vec.

Lemma interpQuantExt_false : interpQuantExt (fun _ => FalseFormulaSem).
Proof.
  introv h; tcsp.
Qed.

Definition interp_quant_false : interpretation_quantifier :=
  MkInterpQuant (fun _ => FalseFormulaSem) interpQuantExt_false.

(** states s1 and s2 are equal for variables in vars *)
Definition equal_states_on (s1 s2 : state) (vs : list KAssignable) : Prop :=
  forall x,
    List.In x vs
    -> s1 x = s2 x.

(** iff states s1 and s2 are equal for all variables,
then they are equal on the variable at the head of that list,
as well as on the variables which are in tale at that list *)
Lemma equal_states_on_cons :
  forall s1 s2 v vs,
    equal_states_on s1 s2 (v :: vs)
    <-> (s1 v = s2 v /\ equal_states_on s1 s2 vs).
Proof.
  introv; split; intro h; repnd; dands; auto.
  { apply (h v); simpl; tcsp. }
  { introv i; apply (h x); simpl; tcsp. }
  { introv i; simpl in i; repndors; subst; auto. }
Qed.

(** iff states s1 and s2 are equal on append of two lists,
then they are equal on both of those lists *)
Lemma equal_states_on_app :
  forall s1 s2 vs1 vs2,
    equal_states_on s1 s2 (vs1 ++ vs2)
    <-> (equal_states_on s1 s2 vs1 /\ equal_states_on s1 s2 vs2).
Proof.
  introv; split; intro h; repnd; dands; auto.
  { introv i.
    apply (h x).
    apply in_app_iff; auto. }
  { introv i.
    apply (h x).
    apply in_app_iff; auto. }
  { introv i.
    apply in_app_iff in i; repndors.
    - apply (h0 x); auto.
    - apply (h x); auto.
  }
Qed.

(** states s1 and s2 are equal for variables in vars *)
Definition equal_states_on_ea (s1 s2 : state) (e : EAssignables) : Prop :=
  forall x : KAssignable,
    in_eassignables x e = true
    -> s1 x = s2 x.

(*
Lemma equal_states_on_ea_cons :
  forall s1 s2 v vs,
    equal_states_on_ea s1 s2 (EA_assignable v :: vs)
    <-> (s1 v = s2 v /\ equal_states_on_ea s1 s2 vs).
Proof.
  introv; split; intro h; repnd; dands; auto.
  { apply (h v); simpl; tcsp.
    dest_cases w; dest_cases w. }
  { introv i; apply (h x); simpl; tcsp.
    dest_cases w. }
  { introv i; simpl in i; repndors; subst; auto.
    dest_cases w; dest_cases w. }
Qed.
*)

(* we need this lemma in order to work with empty set *)
(** iff states s1 and s2 are equal on IF_infinite l,
states s1 and s2 are equal only for variables which are not in l *)
Lemma equal_states_on_ea_all :
  forall s1 s2 l,
    equal_states_on_ea s1 s2 (FCS_infinite l)
    <-> forall v, ~ List.In v l -> s1 v = s2 v.
Proof.
  introv; split; intro h; repnd; dands; auto.
  { introv i; apply (h v); simpl; tcsp; dest_cases w. }
  { introv i; apply h; simpl in *; dest_cases w. }
Qed.

(* we need this lemma in order to work with all variables *)
(** iff states s1 and s2 are equal on FCS_infinite [] (for all variables),
then they are equal for all variables *)
Lemma equal_states_on_ea_all_nil :
  forall s1 s2,
    equal_states_on_ea s1 s2 (FCS_infinite [])
    <-> forall v, s1 v = s2 v.
Proof.
  introv.
  rewrite equal_states_on_ea_all; split; introv h; introv; tcsp.
Qed.

(** iff states s1 and s2 are equal on append of two EAssignables,
then they are equal for both EAssignables *)
Lemma equal_states_on_ea_app :
  forall s1 s2 e1 e2,
    equal_states_on_ea s1 s2 (EAssignables_app e1 e2)
    <-> (equal_states_on_ea s1 s2 e1 /\ equal_states_on_ea s1 s2 e2).
Proof.
  introv; split; intro h; repnd; dands; auto.
  { introv i.
    apply (h x).
    apply in_eassignables_app_true_iff; auto. }
  { introv i.
    apply (h x).
    apply in_eassignables_app_true_iff; auto. }
  { introv i.
    apply in_eassignables_app_true_iff in i; repndors.
    - apply (h0 x); auto.
    - apply (h x); auto.
  }
Qed.

(** extensionallity of big sum in case f and g are extensionally equal *)
Lemma big_sum_ext :
  forall {T} (vs : list T) f g,
    (forall v, List.In v vs -> f v = g v)
    -> big_sum vs f = big_sum vs g.
Proof.
  induction vs; introv imp; simpl in *; auto.
  rewrite (IHvs f g); auto.
  rewrite imp; auto.
Qed.

(** all term variables are subset of free variables of that term *)
Lemma term_variables_subset_free_vars_term :
  forall v t,
    List.In v (term_variables t)
    -> List.In (KAssignVar v) (free_vars_term t).
Proof.
  term_ind t Case; introv i; simpl in *; auto.

  { Case "KTfuncOf".
    allrw in_vec_flatten; exrepnd.
    allrw in_vec_map; exrepnd; subst.
    pose proof (IHargs a i1 i0) as q; clear IHargs.
    exists (free_vars_term a).
    dands; auto.
    apply in_vec_map.
    exists a; dands; auto.
  }

  { Case "KTread".
    destruct var as [z|d]; simpl in *; repndors; subst; auto.
  }

  { Case "KTplus".
    apply in_app_iff in i; apply in_app_iff; repndors;
      [left;apply IHt1|right;apply IHt2];auto.
  }

  { Case "KTminus".
    apply in_app_iff in i; apply in_app_iff; repndors;
      [left;apply IHt1|right;apply IHt2];auto.
  }

  { Case "KTtimes".
    apply in_app_iff in i; apply in_app_iff; repndors;
      [left;apply IHt1|right;apply IHt2];auto.
  }

  { Case "KTdivide".
    apply in_app_iff in i; apply in_app_iff; repndors;
      [left;apply IHt1|right;apply IHt2];auto.
  }

  { Case "KTpower".
    apply in_app_iff in i; apply in_app_iff; repndors;
      [left;apply IHt1|right;apply IHt2];auto.
  }

  { Case "KTdifferential".
    apply in_app_iff; auto.
  }
Qed.

(** term variables have have no duplicates *)
Lemma term_variables_nodup_eqset :
  forall t, eqset (term_variables_nodup t) (term_variables t).
Proof.
  introv; unfold term_variables_nodup.
  apply remove_duplicates_eqset.
Qed.

(** term variables without duplicates are subset of free variables of terms *)
Lemma term_variables_nodup_subset_free_vars_term :
  forall v t,
    List.In v (term_variables_nodup t)
    -> List.In (KAssignVar v) (free_vars_term t).
Proof.
  introv i.
  apply term_variables_subset_free_vars_term.
  apply term_variables_nodup_eqset in i; auto.
Qed.

Lemma implies_in_map_prime_kassignable :
  forall v l,
    List.In (KAssignVar v) l
    -> List.In (DVar v) (map KD l).
Proof.
  introv i.
  apply in_map_iff.
  eexists;dands;[|eauto].
  simpl; auto.
Qed.

(** if states v and w are equal on EA_assignables l,
they are equal on list l *)
Lemma equal_states_on_ea_assigns2ext :
  forall v w l,
    equal_states_on_ea v w (EA_assignables l)
    <-> equal_states_on v w l.
Proof.
  introv; split; introv h i; apply h; apply in_eassignables_assignables; auto.
Qed.

(** reflexivity for equal_states for EA_assignables *)
Lemma equal_states_on_ea_refl :
  forall s l, equal_states_on_ea s s l.
Proof.
  introv h; auto.
Qed.
Hint Resolve equal_states_on_ea_refl : core.

Fixpoint var_sub_find (s : var_sub) (v : KVariable) : option R :=
  match s with
  | [] => None
  | (w,r) :: s =>
    if KVariable_dec v w then Some r
    else var_sub_find s v
  end.

Lemma var_sub_find_some_implies_upd_list_state :
  forall st vs v r,
    var_sub_find vs v = Some r
    -> upd_list_state st vs (KAssignVar v) = r.
Proof.
  induction vs; simpl; introv h; ginv.
  destruct a; dest_cases w; ginv; autorewrite with core; auto.
  rewrite upd_state_diff;[|intro xx; inversion xx; tcsp];[].
  apply IHvs; auto.
Qed.

Lemma upd_list_state_decomp :
  forall st vs a,
    upd_list_state st vs a
    = match a with
      | KAssignVar v =>
        match var_sub_find vs v with
        | Some r => r
        | None => st a
        end
      | _ => st a
      end.
Proof.
  induction vs; introv; simpl; destruct a; auto.
  destruct a0; auto.

  - dest_cases w; subst; auto; autorewrite with core; auto.
    unfold upd_state; dest_cases w.
    rewrite IHvs; auto.

  - unfold upd_state; dest_cases w.
    rewrite IHvs; auto.
Qed.

Lemma var_sub_find_combine_none :
  forall vs rs v,
    length vs = length rs
    -> (var_sub_find (combine vs rs) v = None <-> not (List.In v vs)).
Proof.
  induction vs; destruct rs; introv h; simpl in *; ginv;
    split; introv q; tcsp;
    dest_cases w; subst.

  { apply IHvs in q; tcsp. }

  { destruct q; auto. }

  { apply IHvs; auto. }
Qed.

Lemma implies_var_in_eassignables_remove_vars_true :
  forall v e l,
    in_eassignables (KAssignVar v) e = true
    -> ~ List.In v l
    -> in_eassignables (KAssignVar v) (remove_vars e l) = true.
Proof.
  destruct e; simpl; introv; repeat (dest_cases w); introv h1 h2; GC;
    allrw in_KAssignables_minus.
  { destruct n; dands; auto.
    rewrite in_map_iff; intro q; destruct h2; exrepnd; ginv; auto. }
  { allrw in_app_iff; repndors; tcsp.
    allrw in_map_iff; exrepnd; ginv; tcsp. }
Qed.

(** if v' is in e then v' is in list form which e is removed *)
Lemma implies_diff_in_eassignables_remove_vars_true :
  forall v e l,
    in_eassignables (KAssignDiff v) e = true
    -> in_eassignables (KAssignDiff v) (remove_vars e l) = true.
Proof.
  destruct e; simpl; introv; repeat (dest_cases w); introv h; GC;
    allrw in_KAssignables_minus.
  { destruct n; dands; auto.
    rewrite in_map_iff; intro q; exrepnd; ginv. }
  { allrw in_app_iff; repndors; tcsp.
    allrw in_map_iff; exrepnd; ginv; tcsp. }
Qed.

Lemma equal_states_on_ea_remove_all_implies_upd_list_state :
  forall v w vars rs e,
    length vars = length rs
    -> equal_states_on_ea v w (remove_vars e vars)
    -> equal_states_on_ea
         (upd_list_state v (combine vars rs))
         (upd_list_state w (combine vars rs))
         e.
Proof.
  introv len h i.
  repeat (rewrite upd_list_state_decomp).
  destruct x as [z|d].

  {
    remember (var_sub_find (combine vars rs) z) as fs; symmetry in Heqfs; destruct fs; auto.
    apply h.
    apply var_sub_find_combine_none in Heqfs; auto.
    apply implies_var_in_eassignables_remove_vars_true; auto.
  }

  { apply h.
    apply implies_diff_in_eassignables_remove_vars_true; auto. }
Qed.

(** symmetry for equality of EAssignables on states *)
Lemma equal_states_on_ea_sym :
  forall v w e,
    equal_states_on_ea w v e
    -> equal_states_on_ea v w e.
Proof.
  introv eqs i; symmetry; apply eqs; auto.
Qed.

(** symmetry for equality of KAssignables on states *)
Lemma equal_states_on_sym :
  forall v w e,
    equal_states_on w v e
    -> equal_states_on v w e.
Proof.
  introv eqs i; symmetry; apply eqs; auto.
Qed.

(** reflexivity for equality on states *)
Lemma equal_states_on_refl :
  forall s e, equal_states_on s s e.
Proof.
  introv i; tcsp.
Qed.
Hint Resolve equal_states_on_refl : core.

(** if EAssignables e1 is subset of EAssignables e2 and
states v and w are equal on e2, then v and w are equal on e2 *)
Lemma equal_states_on_ea_eassignables_subset :
  forall v w e1 e2,
    eassignables_subset e1 e2 = true
    -> equal_states_on_ea v w e2
    -> equal_states_on_ea v w e1.
Proof.
  destruct e1, e2; simpl; introv ss es i; apply es; clear es;
    simpl in *; repeat (dest_cases w); GC;
    allrw @disj_dec_prop;
    allrw @included_dec_prop;
    allrw KAssignables_disj_prop;
    allrw KAssignables_included_prop; tcsp.
  apply ss in i0; sp.
Qed.

Lemma differ_state_except_iff_upd :
  forall v w x r,
    differ_state_except v w x r
    <-> w = upd_state v x r.
Proof.
  introv; unfold differ_state_except, upd_state; split; introv h;
    repnd; dands; subst.

  - apply functional_extensionality; introv; dest_cases w.
    symmetry; apply h0; auto.

  - introv i; dest_cases w.

  - dest_cases w.
Qed.

(** box implies not diamond *)
Lemma dynamic_semantics_formula_box_implies_not_diamond :
  forall P F I v,
    dynamic_semantics_formula I (KFbox P F) v
    -> dynamic_semantics_formula I (KFnot (KFdiamond P (KFnot F))) v.
Proof.
  simpl; introv h q; exrepnd.
  apply h in q0; tcsp.
Qed.

(** MBV of program is subset of VB of that program *)
Lemma must_bound_vars_program_subset_bound_vars_program :
  forall P,
    eassignables_subset (must_bound_vars_program P) (bound_vars_program P) = true.
Proof.
  prog_ind P Case; simpl; auto.

  { Case "KPassign".
    dest_cases w. }

  { Case "KPassignAny".
    dest_cases w. }

  { Case "KPchoice".
    apply implies_eassignables_subset_inter_l_true.
    left.
    apply implies_eassignables_subset_app_r_true.
    left; auto. }

  { Case "KPcompose".
    rewrite eassignables_subset_app_l_true_iff; dands;
      apply implies_eassignables_subset_app_r_true;[left|right]; auto. }

  { Case "KPparallel".
    rewrite eassignables_subset_app_l_true_iff; dands;
      apply implies_eassignables_subset_app_r_true;[left|right]; auto. }

  { Case "KPloop".
    remember (bound_vars_program P) as e; destruct e; auto. }

  { Case "KPreceive".
    eauto 2 with core.
    apply included_dec_prop; apply subset_refl. }

  { Case "KPbroadcast".
    eauto 2 with core.
    apply included_dec_prop; apply subset_refl. }
Qed.

(** if states s1 and s2 are equal on EAssignables e1 and e2,
then they are equal in intersection of these EAssignables *)
Lemma implies_equal_states_on_ea_inter :
  forall (s1 s2 : state) (e1 e2 : EAssignables),
    (equal_states_on_ea s1 s2 e1 \/ equal_states_on_ea s1 s2 e2)
    -> equal_states_on_ea s1 s2 (EAssignables_inter e1 e2).
Proof.
  introv h i.
  apply in_eassignables_inter_iff in i; repnd.
  repndors;[apply h in i0|apply h in i]; auto.
Qed.

(** if EAassignables e1 and e2 are equal,
and all states s1 and s2 are equal on e1,
then all states s1 and s2 are equal on e2 *)
Lemma equal_states_on_ea_eassignables_eq :
  forall s1 s2 e1 e2,
    eassignables_eq e1 e2
    -> equal_states_on_ea s1 s2 e1
    -> equal_states_on_ea s1 s2 e2.
Proof.
  introv eqe eqs i.
  apply eqs.
  apply eqe; auto.
Qed.


(** two states equal on complement of EAssignables *)
Definition equal_states_on_complement
           (v w : state)
           (e : EAssignables) : Prop :=
  forall a : KAssignable,
    in_eassignables a e = false
    -> v a = w a.

Lemma in_ode_footprint_implies_in_bound_vars :
  forall a I ode,
    In a (ode_footprint I ode)
    -> in_eassignables a (bound_vars_ode ode) = true.
Proof.
  induction ode; introv i; simpl in *; tcsp.

  { destruct child; simpl in *; auto.
    dest_cases w. }

  { apply eqset_ode_footprint_prod in i.
    apply in_app_iff in i.
    apply in_eassignables_app_true_iff; tcsp. }
Qed.

(*
Lemma dynamic_semantics_ode_implies_eq_initial_state :
  forall ode I r phi x a,
    dynamic_semantics_ode I ode r phi
    -> in_eassignables a (bound_vars_ode ode) = false
    -> ~ In x (ode_footprint I ode)
    -> v x = phi 0%R x.
Proof.
  induction ode; introv d ia i; simpl in *.

  { destruct child; simpl in *; ginv.
    dest_cases w; GC.
    repeat (apply not_or in n; repnd).
    repeat (apply not_or in i; repnd).
    GC.
    apply d0; simpl; tcsp.
    intro xx; repndors; subst; tcsp.
    destruct xp; simpl in *; auto.
  }

  { rewrite (eqset_ode_footprint_prod I ode1 ode2 x) in i.
    rewrite in_app_iff in i.
    apply not_or in i; repnd.
    apply in_eassignables_app_false_implies in ia; repnd.
    eapply IHode1; eauto. }
Qed.
 *)

Lemma ode_footprint_diff_subset_ode_footprint :
  forall I ode,
    subset
      (ode_footprint_diff I ode)
      (ode_footprint I ode).
Proof.
  introv i.
  apply in_app_iff; auto.
Qed.

Lemma ode_footprint_vars_subset_ode_footprint :
  forall I ode,
    subset
      (ode_footprint_vars I ode)
      (ode_footprint I ode).
Proof.
  introv i.
  apply in_app_iff; auto.
Qed.

Lemma equal_states_on_vec_flatten_map :
  forall v w {n} (args : Vector.t Term n ) a,
    equal_states_on v w (vec_flatten (Vector.map free_vars_term args))
    -> Vector.In a args
    -> equal_states_on v w (free_vars_term a).
Proof.
  introv equ i j.
  apply equ.
  apply in_vec_flatten.
  exists (free_vars_term a); dands; auto.
  apply in_vec_map.
  exists a; dands; auto.
Qed.
Hint Resolve equal_states_on_vec_flatten_map : core.

Lemma subset_vec_flatten_map_lr :
  forall {A B} a {n} (v1 v2 : Vector.t A n) (F G : A -> list B),
    (forall m, m < n -> subset (F (vec_nth v1 m a)) (G (vec_nth v2 m a)))
    -> subset (vec_flatten (Vector.map F v1)) (vec_flatten (Vector.map G v2)).
Proof.
  induction n; introv.

  { apply Vector.case0 with (v := v1); simpl; clear v1; auto. }

  { apply (Vector.caseS' v1); introv; clear v1.
    apply (Vector.caseS' v2); introv; clear v2.
    simpl.
    intro hyp.
    apply implies_subset_app_lr.
    { apply (hyp 0); omega. }
    apply IHn; introv ltmn.
    apply (hyp (S m)); omega. }
Qed.

Lemma term_assignables_nodup_subset_free_vars_term :
  forall t,
    subset (term_assignables_nodup t) (free_vars_term t).
Proof.
  introv.
  unfold term_assignables_nodup.
  eapply subset_eqset_l;
    [|apply eqset_sym;apply remove_duplicates_eqset].
  apply subset_refl.
Qed.

Lemma implies_KD_in_map_prime_kassignable :
  forall a l,
    List.In a l
    -> List.In (KD a) (map KD l).
Proof.
  introv i.
  apply in_map_iff.
  eexists;dands;[|eauto]; auto.
Qed.


(******************************************************************************)



(* we needed this definition in order to prove Coincidence of formulas and programs *)
Definition KPtrue : Program := KPtest KFtrue.

(* we needed this definition in order to prove Coincidence of formulas and programs *)
Fixpoint KPcomposeN (P : Program) (n : nat) :=
  match n with
  | 0 => KPtrue
  | S n => KPcompose (KPcomposeN P n) P
  end.

(* we needed this lemma in order to prove Coincidence of formulas and programs *)
Lemma program_close_implies_all :
  forall P v w I,
    program_close (dynamic_semantics_program I P) v w
    <-> exists n, dynamic_semantics_program I (KPcomposeN P n) v w.
Proof.
  introv; split; introv h.

  {
    induction h.

    { exists 0%nat; simpl; dands; tcsp. }

    { exrepnd.
      exists (S n); simpl.
      exists s; dands; auto. }
  }

  {
    exrepnd.
    revert dependent w.
    induction n; simpl in *; introv h; repnd; subst.

    { apply program_close_refl. }

    { exrepnd.
      apply IHn in h1.
      eapply program_close_trans; eauto. }
  }
Qed.

Inductive ODEcontainsConst : ODE -> Prop :=
| ODEconstPrim :
    forall c,
      ODEcontainsConst (ODEconst c)
| ODEconstProdL :
    forall L R,
      ODEcontainsConst L
      -> ODEcontainsConst (ODEprod L R)
| ODEconstProdR :
    forall L R,
      ODEcontainsConst R
      -> ODEcontainsConst (ODEprod L R).
Hint Constructors ODEcontainsConst.

Lemma in_bound_vars_ode_prop1 :
  forall x I ode,
    in_eassignables x (bound_vars_ode ode) = true
    -> ~ In x (ode_footprint I ode)
    -> ODEcontainsConst ode.
Proof.
  induction ode; introv i ni; simpl in *; auto; tcsp.

  { destruct child; simpl in *; auto.
    dest_cases w; GC.
    repeat (apply not_or in ni; repnd; GC).
    repndors; subst; tcsp. }

  { rewrite (eqset_ode_footprint_prod I ode1 ode2 x) in ni.
    rewrite in_app_iff in ni.
    apply not_or in ni; repnd.
    apply in_eassignables_app_true_iff in i; repndors.

    { apply ODEconstProdL.
      apply IHode1; auto. }

    { apply ODEconstProdR.
      apply IHode2; auto. }
  }
Qed.

Lemma contains_const_implies_free_vars_ode_all :
  forall ode,
    ODEcontainsConst ode
    -> free_vars_ode ode = EA_all [].
Proof.
  induction ode; introv h; simpl in *; tcsp; try (complete (inversion h)).

  { destruct child; simpl in *; auto.
    inversion h. }

  { inversion h; subst.

    { autodimp IHode1 hyp.
      rewrite IHode1.
      apply EAssignables_app_all_left. }

    { autodimp IHode2 hyp.
      rewrite IHode2.
      apply EAssignables_app_all_right. }
  }
Qed.

Lemma eqset_ode_footprint_vars_prod :
  forall I ode1 ode2,
    eqset (ode_footprint_vars I (ODEprod ode1 ode2))
          (ode_footprint_vars I ode1 ++ ode_footprint_vars I ode2).
Proof.
  repeat introv.
  unfold ode_footprint_vars; simpl.
  allrw map_app.
  allrw in_app_iff.
  split; intro h; tcsp.
Qed.

Lemma subset_ode_footprint_vars_free_vars_ode :
  forall I ode,
    eassignables_subset
      (EA_assignables (ode_footprint_vars I ode))
      (free_vars_ode ode) = true.
Proof.
  induction ode; tcsp.

  { destruct child; simpl; auto.

    { apply disj_dec_prop.
      apply disjoint_sym; auto. }

    { dest_cases w. }
  }

  { rewrite eassignables_subset_iff in *; introv i; simpl in *.
    dest_cases w; ginv.
    apply eqset_ode_footprint_vars_prod in i0.
    apply in_eassignables_app_true_iff.
    apply in_app_iff in i0; repndors.

    { left.
      apply IHode1; dest_cases w. }

    { right.
      apply IHode2; dest_cases w. }
  }
Qed.

Definition upd_solution_at_list
           (phi : R -> state)
           (v   : state)
           (e   : EAssignables)
           (l   : list KAssignable): R -> state :=
  fun (r : R) (a : KAssignable) =>
    if in_dec KAssignable_dec a l
    then phi r a
    else
      if in_eassignables a e (* and (not?) (r = 0)? *)
      then phi r a
      else v a.

Lemma equal_states_on_ea_upd_solution_at_list :
  forall phi r v e d,
    equal_states_on_ea (phi r) (upd_solution_at_list phi v e d r) e.
Proof.
  introv i.
  unfold upd_solution_at_list; repeat (dest_cases w).
Qed.

(** returns all variables in Formula *)
Definition all_vars_formula (f : Formula) : EAssignables :=
  EAssignables_app (free_vars_formula f) (bound_vars_formula f).

(** returns all variables in Program *)
Definition all_vars_program (p : Program) : EAssignables :=
  EAssignables_app (free_vars_program p) (bound_vars_program p).

Lemma free_vars_program_eassignables_subset_all_vars_program :
  forall p, eassignables_subset (free_vars_program p) (all_vars_program p) = true.
Proof.
  introv; unfold all_vars_program.
  apply implies_eassignables_subset_app_r_true; left; eauto 2 with core.
Qed.
Hint Resolve free_vars_program_eassignables_subset_all_vars_program : core.
