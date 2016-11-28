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


Require Export adjoint_interpretation.


Definition on_uniform_substitution_term
           (t : Term)
           (s : UniformSubstitution)
           (Q : Term -> Prop) : Prop :=
  match uniform_substitution_term t s with
  | Some u => Q u
  | None => True
  end.

Definition on_substitution_dot_term
           (t u : Term)
           (Q : Term -> Prop) : Prop :=
  match substitution_dot_term t u with
  | Some u => Q u
  | None => True
  end.

Definition on_uniform_substitution_formula
           (F : Formula)
           (s : UniformSubstitution)
           (Q : Formula -> Prop) : Prop :=
  match uniform_substitution_formula F s with
  | Some f => Q f
  | None => True
  end.

Definition on_substitution_dot_term_in_formula
           (F : Formula)
           (u : Term)
           (Q : Formula -> Prop) : Prop :=
  match substitution_dot_term_in_formula F u with
  | Some u => Q u
  | None => True
  end.

Definition on_substitution_dot_term_in_program
           (P : Program)
           (u : Term)
           (Q : Program -> Prop) : Prop :=
  match substitution_dot_term_in_program P u with
  | Some u => Q u
  | None => True
  end.

Definition on_uniform_substitution_program
           (P : Program)
           (s : UniformSubstitution)
           (Q : Program -> Prop) : Prop :=
  match uniform_substitution_program P s with
  | Some p => Q p
  | None => True
  end.

Definition on_uniform_substitution_atomic_ode
           (ode : AtomicODE)
           (s   : UniformSubstitution)
           (Q   : ODE -> Prop) : Prop :=
  match uniform_substitution_atomic_ode ode s with
  | Some u => Q u
  | None => True
  end.

Definition on_substitution_dot_term_in_atomic_ode
           (ode : AtomicODE)
           (u   : Term)
           (Q   : AtomicODE -> Prop) : Prop :=
  match substitution_dot_term_in_atomic_ode ode u with
  | Some u => Q u
  | None => True
  end.

Lemma ext_interpretations_at_adjoint_interpretation_uniform_substitution_restriction_term :
  forall s t I v w x,
    In x (term_signature t)
    -> ext_interpretations_at
         (adjoint_interpretation (uniform_substitution_restriction_term s t) I v)
         (adjoint_interpretation (uniform_substitution_restriction_term s t) I w)
         x
    -> ext_interpretations_at
         (adjoint_interpretation s I v)
         (adjoint_interpretation s I w)
         x.
Proof.
  introv i h.
  destruct x; simpl; auto.

  {
    introv.
    pose proof (h r) as q; simpl in q; clear h.
    rewrite lookup_func_uniform_substitution_restriction_term_in in q; auto.
  }

  {
    introv.
    pose proof (h r) as q; simpl in q; clear h.
    rewrite lookup_pred_uniform_substitution_restriction_term_in in q; auto.
  }

  {
    introv h1 h2.
    pose proof (h v0 w0 f0 g h1 h2) as q; simpl in q; clear h.
    rewrite lookup_quant_uniform_substitution_restriction_term_in in q; auto.
  }

  {
    dands; auto.
    introv q.
    apply ext_dynamic_semantics_ode_fun; auto.
  }

  {
    introv h1 h2.
    pose proof (h v1 v2 w1 w2 h1 h2) as q; simpl in q; clear h.
    rewrite lookup_const_uniform_substitution_restriction_term_in in q; auto.
  }
Qed.

Lemma ext_interpretations_at_adjoint_interpretation_uniform_substitution_restriction_formula :
  forall s t I v w x,
    In x (formula_signature t)
    -> ext_interpretations_at
         (adjoint_interpretation (uniform_substitution_restriction_formula s t) I v)
         (adjoint_interpretation (uniform_substitution_restriction_formula s t) I w)
         x
    -> ext_interpretations_at
         (adjoint_interpretation s I v)
         (adjoint_interpretation s I w)
         x.
Proof.
  introv i h.
  destruct x; simpl; auto.

  {
    introv.
    pose proof (h r) as q; simpl in q; clear h.
    rewrite lookup_func_uniform_substitution_restriction_formula_in in q; auto.
  }

  {
    introv.
    pose proof (h r) as q; simpl in q; clear h.
    rewrite lookup_pred_uniform_substitution_restriction_formula_in in q; auto.
  }

  {
    introv h1 h2.
    pose proof (h v0 w0 f0 g h1 h2) as q; simpl in q; clear h.
    rewrite lookup_quant_uniform_substitution_restriction_formula_in in q; auto.
  }

  {
    dands; auto.
    introv q.
    apply ext_dynamic_semantics_ode_fun; auto.
  }

  {
    introv h1 h2.
    pose proof (h v1 v2 w1 w2 h1 h2) as q; simpl in q; clear h.
    rewrite lookup_const_uniform_substitution_restriction_formula_in in q; auto.
  }
Qed.

Lemma ext_interpretations_at_adjoint_interpretation_uniform_substitution_restriction_program :
  forall s t I v w x,
    In x (program_signature t)
    -> ext_interpretations_at
         (adjoint_interpretation (uniform_substitution_restriction_program s t) I v)
         (adjoint_interpretation (uniform_substitution_restriction_program s t) I w)
         x
    -> ext_interpretations_at
         (adjoint_interpretation s I v)
         (adjoint_interpretation s I w)
         x.
Proof.
  introv i h.
  destruct x; simpl; auto.

  {
    introv.
    pose proof (h r) as q; simpl in q; clear h.
    rewrite lookup_func_uniform_substitution_restriction_program_in in q; auto.
  }

  {
    introv.
    pose proof (h r) as q; simpl in q; clear h.
    rewrite lookup_pred_uniform_substitution_restriction_program_in in q; auto.
  }

  {
    introv h1 h2.
    pose proof (h v0 w0 f0 g h1 h2) as q; simpl in q; clear h.
    rewrite lookup_quant_uniform_substitution_restriction_program_in in q; auto.
  }

  {
    dands; auto.
    introv q.
    apply ext_dynamic_semantics_ode_fun; auto.
  }

  {
    introv h1 h2.
    pose proof (h v1 v2 w1 w2 h1 h2) as q; simpl in q; clear h.
    rewrite lookup_const_uniform_substitution_restriction_program_in in q; auto.
  }
Qed.

Lemma find_function_in_uniform_substitution_implies_subset_free_vars :
  forall s f n t,
    find_function_in_uniform_substitution s f n = Some t
    -> eassignables_subset
         (EA_assignables (free_vars_term t))
         (free_vars_uniform_substitution s) = true.
Proof.
  induction s; introv h; simpl in *; ginv.
  destruct a; simpl in *; repeat (dest_cases w; subst; ginv).

  {
    remember (free_vars_uniform_substitution s) as e; destruct e.
    - apply included_dec_prop; introv i; apply in_app_iff; tcsp.
    - apply disj_dec_prop; introv i j; apply in_KAssignables_minus in j; tcsp.
  }

  {
    apply IHs in h.
    remember (free_vars_uniform_substitution s) as e; destruct e.
    - allrw @included_dec_prop; introv i; apply in_app_iff; tcsp.
    - allrw @disj_dec_prop; introv i j; apply in_KAssignables_minus in j; repnd.
      apply h in j0; tcsp.
  }

  {
    apply IHs in h.
    remember (free_vars_uniform_substitution s) as e; destruct e.
    - allrw @included_dec_prop; introv i; apply in_app_iff; tcsp.
    - allrw @disj_dec_prop; introv i j; apply in_KAssignables_minus in j; repnd.
      apply h in j0; tcsp.
  }

  {
    apply IHs in h.
    remember (free_vars_formula f0) as e; destruct e; simpl;
      remember (free_vars_uniform_substitution s) as e; destruct e; simpl.
    - allrw @included_dec_prop; introv i; apply in_app_iff; tcsp.
    - allrw @disj_dec_prop; introv i j; apply in_KAssignables_minus in j; repnd.
      apply h in j0; tcsp.
    - allrw @included_dec_prop.
      allrw @disj_dec_prop; introv i j; apply h in i.
      apply in_KAssignables_minus in j; tcsp.
    - allrw @disj_dec_prop; introv i j; apply h in i.
      apply in_KAssignables_inter in j; tcsp.
  }

  {
    apply IHs in h.
    remember (free_vars_formula f0) as e; destruct e; simpl;
      remember (free_vars_uniform_substitution s) as e; destruct e; simpl.
    - allrw @included_dec_prop; introv i; apply h in i; auto.
    - allrw @disj_dec_prop; introv i j; apply in_KAssignables_minus in j; repnd.
      apply h in j0; tcsp.
    - allrw @included_dec_prop; auto.
    - autorewrite with core.
      allrw @disj_dec_prop; introv i j; apply h in i; tcsp.
  }

  {
    apply IHs in h.
    remember (free_vars_program p0) as e; destruct e; simpl;
      remember (free_vars_uniform_substitution s) as e; destruct e; simpl.
    - allrw @included_dec_prop; introv i; apply h in i; auto.
    - allrw @disj_dec_prop; introv i j; apply in_KAssignables_minus in j; repnd.
      apply h in j0; tcsp.
    - allrw @included_dec_prop; auto.
    - autorewrite with core.
      allrw @disj_dec_prop; introv i j; apply h in i; tcsp.
  }

  {
    apply IHs in h.
    remember (free_vars_ode o0) as e; destruct e; simpl;
      remember (free_vars_uniform_substitution s) as e; destruct e; simpl.
    - allrw @included_dec_prop; introv i; apply h in i; auto.
    - allrw @disj_dec_prop; introv i j; apply in_KAssignables_minus in j; repnd.
      apply h in j0; tcsp.
    - allrw @included_dec_prop; auto.
    - autorewrite with core.
      allrw @disj_dec_prop; introv i j; apply h in i; tcsp.
  }
Qed.

Lemma find_predicate_in_uniform_substitution_implies_subset_free_vars :
  forall s f n t,
    find_predicate_in_uniform_substitution s f n = Some t
    -> eassignables_subset
         (free_vars_formula t)
         (free_vars_uniform_substitution s) = true.
Proof.
  induction s; introv h; simpl in *; ginv.
  destruct a; simpl in *; repeat (dest_cases w; subst; ginv).

  {
    apply IHs in h.
    eapply eassignables_subset_trans;[exact h|]; clear h.
    remember (free_vars_uniform_substitution s) as e; destruct e; simpl;
      apply included_dec_prop; introv i; allrw in_app_iff; tcsp.
    apply in_KAssignables_minus in i; tcsp.
  }

  {
    apply implies_eassignables_subset_app_r_true; left.
    apply eassignables_subset_refl.
  }

  {
    apply IHs in h.
    eapply eassignables_subset_trans;[exact h|]; clear h.
    apply implies_eassignables_subset_app_r_true; right.
    apply eassignables_subset_refl.
  }

  {
    apply IHs in h.
    eapply eassignables_subset_trans;[exact h|]; clear h.
    apply implies_eassignables_subset_app_r_true; right.
    apply eassignables_subset_refl.
  }

  {
    apply IHs in h.
    eapply eassignables_subset_trans;[exact h|]; clear h.
    remember (free_vars_uniform_substitution s) as k;
      destruct k; autorewrite with core; auto.
  }

  {
    apply IHs in h.
    eapply eassignables_subset_trans;[exact h|]; clear h.
    remember (free_vars_uniform_substitution s) as k;
      destruct k; autorewrite with core; auto.
  }

  {
    apply IHs in h.
    eapply eassignables_subset_trans;[exact h|]; clear h.
    remember (free_vars_uniform_substitution s) as k;
      destruct k; autorewrite with core; auto.
  }
Qed.

Lemma vec_flatten_map_free_vars_term_vec_const_n_dot :
  forall n m,
    vec_flatten (Vector.map free_vars_term (vec_const_n n m KTdot))
    = [].
Proof.
  induction n; simpl; auto.
Qed.

Lemma vec_flatten_map_term_variables_vec_const_n_dot :
  forall n m,
    vec_flatten (Vector.map term_variables (vec_const_n n m KTdot))
    = [].
Proof.
  induction n; simpl; auto.
Qed.

Lemma vec_flatten_map_free_vars_term_vec_const_dot :
  forall n,
    vec_flatten (Vector.map free_vars_term (vec_const n KTdot))
    = [].
Proof.
  introv; apply vec_flatten_map_free_vars_term_vec_const_n_dot.
Qed.
Hint Rewrite vec_flatten_map_free_vars_term_vec_const_dot : core.

Lemma vec_flatten_map_term_variables_vec_const_dot :
  forall n,
    vec_flatten (Vector.map term_variables (vec_const n KTdot))
    = [].
Proof.
  introv; apply vec_flatten_map_term_variables_vec_const_n_dot.
Qed.
Hint Rewrite vec_flatten_map_term_variables_vec_const_dot : core.

(** Admissible adjoints for states --- see Corollary 6, Section 3.1 *)
Lemma substitution_adjoint_state :
  forall v w s I,
    equal_states_on_ea v w (free_vars_uniform_substitution s)
    -> ext_interpretations
         (adjoint_interpretation s I v)
         (adjoint_interpretation s I w).
Proof.
  introv eqse; introv.
  destruct s0; simpl; tcsp.

  {
    introv.
    apply coincidence_term; eauto 3 with core;[].
    apply equal_states_on_ea_assigns2ext.
    eapply equal_states_on_ea_eassignables_subset;[|exact eqse].
    unfold lookup_func.
    remember (find_function_in_uniform_substitution s f n) as ff;
      destruct ff;
      symmetry in Heqff; simpl;
        remember (free_vars_uniform_substitution s) as e; destruct e; auto;
          try (applydup find_function_in_uniform_substitution_implies_subset_free_vars in Heqff;
               rewrite <- Heqe in Heqff0; simpl in Heqff0; auto);
              autorewrite with core; auto.
  }

  {
    introv.
    apply coincidence_formula; eauto 3 with core;[].
    eapply equal_states_on_ea_eassignables_subset;[|exact eqse].
    unfold lookup_pred.
    remember (find_predicate_in_uniform_substitution s f n) as ff; destruct ff;
      symmetry in Heqff; simpl; autorewrite with core; simpl;
        [|destruct (free_vars_uniform_substitution s); auto];[].
    apply find_predicate_in_uniform_substitution_implies_subset_free_vars in Heqff.
    eapply eassignables_subset_trans;[exact Heqff|].
    eauto 3 with core.
  }

  {
    introv h1 h2.
    apply coincidence_formula; eauto 3 with core.

    { introv h; auto. }

    {
      apply ext_interpretations_implies_equal_interpretations_on_ext.
      apply ext_interpretations_upd_interpretation_dot_form; auto.
    }
  }

  {
    introv h.
    (* make interpretations more extensional to get rid of functional_extensionality *)
    assert (v0 = w0) as xx by (apply functional_extensionality; auto).
    subst; tcsp.
  }

  { dands; auto.
    introv h.
    apply ext_dynamic_semantics_ode_fun; auto.
  }

  {
    introv h1 h2.
    (* make interpretations more extensional to get rid of functional_extensionality *)
    assert (v1 = v2) as xx1 by (apply functional_extensionality; auto).
    assert (w1 = w2) as xx2 by (apply functional_extensionality; auto).
    subst; clear h1 h2.
    remember (find_const_in_uniform_substitution s a) as fc;
      symmetry in Heqfc; destruct fc; simpl; tcsp.
  }
Qed.


Lemma free_vars_uniform_substitution_uniform_substitution_restriction_term_subset :
  forall s t,
    eassignables_subset
      (free_vars_sub_restrict_term s t)
      (free_vars_uniform_substitution s)
    = true.
Proof.
  induction s; introv; simpl; auto.
  unfold free_vars_sub_restrict_term in *; simpl; auto.
  destruct (uniform_substitution_entry_in_term a t); simpl.

  {
    apply eassignables_subset_app_l_true_iff; dands;
      apply implies_eassignables_subset_app_r_true; tcsp.
  }

  {
    apply implies_eassignables_subset_app_r_true; tcsp.
  }
Qed.


Lemma free_vars_uniform_substitution_uniform_substitution_restriction_program_subset :
  forall s p,
    eassignables_subset
      (free_vars_sub_restrict_program s p)
      (free_vars_uniform_substitution s)
    = true.
Proof.
  induction s; introv; simpl; auto.
  unfold free_vars_sub_restrict_program in *; simpl; auto.
  destruct (uniform_substitution_entry_in_program a p); simpl.

  {
    apply eassignables_subset_app_l_true_iff; dands;
      apply implies_eassignables_subset_app_r_true; tcsp.
  }

  {
    apply implies_eassignables_subset_app_r_true; tcsp.
  }
Qed.

Lemma U_admissible_and_complement_implies_restrict_term :
  forall U t s v w,
    U_admissible_term U t s = true
    -> equal_states_on_complement v w U
    -> equal_states_on_ea v w (free_vars_sub_restrict_term s t).
Proof.
  introv adm eqs.
  introv j.
  apply eqs.
  remember (in_eassignables x U) as b; destruct b; auto;[]; symmetry in Heqb.
  eapply eassignables_disj_prop in adm;[|exact Heqb]; tcsp.
Qed.

Lemma U_admissible_and_complement_implies_restrict_formula :
  forall U f s v w,
    U_admissible_formula U f s = true
    -> equal_states_on_complement v w U
    -> equal_states_on_ea v w (free_vars_sub_restrict_formula s f).
Proof.
  introv adm eqs.
  introv j.
  apply eqs.
  remember (in_eassignables x U) as b; destruct b; auto;[]; symmetry in Heqb.
  eapply eassignables_disj_prop in adm;[|exact Heqb]; tcsp.
Qed.

Lemma U_admissible_and_complement_implies_restrict_program :
  forall U p s v w,
    U_admissible_program U p s = true
    -> equal_states_on_complement v w U
    -> equal_states_on_ea v w (free_vars_sub_restrict_program s p).
Proof.
  introv adm eqs.
  introv j.
  apply eqs.
  remember (in_eassignables x U) as b; destruct b; auto;[]; symmetry in Heqb.
  eapply eassignables_disj_prop in adm;[|exact Heqb]; tcsp.
Qed.

Lemma substitution_adjoint_admissible_term0 :
  forall t s v w I st,
  equal_states_on_ea v w (free_vars_sub_restrict_term s t)
  -> dynamic_semantics_term (adjoint_interpretation s I v) st t
     = dynamic_semantics_term (adjoint_interpretation s I w) st t.
Proof.
  introv eqs.
  apply coincidence_term; auto; try (apply equal_states_on_refl).
  introv i.
  eapply substitution_adjoint_state in eqs.
  eapply ext_interpretations_at_adjoint_interpretation_uniform_substitution_restriction_term; eauto.
Qed.


(** Admissible adjoints for terms --- see Corollary 6, Section 3.1 *)
Lemma substitution_adjoint_admissible_term:
  forall U t s v w I st,
  U_admissible_term U t s = true
  -> equal_states_on_complement v w U
  -> dynamic_semantics_term (adjoint_interpretation s I v) st t
     = dynamic_semantics_term (adjoint_interpretation s I w) st t.
Proof.
  introv adm eqs.
  apply substitution_adjoint_admissible_term0.
  eapply U_admissible_and_complement_implies_restrict_term; eauto.
Qed.

Lemma substitution_adjoint_admissible_formula0 :
  forall f s v w I st,
  equal_states_on_ea v w (free_vars_sub_restrict_formula s f)
  -> dynamic_semantics_formula (adjoint_interpretation s I v) f st
     <-> dynamic_semantics_formula (adjoint_interpretation s I w) f st.
Proof.
  introv eqs.
  apply coincidence_formula; auto; try (apply equal_states_on_refl).
  introv i.
  eapply substitution_adjoint_state in eqs.
  eapply ext_interpretations_at_adjoint_interpretation_uniform_substitution_restriction_formula; eauto.
Qed.

(** Admissible adjoints for formulas --- see Corollary 6, Section 3.1 *)
Lemma substitution_adjoint_admissible_formula:
  forall U f s v w I st,
  U_admissible_formula U f s = true
  -> equal_states_on_complement v w U
  -> dynamic_semantics_formula (adjoint_interpretation s I v) f st
     <-> dynamic_semantics_formula (adjoint_interpretation s I w) f st.
Proof.
  introv adm eqs.
  apply substitution_adjoint_admissible_formula0.
  eapply U_admissible_and_complement_implies_restrict_formula; eauto.
Qed.

Lemma dynamic_semantics_ode_if_equal_interpretations_on_ext :
  forall I J ode r phi,
    equal_interpretations_on_ext I J (ode_signature ode)
    -> dynamic_semantics_ode I ode r phi
    -> dynamic_semantics_ode J ode r phi.
Proof.
  introv eqs ds i; simpl in *.
  applydup equal_interpretations_on_ext_ode_signature_implies_eqset_ode_vars in eqs.
  apply eqs0 in i.
  apply (ds zeta) in i; simpl in i; repnd; dands; auto.
  rewrite i.
  apply equal_interpretations_on_ext_implies_eq_dynamic_semantics_ode_fun; auto.
Qed.

Lemma dynamic_semantics_program_equal_interpretations_on_ext :
  forall p I J v w,
    equal_interpretations_on_ext I J (program_signature p)
    -> dynamic_semantics_program I p v w
    -> dynamic_semantics_program J p v w.
Proof.
  prog_ind p Case; introv eqi dsp; simpl in *; auto.

  { Case "KPconstant".
    apply equal_interpretations_on_ext_cons in eqi; repnd.
    simpl in eqi0.
    eapply eqi0;try (exact dsp); auto.
  }

  { Case "KPassign".
    erewrite coincidence_term; try (exact dsp); auto.
    apply equal_interpretations_on_ext_sym; auto.
  }

  { Case "KPtest".
    repnd; subst; dands; auto.
    eapply coincidence_formula; try (exact dsp); auto.
    apply equal_interpretations_on_ext_sym; auto.
  }

  { Case "KPchoice".
    apply equal_interpretations_on_ext_app in eqi; repnd.
    repndors.
    { eapply IHp1 in dsp; try (exact eqi0); tcsp. }
    { eapply IHp2 in dsp; try (exact eqi); tcsp. }
  }

  { Case "KPcompose".
    apply equal_interpretations_on_ext_app in eqi; repnd.
    exrepnd.
    eapply IHp1 in dsp1; try (exact eqi0).
    eapply IHp2 in dsp0; try (exact eqi).
    eexists; dands; eauto.
  }

  { Case "KPloop".
    allrw program_close_implies_all.
    exrepnd.
    exists n.

    revert w dsp0.
    induction n; introv dsp; simpl in *; auto.
    exrepnd.
    exists s; dands; auto.
    eapply IHp; eauto.
  }

  { Case "KPodeSystem".
    exrepnd; subst.
    apply equal_interpretations_on_ext_app in eqi; repnd.
    exists r phi; dands; auto.

    {
      introv i; apply dsp0; intro xx.
      apply eqset_ode_footprint_diff_if_equal_interpretations_on_ext in eqi0.
      apply eqi0 in xx; auto.
    }

    { eapply dynamic_semantics_ode_if_equal_interpretations_on_ext; eauto. }

    {
      introv.
      pose proof (dsp1 zeta) as q; repnd; dands; auto.
      { eapply coincidence_formula; try (exact q0); auto.
        apply equal_interpretations_on_ext_sym; auto. }
      { introv i ;apply q; intro xx.
        apply eqset_ode_footprint_if_equal_interpretations_on_ext in eqi0.
        apply eqi0 in xx; auto. }
    }
  }
Qed.

Lemma substitution_adjoint_admissible_program0 :
  forall p s v w I v1 v2,
  equal_states_on_ea v w (free_vars_sub_restrict_program s p)
  -> dynamic_semantics_program (adjoint_interpretation s I v) p v1 v2
  -> dynamic_semantics_program (adjoint_interpretation s I w) p v1 v2.
Proof.
  introv eqs dsp.

  eapply dynamic_semantics_program_equal_interpretations_on_ext;
    try (exact dsp); clear dsp.

  introv i.
  eapply substitution_adjoint_state in eqs.
  eapply ext_interpretations_at_adjoint_interpretation_uniform_substitution_restriction_program; eauto.
Qed.

Lemma equal_states_on_complement_sym :
  forall v w U,
    equal_states_on_complement v w U
    -> equal_states_on_complement w v U.
Proof.
  introv eqs i; symmetry; apply eqs; auto.
Qed.

(** Admissible adjoints for programss --- see Corollary 6, Section 3.1 *)
Lemma substitution_adjoint_admissible_program :
  forall p U s v w I v1 v2,
    U_admissible_program U p s = true
    -> equal_states_on_complement v w U
    -> dynamic_semantics_program (adjoint_interpretation s I v) p v1 v2
       <-> dynamic_semantics_program (adjoint_interpretation s I w) p v1 v2.
Proof.
  introv adm eqs.

  split; introv dsp.

  { eapply substitution_adjoint_admissible_program0; try (exact dsp).
    eapply U_admissible_and_complement_implies_restrict_program; eauto. }

  { eapply substitution_adjoint_admissible_program0; try (exact dsp).
    eapply U_admissible_and_complement_implies_restrict_program; eauto.
    apply equal_states_on_complement_sym; auto. }
Qed.

(*
Lemma fold_dst :
  forall t I,
    DSD_F (dynamic_semantics_term_diff t I)
    = dynamic_semantics_term t I.
Proof.
  tcsp.
Qed.

Ltac dstf w :=
  match goal with
  | [ |- context[dynamic_semantics_term_diff ?t ?I] ] =>
    remember (dynamic_semantics_term_diff t I) as w;
    destruct w;
    simpl in *;
    match goal with
    | [ H : _ = dynamic_semantics_term_diff t I |- _ ] =>
      apply (@f_equal _ _ dynamic_semantics.DSD_F) in H;
      simpl in *;
      try (rewrite fold_dst in H)
    end
  | [ H : context[dynamic_semantics_term_diff ?t ?I] |- _ ] =>
    remember (dynamic_semantics_term_diff t I) as w;
    destruct w;
    simpl in *;
    match goal with
    | [ H : _ = dynamic_semantics_term_diff t I |- _ ] =>
      apply (@f_equal _ _ dynamic_semantics.DSD_F) in H;
      simpl in *;
      try (rewrite fold_dst in H)
    end
  end.

Ltac dstft t w :=
  match goal with
  | [ |- context[dynamic_semantics_term_diff t ?I] ] =>
    remember (dynamic_semantics_term_diff t I) as w;
    destruct w;
    simpl in *;
    match goal with
    | [ H : _ = dynamic_semantics_term_diff t I |- _ ] =>
      apply (@f_equal _ _ dynamic_semantics.DSD_F) in H;
      simpl in *;
      try (rewrite fold_dst in H)
    end
  | [ H : context[dynamic_semantics_term_diff t ?I] |- _ ] =>
    remember (dynamic_semantics_term_diff t I) as w;
    destruct w;
    simpl in *;
    match goal with
    | [ H : _ = dynamic_semantics_term_diff t I |- _ ] =>
      apply (@f_equal _ _ dynamic_semantics.DSD_F) in H;
      simpl in *;
      try (rewrite fold_dst in H)
    end
  end.
*)

Ltac dest_sub w :=
  match goal with
  | [ |- context[substitution_dot_term ?t ?u] ] =>
    remember (substitution_dot_term t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dot_term ?t ?u] |- _ ] =>
    remember (substitution_dot_term t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dots_term ?t ?u] ] =>
    remember (substitution_dots_term t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dots_term ?t ?u] |- _ ] =>
    remember (substitution_dots_term t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dot_term_in_formula ?t ?u] ] =>
    remember (substitution_dot_term_in_formula t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dot_term_in_formula ?t ?u] |- _ ] =>
    remember (substitution_dot_term_in_formula t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dots_term_in_formula ?t ?u] ] =>
    remember (substitution_dots_term_in_formula t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dots_term_in_formula ?t ?u] |- _ ] =>
    remember (substitution_dots_term_in_formula t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dot_term_in_program ?t ?u] ] =>
    remember (substitution_dot_term_in_program t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dot_term_in_program ?t ?u] |- _ ] =>
    remember (substitution_dot_term_in_program t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dots_term_in_program ?t ?u] ] =>
    remember (substitution_dots_term_in_program t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dots_term_in_program ?t ?u] |- _ ] =>
    remember (substitution_dots_term_in_program t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dot_term_in_atomic_ode ?t ?u] ] =>
    remember (substitution_dot_term_in_atomic_ode t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dot_term_in_atomic_ode ?t ?u] |- _ ] =>
    remember (substitution_dot_term_in_atomic_ode t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dots_term_in_atomic_ode ?t ?u] ] =>
    remember (substitution_dots_term_in_atomic_ode t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dots_term_in_atomic_ode ?t ?u] |- _ ] =>
    remember (substitution_dots_term_in_atomic_ode t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dot_term_in_ode ?t ?u] ] =>
    remember (substitution_dot_term_in_ode t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dot_term_in_ode ?t ?u] |- _ ] =>
    remember (substitution_dot_term_in_ode t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dots_term_in_ode ?t ?u] ] =>
    remember (substitution_dots_term_in_ode t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dots_term_in_ode ?t ?u] |- _ ] =>
    remember (substitution_dots_term_in_ode t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dot_formula_in_formula ?t ?u] ] =>
    remember (substitution_dot_formula_in_formula t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dot_formula_in_formula ?t ?u] |- _ ] =>
    remember (substitution_dot_formula_in_formula t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dot_formula_in_program ?t ?u] ] =>
    remember (substitution_dot_formula_in_program t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dot_formula_in_program ?t ?u] |- _ ] =>
    remember (substitution_dot_formula_in_program t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[uniform_substitution_term ?t ?s] ] =>
    remember (uniform_substitution_term t s) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[uniform_substitution_term ?t ?s] |- _ ] =>
    remember (uniform_substitution_term t s) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[uniform_substitution_formula ?t ?s] ] =>
    remember (uniform_substitution_formula t s) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[uniform_substitution_formula ?t ?s] |- _ ] =>
    remember (uniform_substitution_formula t s) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[uniform_substitution_program ?t ?s] ] =>
    remember (uniform_substitution_program t s) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[uniform_substitution_program ?t ?s] |- _ ] =>
    remember (uniform_substitution_program t s) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[uniform_substitution_atomic_ode ?t ?s] ] =>
    remember (uniform_substitution_atomic_ode t s) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[uniform_substitution_atomic_ode ?t ?s] |- _ ] =>
    remember (uniform_substitution_atomic_ode t s) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[uniform_substitution_ode ?t ?s] ] =>
    remember (uniform_substitution_ode t s) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[uniform_substitution_ode ?t ?s] |- _ ] =>
    remember (uniform_substitution_ode t s) as w;
    destruct w;
    simpl in *;
    auto
  end.

Definition tvec_nth1 {n} (v : Vector.t Term n) m := vec_nth v m DTD.
Definition tvec_nth2 {n} (v : Vector.t Term n) m := vec_nth v m DTN.

Lemma free_vars_substitution_dot_term_if_null :
  forall u t z,
    null (free_vars_term u)
    -> substitution_dot_term t u = Some z
    -> free_vars_term t = free_vars_term z.
Proof.
  term_ind t Case; simpl; introv nl e; unfold ret in *; ginv; tcsp;
    try (complete (dest_sub w; ginv; simpl; eapply IHt; eauto));
    try (complete (dest_sub w; ginv; dest_sub y; ginv; simpl;
                   erewrite IHt1; eauto; erewrite IHt2; eauto)).

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a => substitution_dot_term a u) args)) as opv.
    destruct opv; symmetry in Heqopv; simpl in *; ginv; simpl.
    f_equal.
    apply (eq_vec_map2 DTN); introv ltmn.
    pose proof (vec_opt2opt_vec_map_some_implies_some
                  args t
                  (fun a => substitution_dot_term a u)
                  m DTN) as q.
    simpl in q; repeat (autodimp q hyp).
    remember (substitution_dot_term (vec_nth args m DTN) u) as opt.
    destruct opt; tcsp; subst.
    apply IHargs; auto.
  }

  { Case "KTdifferential".
    unfold on_test in e.
    dest_cases w.
    clear Heqw.
    dest_sub x; ginv.
    erewrite IHt; eauto.
    simpl; auto. }
Qed.

Lemma null_free_vars_term_implies_null_term_variables :
  forall t,
    null (free_vars_term t)
    -> null (term_variables t).
Proof.
  introv n.
  remember (term_variables t) as l; destruct l; unfold null; simpl; auto.
  pose proof (term_variables_subset_free_vars_term k t) as h.
  rewrite <- Heql in h; simpl in h; autodimp h hyp.
  rewrite n in h; simpl in h; tcsp.
Qed.

Lemma term_variables_substitution_dot_term_if_null :
  forall u t z,
    null (free_vars_term u)
    -> substitution_dot_term t u = Some z
    -> term_variables t = term_variables z.
Proof.
  term_ind t Case; simpl; introv nl e; unfold ret in *; ginv; tcsp;
    try (complete (dest_sub w; ginv; simpl; eapply IHt; eauto));
    try (complete (dest_sub w; ginv; dest_sub y; ginv; simpl;
                   erewrite IHt1; eauto; erewrite IHt2; eauto)).

  { Case "KTdot".
    apply null_free_vars_term_implies_null_term_variables in nl; auto. }

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a => substitution_dot_term a u) args)) as opv.
    destruct opv; symmetry in Heqopv; simpl in *; ginv; simpl.
    f_equal.
    apply (eq_vec_map2 DTN); introv ltmn.
    pose proof (vec_opt2opt_vec_map_some_implies_some
                  args t
                  (fun a => substitution_dot_term a u)
                  m DTN) as q.
    simpl in q; repeat (autodimp q hyp).
    remember (substitution_dot_term (vec_nth args m DTN) u) as opt.
    destruct opt; tcsp; subst.
    apply IHargs; auto.
  }

  { Case "KTdifferential".
    unfold on_test in e.
    dest_cases w.
    clear Heqw.
    dest_sub x; ginv.
    simpl.
    erewrite IHt; eauto. }
Qed.

Lemma equal_states_on_nil :
  forall v w, equal_states_on v w [].
Proof.
  introv i; allsimpl; tcsp.
Qed.
Hint Resolve equal_states_on_nil : core.

Lemma fold_term_variables_nodup :
  forall t,
    remove_duplicates KVariable_dec (term_variables t)
    = term_variables_nodup t.
Proof.
  auto.
Qed.

Lemma fold_free_vars_term_nodup :
  forall t,
    remove_duplicates KAssignable_dec (free_vars_term t)
    = term_assignables_nodup t.
Proof.
  auto.
Qed.

Lemma U_admissible_term_all_implies :
  forall t s,
    U_admissible_term (EA_all []) t s = true
    -> free_vars_sub_restrict_term s t = EA_assignables [].
Proof.
  introv adm.
  unfold U_admissible_term in adm; simpl in *.
  remember (free_vars_sub_restrict_term s t) as fvs;
    destruct fvs; unfold eassignables_disj in *; simpl in *; tcsp.
  apply included_dec_nil_implies in adm; subst; auto.
Qed.

Lemma equal_states_on_ea_nil :
  forall s1 s2 : state,
    equal_states_on_ea s1 s2 (EA_assignables []).
Proof.
  introv i.
  simpl in i; tcsp.
Qed.

Lemma free_vars_term_substitution_dot_term_if_null :
  forall u t z,
    null (free_vars_term u)
    -> substitution_dot_term t u = Some z
    -> free_vars_term t = free_vars_term z.
Proof.
  term_ind t Case; simpl; introv nl e; unfold ret in *; ginv; tcsp;
    try (complete (dest_sub w; ginv; simpl; eapply IHt; eauto));
    try (complete (dest_sub w; ginv; dest_sub y; ginv; simpl;
                   erewrite IHt1; eauto; erewrite IHt2; eauto)).

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a => substitution_dot_term a u) args)) as opv.
    destruct opv; symmetry in Heqopv; simpl in *; ginv; simpl.
    f_equal.
    apply (eq_vec_map2 DTN); introv ltmn.
    pose proof (vec_opt2opt_vec_map_some_implies_some
                  args t
                  (fun a => substitution_dot_term a u)
                  m DTN) as q.
    simpl in q; repeat (autodimp q hyp).
    remember (substitution_dot_term (vec_nth args m DTN) u) as opt.
    destruct opt; tcsp; subst.
    apply IHargs; auto.
  }

  { Case "KTdifferential".
    unfold on_test in e.
    dest_cases w.
    clear Heqw.
    dest_sub x; ginv.
    simpl.
    erewrite IHt; eauto. }
Qed.

Lemma substitution_dot_term_if_no_dot :
  forall t u v,
    containsDot t = false
    -> substitution_dot_term t u = Some v
    -> t = v.
Proof.
  term_ind t Case; introv cd s; simpl in *; unfold ret in *; ginv;
    try (complete (dest_sub w; ginv; symmetry in Heqw;
                   apply IHt in Heqw; subst; auto));
    try (complete (dest_sub w; symmetry in Heqw; ginv;
                   dest_sub z; symmetry in Heqz; ginv;
                   apply orb_false_iff in cd; repnd;
                   apply IHt1 in Heqw; auto;
                   apply IHt2 in Heqz; auto;
                   subst; auto)).

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => substitution_dot_term a u) args)) as opv.
    destruct opv; symmetry in Heqopv; simpl in *; ginv; simpl.
    f_equal.
    induction n.

    { apply Vector.case0 with (v := args).
      apply Vector.case0 with (v := t); auto. }

    { revert dependent args; intro args.
      apply (Vector.caseS' args); introv.
      revert dependent t; intro t.
      apply (Vector.caseS' t); introv; simpl.
      introv ih e q.
      apply orb_false_iff in e; repnd.
      remember (substitution_dot_term h u) as sdt; symmetry in Heqsdt.
      destruct sdt; ginv.
      remember (vec_opt2opt_vec (Vector.map (fun a : Term => substitution_dot_term a u) t0)) as vopt.
      symmetry in Heqvopt; destruct vopt; simpl in *; ginv.
      pose proof (IHn t0) as z; clear IHn.
      autodimp z hyp.
      { introv h1 h2 h3.
        eapply ih;[| |eauto]; auto.
        constructor; auto. }
      autodimp z hyp.
      pose proof (z t3) as w; clear z.
      autodimp w hyp; subst.
      apply ih in Heqsdt; auto;[|constructor; auto]; subst.
      inversion q; eqDepDec; subst; auto. }
  }

  { Case "KTdifferential".
    unfold on_test in s.
    dest_cases fv; symmetry in Heqfv.
    apply nullb_prop in Heqfv.
    dest_sub x; ginv; symmetry in Heqx.
    unfold free_vars_term_restrict_term in Heqfv.
    dest_cases w; ginv.
    apply IHt in Heqx; subst; auto. }
Qed.

Lemma substitution_dots_term_if_no_dot :
  forall t {n} (u : Vector.t Term n) v,
    containsDot t = false
    -> substitution_dots_term t u = Some v
    -> t = v.
Proof.
  term_ind t Case; introv cd s; simpl in *; unfold ret in *; ginv;
    try (complete (dest_sub w; ginv; symmetry in Heqw;
                   apply IHt in Heqw; subst; auto));
    try (complete (dest_sub w; symmetry in Heqw; ginv;
                   dest_sub z; symmetry in Heqz; ginv;
                   apply orb_false_iff in cd; repnd;
                   apply IHt1 in Heqw; auto;
                   apply IHt2 in Heqz; auto;
                   subst; auto)).

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => substitution_dots_term a u) args)) as opv.
    destruct opv; symmetry in Heqopv; simpl in *; ginv; simpl.
    f_equal.
    induction n.

    { apply Vector.case0 with (v := args).
      apply Vector.case0 with (v := t); auto. }

    { revert dependent args; intro args.
      apply (Vector.caseS' args); introv.
      revert dependent t; intro t.
      apply (Vector.caseS' t); introv; simpl.
      introv ih e q.
      apply orb_false_iff in e; repnd.
      remember (substitution_dots_term h u) as sdt; symmetry in Heqsdt.
      destruct sdt; ginv.
      remember (vec_opt2opt_vec (Vector.map (fun a : Term => substitution_dots_term a u) t0)) as vopt.
      symmetry in Heqvopt; destruct vopt; simpl in *; ginv.
      pose proof (IHn t0) as z; clear IHn.
      autodimp z hyp.
      { introv h1 h2 h3.
        eapply ih;[| |eauto]; auto.
        constructor; auto. }
      autodimp z hyp.
      pose proof (z t3) as w; clear z.
      autodimp w hyp; subst.
      apply ih in Heqsdt; auto;[|constructor; auto]; subst.
      inversion q; eqDepDec; subst; auto. }
  }

  { Case "KTdifferential".
    unfold on_test in s.
    dest_cases fv; symmetry in Heqfv.
    apply nullb_prop in Heqfv.
    dest_sub x; ginv; symmetry in Heqx.
    unfold free_vars_vec_term_restrict_term in Heqfv.
    dest_cases w; ginv.
    apply IHt in Heqx; subst; auto. }
Qed.

Lemma vec2bool_map_false_implies :
  forall {A} b {n} m (v : Vector.t A n) (F : A -> bool),
    m < n
    -> vec2bool (Vector.map F v) = false
    -> F (vec_nth v m b) = false.
Proof.
  induction n; introv ltmn; try omega.
  apply (Vector.caseS' v); introv; clear v.
  simpl.
  intro hyp.
  apply orb_false_iff in hyp; repnd.
  destruct m; auto.
  apply IHn; auto; omega.
Qed.

Lemma vec2bool_map_false_implies2 :
  forall {A} {n} (v : Vector.t A n) (F : A -> bool) a,
    Vector.In a v
    -> vec2bool (Vector.map F v) = false
    -> F a = false.
Proof.
  induction n; introv i e; try omega.

  { revert dependent v; intro v.
    apply Vector.case0 with (v := v).
    introv i e.
    inversion i. }

  { revert dependent v; intro v.
    apply (Vector.caseS' v); introv i e; clear v.
    simpl in *.
    apply orb_false_iff in e; repnd.
    inversion i; eqDepDec; subst; ginv.
    eapply IHn; eauto. }
Qed.

Lemma dynamic_semantics_term_upd_interpretation_dot_if_not_dot :
  forall t I r1 r2 v,
    containsDot t = false
    -> dynamic_semantics_term (upd_interpretation_dot I r1) v t
       = dynamic_semantics_term (upd_interpretation_dot I r2) v t.
Proof.
  term_ind t Case; introv cd; simpl in *; ginv;
    try (complete (f_equal; auto));
    try (complete (apply orb_false_iff in cd; repnd; f_equal; auto)).

  { Case "KTfuncOf".
    f_equal.
    apply eq_vec_map; introv i.
    apply IHargs; auto.
    eapply vec2bool_map_false_implies2 in cd;[|eauto]; auto. }

  { Case "KTdifferential".
    apply big_sum_ext; introv i.
    f_equal.
    apply Derive_ext; introv.
    apply IHt; auto. }
Qed.

Lemma dynamic_semantics_term_upd_interpretation_dots_if_not_dot :
  forall t I {n} (r1 r2 : Vector.t R n) v,
    containsDot t = false
    -> dynamic_semantics_term (upd_interpretation_dots I r1) v t
       = dynamic_semantics_term (upd_interpretation_dots I r2) v t.
Proof.
  term_ind t Case; introv cd; simpl in *; ginv;
    try (complete (f_equal; auto));
    try (complete (apply orb_false_iff in cd; repnd; f_equal; auto)).

  { Case "KTfuncOf".
    f_equal.
    apply eq_vec_map; introv i.
    apply IHargs; auto.
    eapply vec2bool_map_false_implies2 in cd;[|eauto]; auto. }

  { Case "KTdifferential".
    apply big_sum_ext; introv i.
    f_equal.
    apply Derive_ext; introv.
    apply IHt; auto. }
Qed.

Lemma dynamic_semantics_term_substitution_dot_term :
  forall t u I v,
    on_substitution_dot_term
      t u
      (fun x =>
         dynamic_semantics_term I v x
         = dynamic_semantics_term
             (upd_interpretation_dot I (dynamic_semantics_term I v u)) v t).
Proof.
  term_ind t Case;
    unfold on_substitution_dot_term in *;
    introv; simpl; tcsp;
      try (complete (pose proof (IHt u I v) as h; clear IHt;
                     dest_sub x; congruence));
      try (complete (pose proof (IHt1 u I v) as h1; clear IHt1;
                     pose proof (IHt2 u I v) as h2; clear IHt2;
                     dest_sub x; dest_sub y; congruence)).

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => substitution_dot_term a u) args)) as opv.
    destruct opv; symmetry in Heqopv; simpl in *; ginv; simpl.
    f_equal.
    apply (eq_vec_map2 DTN); introv ltmn.
    pose proof (vec_opt2opt_vec_map_some_implies_some
                  args t
                  (fun a => substitution_dot_term a u)
                  m DTN) as q.
    simpl in q; repeat (autodimp q hyp).
    remember (substitution_dot_term (vec_nth args m DTN) u) as opt.
    destruct opt; tcsp; subst.
    pose proof (IHargs (vec_nth args m DTN)) as q; clear IHargs.
    autodimp q hyp.
    pose proof (q u I v) as h; clear q.
    rewrite <- Heqopt in h; auto.
  }

  { Case "KTdifferential".
    unfold on_test.
    dest_cases fv.
    dest_sub x.
    symmetry in Heqx.
    symmetry in Heqfv; apply nullb_prop in Heqfv.

    unfold free_vars_term_restrict_term in Heqfv.
    dest_cases w.

    { applydup free_vars_term_substitution_dot_term_if_null in Heqx; auto;[].
      apply (f_equal (remove_duplicates KAssignable_dec)) in Heqx0.
      allrw fold_free_vars_term_nodup.
      rewrite Heqx0.
      apply big_sum_ext; introv i.
      f_equal.

      apply Derive_ext; introv.

      pose proof (IHt u I (upd_state v v0 t1)) as h; clear IHt.
      rewrite Heqx in h.
      rewrite h; clear h.

      rewrite (coincidence_term u (upd_state v v0 t1) v I I); auto.
      rewrite Heqfv; auto.
    }

    { applydup substitution_dot_term_if_no_dot in Heqx; subst; auto.
      apply big_sum_ext; introv i.
      f_equal.

      apply Derive_ext; introv.

      pose proof (IHt u I (upd_state v v0 t)) as h; clear IHt.
      rewrite Heqx in h.
      rewrite h; clear h.

      apply dynamic_semantics_term_upd_interpretation_dot_if_not_dot; auto.
    }
  }
Qed.

Lemma vec_in_implies_nth :
  forall {T n} d (v : Vector.t T n) a,
    Vector.In a v -> exists m, m < n /\ a = vec_nth v m d.
Proof.
  introv i.
  induction i; simpl.
  { exists 0; dands; auto; try omega. }
  { exrepnd; subst.
    exists (S m0); dands; try omega; auto. }
Qed.

Lemma subset_term_variables_substitution_dot_term :
  forall t1 t2 u,
    substitution_dot_term t1 t2 = Some u
    -> subset (term_variables u) (term_variables t1 ++ term_variables t2).
Proof.
  term_ind t1 Case; introv sdt; simpl in *; unfold ret in *; ginv; simpl; auto;
    try (complete (dest_sub s; dest_sub q; ginv;
                   symmetry in Heqs; symmetry in Heqq; simpl;
                   apply IHt1_1 in Heqs; auto; apply IHt1_2 in Heqq; auto;
                   introv i; apply in_app_iff in i; repndors;[apply Heqs in i|apply Heqq in i];
                   allrw in_app_iff; tcsp));
    try (complete (dest_sub s; ginv; symmetry in Heqs; simpl;
                   apply IHt1 in Heqs; auto)).

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => substitution_dot_term a t2) args)) as opv.
    destruct opv; symmetry in Heqopv; simpl in *; ginv; simpl.
    f_equal.
    introv i.
    apply in_app_iff.
    allrw in_vec_flatten; exrepnd.
    allrw in_vec_map; exrepnd; subst.
    apply (vec_in_implies_nth DTN) in i1; exrepnd; subst.

    pose proof (vec_opt2opt_vec_map_some_implies_some
                  args t
                  (fun a => substitution_dot_term a t2)
                  m DTN) as q.
    simpl in q; repeat (autodimp q hyp).
    remember (substitution_dot_term (vec_nth args m DTN) t2) as opt.
    destruct opt; tcsp; subst.

    pose proof (IHargs (vec_nth args m DTN)) as q; clear IHargs.
    autodimp q hyp.
    symmetry in Heqopt.
    apply q in Heqopt; clear q.
    apply Heqopt in i0; clear Heqopt.
    apply in_app_iff in i0; repndors; auto.
    left.
    eexists; dands;[|eauto].
    apply in_vec_map.
    eexists; dands;[|reflexivity]; auto.
  }

  { Case "KTread".
    apply implies_subset_app_r; tcsp. }

  { Case "KTdifferential".
    unfold on_test in sdt.
    dest_cases fv.
    dest_sub x; ginv.
    symmetry in Heqx.
    symmetry in Heqfv; apply nullb_prop in Heqfv.
    apply IHt1 in Heqx.
    simpl; auto. }
Qed.

Lemma find_function_in_uniform_substitution_uniform_substitution_restriction_term_funcof :
  forall s f n t,
    find_function_in_uniform_substitution s f n
    = find_function_in_uniform_substitution
        (uniform_substitution_restriction_term s (KTfuncOf f n t)) f n.
Proof.
  induction s; introv; simpl; auto.
  destruct a; simpl; repeat (dest_cases w; subst; simpl; tcsp); GC.
  unfold in_signature in *; dest_cases w; GC; simpl in *.
  apply not_or in n; tcsp.
Qed.

Lemma subset_term_variables_substitution_dots_term :
  forall t {n} (v : Vector.t Term n) u,
    substitution_dots_term t v = Some u
    -> subset
         (term_variables u)
         (term_variables t ++ vec_flatten (Vector.map term_variables v)).
Proof.
  term_ind t Case; introv sdt; simpl in *; unfold ret in *; ginv; simpl; auto;
    try (complete (dest_sub s; dest_sub q; ginv;
                   symmetry in Heqs; symmetry in Heqq; simpl;
                   apply IHt1 in Heqs; auto; apply IHt2 in Heqq; auto;
                   introv i; apply in_app_iff in i; repndors;[apply Heqs in i|apply Heqq in i];
                   allrw in_app_iff; tcsp));
    try (complete (dest_sub s; ginv; symmetry in Heqs; simpl;
                   apply IHt in Heqs; auto)).

  { Case "KTdot".
    destruct (le_gt_dec n0 n) as [d|d].
    { rewrite vec_nth_default; auto; simpl; auto. }
    introv i.
    apply in_vec_flatten.
    eexists; dands;[|eauto].
    apply in_vec_map.
    eexists;dands;[|eauto]; auto.
  }

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => substitution_dots_term a v) args)) as opv.
    destruct opv; symmetry in Heqopv; simpl in *; ginv; simpl.
    introv i.
    apply in_app_iff.
    allrw in_vec_flatten; exrepnd.
    allrw in_vec_map; exrepnd; subst.
    apply (vec_in_implies_nth DTN) in i1; exrepnd; subst.

    pose proof (vec_opt2opt_vec_map_some_implies_some
                  args t
                  (fun a => substitution_dots_term a v)
                  m DTN) as q.
    simpl in q; repeat (autodimp q hyp).
    remember (substitution_dots_term (vec_nth args m DTN) v) as opt; symmetry in Heqopt.
    destruct opt; tcsp; subst.

    pose proof (IHargs (vec_nth args m DTN)) as q; clear IHargs.
    autodimp q hyp.
    apply q in Heqopt; clear q.
    apply Heqopt in i0; clear Heqopt.
    apply in_app_iff in i0; repndors; auto.
    { left.
      eexists; dands;[|eauto].
      apply in_vec_map.
      eexists; dands;[|reflexivity]; auto. }
    { right; apply in_vec_flatten in i0; auto. }
  }

  { Case "KTread".
    apply implies_subset_app_r; tcsp. }

  { Case "KTdifferential".
    unfold on_test in sdt.
    dest_cases fv.
    dest_sub x; ginv.
    symmetry in Heqx.
    symmetry in Heqfv; apply nullb_prop in Heqfv.
    apply IHt in Heqx.
    simpl; auto. }
Qed.

Lemma term_variables_closed_uniform_substitution_term :
  forall t s u,
    free_vars_sub_restrict_term s t = EA_assignables []
    -> uniform_substitution_term t s = Some u
    -> subset (term_variables u) (term_variables t).
Proof.
  term_ind t Case; introv e ust; simpl in *; auto;
    unfold ret in *; ginv.

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => uniform_substitution_term a s) args)) as vop.
    destruct vop; symmetry in Heqvop; simpl in *; ginv.
    apply subset_term_variables_substitution_dots_term in ust.
    eapply subset_trans;[exact ust|];clear ust.

    assert (null (term_variables (lookup_func s f n))) as nl.
    { unfold lookup_func.
      remember (find_function_in_uniform_substitution s f n) as ff;
        destruct ff; simpl in *; ginv; autorewrite with core; try reflexivity.
      symmetry in Heqff.
      rewrite (find_function_in_uniform_substitution_uniform_substitution_restriction_term_funcof _ _ _ args) in Heqff.
      apply find_function_in_uniform_substitution_implies_subset_free_vars in Heqff.
      allrw @fold_free_vars_sub_restrict_term.
      rewrite e in Heqff.
      apply included_dec_nil_implies in Heqff.
      apply null_free_vars_term_implies_null_term_variables; auto. }
    rewrite nl; clear nl; simpl.

    apply (subset_vec_flatten_map_lr DTN).
    introv ltmn.

    pose proof (vec_opt2opt_vec_map_some_implies_some
                  args t
                  (fun a => uniform_substitution_term a s)
                  m DTN) as q.
    simpl in q; repeat (autodimp q hyp).
    remember (uniform_substitution_term (vec_nth args m DTN) s) as opt; symmetry in Heqopt.
    destruct opt; tcsp; subst.

    eapply IHargs;[auto| |eauto].

    pose proof (eassignables_subset_funcof s f n args (vec_nth args m DTN)) as q.
    autodimp q hyp.
    rewrite e in q.
    apply eassignables_subset_nil_implies in q; auto.
  }

  { Case "KTneg".
    dest_sub x; ginv; symmetry in Heqx.
    apply IHt in Heqx; auto.
    pose proof (eassignables_subset_neg s t) as h.
    rewrite e in h.
    apply eassignables_subset_nil_implies in h; auto.
  }

  { Case "KTplus".
    dest_sub x; ginv; symmetry in Heqx.
    dest_sub y; ginv; symmetry in Heqy.
    pose proof (eassignables_subset_plus1 s t1 t2) as h1; rewrite e in h1.
    pose proof (eassignables_subset_plus2 s t1 t2) as h2; rewrite e in h2.
    apply eassignables_subset_nil_implies in h1; auto.
    apply eassignables_subset_nil_implies in h2; auto.
    apply IHt1 in Heqx; auto.
    apply IHt2 in Heqy; auto.
    simpl; introv i; allrw in_app_iff; tcsp.
  }

  { Case "KTminus".
    dest_sub x; ginv; symmetry in Heqx.
    dest_sub y; ginv; symmetry in Heqy.
    pose proof (eassignables_subset_minus1 s t1 t2) as h1; rewrite e in h1.
    pose proof (eassignables_subset_minus2 s t1 t2) as h2; rewrite e in h2.
    apply eassignables_subset_nil_implies in h1; auto.
    apply eassignables_subset_nil_implies in h2; auto.
    apply IHt1 in Heqx; auto.
    apply IHt2 in Heqy; auto.
    simpl; introv i; allrw in_app_iff; tcsp.
  }

  { Case "KTtimes".
    dest_sub x; ginv; symmetry in Heqx.
    dest_sub y; ginv; symmetry in Heqy.
    pose proof (eassignables_subset_times1 s t1 t2) as h1; rewrite e in h1.
    pose proof (eassignables_subset_times2 s t1 t2) as h2; rewrite e in h2.
    apply eassignables_subset_nil_implies in h1; auto.
    apply eassignables_subset_nil_implies in h2; auto.
    apply IHt1 in Heqx; auto.
    apply IHt2 in Heqy; auto.
    simpl; introv i; allrw in_app_iff; tcsp.
  }

  { Case "KTdifferential".
    unfold on_test in ust.
    dest_cases fv.
    dest_sub x; ginv.
    symmetry in Heqx.
    symmetry in Heqfv.
    simpl.
    apply IHt in Heqx; auto.
    pose proof (eassignables_subset_diff s t) as h.
    rewrite e in h.
    apply eassignables_subset_nil_implies in h; auto.
  }
Qed.

Lemma free_vars_vec_term_as_vec_flatten_assignables :
  forall {n} (v : Vector.t Term n),
    free_vars_vec_term v = vec_flatten (Vector.map free_vars_term v).
Proof.
  unfold free_vars_vec_term; auto.
Qed.

Lemma subset_free_vars_term_substitution_dots_term :
  forall t {n} (v : Vector.t Term n) u,
    substitution_dots_term t v = Some u
    -> subset
         (free_vars_term u)
         (free_vars_term t ++ vec_flatten (Vector.map free_vars_term v)).
Proof.
  term_ind t Case; introv sdt; simpl in *; unfold ret in *; ginv; simpl; auto;
    try (complete (dest_sub s; dest_sub q; ginv;
                   symmetry in Heqs; symmetry in Heqq; simpl;
                   apply IHt1 in Heqs; auto; apply IHt2 in Heqq; auto;
                   introv i; apply in_app_iff in i; repndors;[apply Heqs in i|apply Heqq in i];
                   allrw in_app_iff; tcsp));
    try (complete (dest_sub s; ginv; symmetry in Heqs; simpl;
                   apply IHt in Heqs; auto)).

  { Case "KTdot".
    destruct (le_gt_dec n0 n) as [d|d].
    { rewrite vec_nth_default; auto; simpl; auto. }
    introv i.
    apply in_vec_flatten.
    eexists; dands;[|eauto].
    apply in_vec_map.
    eexists;dands;[|eauto]; auto.
  }

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => substitution_dots_term a v) args)) as opv.
    destruct opv; symmetry in Heqopv; simpl in *; ginv; simpl.
    introv i.
    apply in_app_iff.
    allrw in_vec_flatten; exrepnd.
    allrw in_vec_map; exrepnd; subst.
    apply (vec_in_implies_nth DTN) in i1; exrepnd; subst.

    pose proof (vec_opt2opt_vec_map_some_implies_some
                  args t
                  (fun a => substitution_dots_term a v)
                  m DTN) as q.
    simpl in q; repeat (autodimp q hyp).
    remember (substitution_dots_term (vec_nth args m DTN) v) as opt; symmetry in Heqopt.
    destruct opt; tcsp; subst.

    pose proof (IHargs (vec_nth args m DTN)) as q; clear IHargs.
    autodimp q hyp.
    apply q in Heqopt; clear q.
    apply Heqopt in i0; clear Heqopt.
    apply in_app_iff in i0; repndors; auto.
    { left.
      eexists; dands;[|eauto].
      apply in_vec_map.
      eexists; dands;[|reflexivity]; auto. }
    { right; apply in_vec_flatten in i0; auto. }
  }

  { Case "KTread".
    introv i; simpl in *; tcsp. }

  { Case "KTdifferential".
    unfold on_test in sdt.
    dest_cases fv.
    dest_sub x; ginv.
    symmetry in Heqx.
    symmetry in Heqfv; apply nullb_prop in Heqfv.
    applydup IHt in Heqx.
    simpl; auto.

    rewrite <- free_vars_vec_term_as_vec_flatten_assignables in Heqx0.
    rewrite <- free_vars_vec_term_as_vec_flatten_assignables.

    unfold free_vars_vec_term_restrict_term in Heqfv.
    dest_cases w; symmetry in Heqw.

    { rewrite Heqfv in Heqx0.
      rewrite Heqfv.
      autorewrite with core in *.
      apply implies_subset_app_lr; auto.
      apply implies_subset_map_lr; auto. }

    { apply substitution_dots_term_if_no_dot in Heqx; auto; subst.
      introv i; rewrite in_app_iff; auto. }
  }
Qed.

Lemma free_vars_term_closed_uniform_substitution_term :
  forall t s u,
    free_vars_sub_restrict_term s t = EA_assignables []
    -> uniform_substitution_term t s = Some u
    -> subset (free_vars_term u) (free_vars_term t).
Proof.
  term_ind t Case; introv e ust; simpl in *; auto;
    unfold ret in *; ginv.

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => uniform_substitution_term a s) args)) as vop.
    destruct vop; symmetry in Heqvop; simpl in *; ginv.

    apply subset_free_vars_term_substitution_dots_term in ust.
    eapply subset_trans;[exact ust|];clear ust.

    assert (null (free_vars_term (lookup_func s f n))) as nl.
    { unfold lookup_func.
      remember (find_function_in_uniform_substitution s f n) as ff;
        destruct ff; simpl in *; ginv; autorewrite with core; try reflexivity.
      simpl.
      symmetry in Heqff.
      rewrite (find_function_in_uniform_substitution_uniform_substitution_restriction_term_funcof _ _ _ args) in Heqff.
      apply find_function_in_uniform_substitution_implies_subset_free_vars in Heqff.
      allrw @fold_free_vars_sub_restrict_term.
      rewrite e in Heqff.
      apply included_dec_nil_implies in Heqff; auto. }
    rewrite nl; clear nl; simpl.

    apply (subset_vec_flatten_map_lr DTN).
    introv ltmn.

    pose proof (vec_opt2opt_vec_map_some_implies_some
                  args t
                  (fun a => uniform_substitution_term a s)
                  m DTN) as q.
    simpl in q; repeat (autodimp q hyp).
    remember (uniform_substitution_term (vec_nth args m DTN) s) as opt; symmetry in Heqopt.
    destruct opt; tcsp; subst.

    eapply IHargs;[auto| |eauto].

    pose proof (eassignables_subset_funcof s f n args (vec_nth args m DTN)) as q.
    autodimp q hyp.
    rewrite e in q.
    apply eassignables_subset_nil_implies in q; auto.
  }

  { Case "KTneg".
    dest_sub x; ginv; symmetry in Heqx.
    apply IHt in Heqx; auto.
    pose proof (eassignables_subset_neg s t) as h.
    rewrite e in h.
    apply eassignables_subset_nil_implies in h; auto.
  }

  { Case "KTplus".
    dest_sub x; ginv; symmetry in Heqx.
    dest_sub y; ginv; symmetry in Heqy.
    pose proof (eassignables_subset_plus1 s t1 t2) as h1; rewrite e in h1.
    pose proof (eassignables_subset_plus2 s t1 t2) as h2; rewrite e in h2.
    apply eassignables_subset_nil_implies in h1; auto.
    apply eassignables_subset_nil_implies in h2; auto.
    apply IHt1 in Heqx; auto.
    apply IHt2 in Heqy; auto.
    simpl; introv i; allrw in_app_iff; tcsp.
  }

  { Case "KTminus".
    dest_sub x; ginv; symmetry in Heqx.
    dest_sub y; ginv; symmetry in Heqy.
    pose proof (eassignables_subset_minus1 s t1 t2) as h1; rewrite e in h1.
    pose proof (eassignables_subset_minus2 s t1 t2) as h2; rewrite e in h2.
    apply eassignables_subset_nil_implies in h1; auto.
    apply eassignables_subset_nil_implies in h2; auto.
    apply IHt1 in Heqx; auto.
    apply IHt2 in Heqy; auto.
    simpl; introv i; allrw in_app_iff; tcsp.
  }

  { Case "KTtimes".
    dest_sub x; ginv; symmetry in Heqx.
    dest_sub y; ginv; symmetry in Heqy.
    pose proof (eassignables_subset_times1 s t1 t2) as h1; rewrite e in h1.
    pose proof (eassignables_subset_times2 s t1 t2) as h2; rewrite e in h2.
    apply eassignables_subset_nil_implies in h1; auto.
    apply eassignables_subset_nil_implies in h2; auto.
    apply IHt1 in Heqx; auto.
    apply IHt2 in Heqy; auto.
    simpl; introv i; allrw in_app_iff; tcsp.
  }

  { Case "KTdifferential".
    unfold on_test in ust.
    dest_cases fv.
    dest_sub x; ginv.
    symmetry in Heqx.
    symmetry in Heqfv.
    simpl.

    pose proof (eassignables_subset_diff s t) as ss.
    rewrite e in ss.
    apply eassignables_subset_nil_implies in ss.

    apply IHt in Heqx; auto.
    apply implies_subset_app_lr; auto.
    apply implies_subset_map_lr; auto.
  }
Qed.

Lemma free_vars_term_subset_term_variables_subset :
  forall (v : KVariable) (t : Term),
    In (KAssignVar v) (free_vars_term t)
    -> In v (term_variables t).
Proof.
  term_ind t Case; introv i; simpl in *; auto.

  { Case "KTfuncOf".
    allrw in_vec_flatten; exrepnd.
    allrw in_vec_map; exrepnd; subst.
    apply IHargs in i0; auto.
    eexists;dands;[|eauto].
    apply in_vec_map.
    eexists;dands;[|eauto];auto.
  }

  { Case "KTread".
    repndors; subst; simpl; tcsp.
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

  { Case "KTdifferential".
    apply in_app_iff in i; repndors; tcsp.
    apply in_map_iff in i; exrepnd.
    destruct x; simpl in *; ginv.
  }
Qed.

Lemma substitution_dot_term_preserves_term_variables_if_containsDot :
  forall t u z,
    substitution_dot_term t u = Some z
    -> containsDot t = true
    -> subset (term_variables u) (term_variables z).
Proof.
  term_ind t Case; introv sdt cd; simpl in *; unfold ret in *; ginv; tcsp; GC;
    try (complete (dest_sub w; ginv; symmetry in Heqw;
                   dest_sub y; ginv; symmetry in Heqy;
                   allrw orb_true_iff; simpl;
                   apply implies_subset_app_r;
                   repndors;[apply IHt1 in Heqw|apply IHt2 in Heqy]; tcsp));
    try (complete (dest_sub w; ginv; symmetry in Heqw; simpl;
                   apply IHt in Heqw; auto)).

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => substitution_dot_term a u) args)) as vop.
    destruct vop; symmetry in Heqvop; simpl in *; ginv.
    simpl.
    apply (vec2bool_map_true_implies DTN) in cd; exrepnd.

    pose proof (vec_opt2opt_vec_map_some_implies_some
                  args t
                  (fun a => substitution_dot_term a u)
                  m DTN) as q.
    simpl in q; repeat (autodimp q hyp).
    remember (substitution_dot_term (vec_nth args m DTN) u) as opt; symmetry in Heqopt.
    destruct opt; tcsp; subst.
    apply IHargs in Heqopt; auto.
    eapply implies_subset_vec_flatten_map_r;[|eauto]; auto.
  }

  { Case "KTdifferential".
    unfold on_test in *; dest_cases w.
    dest_sub y; ginv; symmetry in Heqy; simpl.
    apply IHt in Heqy; auto.
  }
Qed.

Lemma vec_eta :
  forall {A} a {n} (v1 v2 : Vector.t A n),
    (forall m, m < n -> vec_nth v1 m a = vec_nth v2 m a)
    -> v1 = v2.
Proof.
  induction n; introv.

  { apply (@Vector.case0
             A
             (fun v1 =>
                (forall m : nat, m < 0 -> vec_nth v1 m a = vec_nth v2 m a) -> v1 = v2));
      simpl; clear v1.
    apply (@Vector.case0
             A
             (fun v2 =>
                (forall m : nat, m < 0 -> a = vec_nth v2 m a) -> Vector.nil A = v2));
      simpl; clear v2.
    auto. }

  { apply (Vector.caseS' v1); introv; clear v1.
    apply (Vector.caseS' v2); introv; clear v2.
    simpl.
    intro hyp.
    f_equal.
    { apply (hyp 0); omega. }
    apply IHn; introv ltmn.
    apply (hyp (S m)); omega. }
Qed.

Lemma substitution_dot_term_preserves_term_variables_if_not_containsDot :
  forall t u z,
    substitution_dot_term t u = Some z
    -> containsDot t = false
    -> t = z.
Proof.
  term_ind t Case; introv sdt cd; simpl in *; unfold ret in *; ginv; tcsp; GC;
    try (complete (dest_sub w; ginv; symmetry in Heqw;
                   dest_sub y; ginv; symmetry in Heqy;
                   allrw orb_false_iff; simpl; repnd;
                   apply IHt1 in Heqw; auto;
                   apply IHt2 in Heqy; auto; subst; auto));
    try (complete (dest_sub w; ginv; symmetry in Heqw; simpl;
                   apply IHt in Heqw; subst; auto)).

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => substitution_dot_term a u) args)) as vop.
    destruct vop; symmetry in Heqvop; simpl in *; ginv.
    f_equal.
    apply (vec_eta DTN); introv ltmn.
    pose proof (vec_opt2opt_vec_map_some_implies_some
                  args t
                  (fun a => substitution_dot_term a u)
                  m DTN) as q.
    simpl in q; repeat (autodimp q hyp).
    remember (substitution_dot_term (vec_nth args m DTN) u) as opt; symmetry in Heqopt.
    destruct opt; tcsp; subst.
    apply IHargs in Heqopt; auto.
    apply vec2bool_map_false_implies; auto.
  }

  { Case "KTdifferential".
    unfold on_test in *; dest_cases w.
    dest_sub y; ginv; symmetry in Heqy; simpl.
    apply IHt in Heqy; subst; auto.
  }
Qed.

Lemma dynamic_semantics_term_upd_interpretation_dot_if_not_containsDot :
  forall t I u v,
    containsDot t = false
    -> dynamic_semantics_term (upd_interpretation_dot I u) v t
       = dynamic_semantics_term I v t.
Proof.
  term_ind t Case; introv cd; simpl in *; tcsp;
    try (complete (rewrite IHt; auto));
    try (complete (allrw orb_false_iff; simpl; repnd;
                   rewrite IHt1; auto; rewrite IHt2; auto)).

  { Case "KTfuncOf".
    f_equal.
    apply eq_vec_map; introv i.
    apply (vec_in_implies_nth DTN) in i; exrepnd; subst.
    apply (vec2bool_map_false_implies DTN m) in cd; auto.
  }

  { Case "KTdifferential".
    apply big_sum_ext; introv i.
    apply Rmult_eq_compat_l.
    apply Derive_ext; introv.
    apply IHt; auto.
  }
Qed.

Lemma vec_nth_change_default :
  forall {A} a b {n} (v : Vector.t A n) m,
    m < n -> vec_nth v m b = vec_nth v m a.
Proof.
  induction n; introv ltm; try omega.
  apply (Vector.caseS' v); introv; clear v.
  simpl.
  destruct m; auto.
  apply IHn; omega.
Qed.

Lemma substitution_dots_term_var_not_in_some_implies :
  forall d t {n} (v : Vector.t Term n) u x,
    substitution_dots_term t v = Some u
    -> ~ In x (term_variables u)
    -> ~ In x (term_variables t)
       /\ (forall m,
              m < n
              -> containsDotN m t = true
              -> ~ In x (term_variables (vec_nth v m d))).
Proof.
  term_ind t Case; introv sub ni; simpl in *;
    unfold ret in *; ginv; simpl in *;
      try (complete (dands; auto));
      try (complete (dest_sub w; ginv; symmetry in Heqw; simpl in *;
                     eapply IHt in Heqw;[|eauto]; auto));
      try (complete (dest_sub w; ginv; dest_sub y; ginv;
                     symmetry in Heqw, Heqy; simpl in *;
                     rewrite in_app_iff in ni; apply not_or in ni; repnd;
                     rewrite in_app_iff;
                     eapply IHt1 in Heqw;[|eauto];
                     eapply IHt2 in Heqy;[|eauto];
                     repnd; dands;[tcsp|];
                     introv ltmn cd;
                     apply orb_true_iff in cd; repndors;
                     [apply Heqw in cd|apply Heqy in cd]; auto)).


  { Case "KTdot".
    dands; auto.
    introv ltmn cd.
    dest_cases w; subst; auto.
    erewrite vec_nth_change_default; eauto. }

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => substitution_dots_term a v) args)) as vop.
    destruct vop; symmetry in Heqvop; simpl in *; ginv.
    simpl in *.
    rewrite in_vec_flatten in ni.
    assert (forall m, m < n -> ~ In x (term_variables (vec_nth t m DTN))) as ani.
    { introv ltm j.
      destruct ni.
      eexists;dands;[|eauto].
      apply in_vec_map; eexists; dands;[|eauto];auto. }
    clear ni.

    dands.

    { intro i.
      apply in_vec_flatten in i; exrepnd.
      apply in_vec_map in i1; exrepnd; subst.
      apply (vec_in_implies_nth DTN) in i1; exrepnd; subst.

      pose proof (ani m) as ni; autodimp ni hyp.

      pose proof (vec_opt2opt_vec_map_some_implies_some
                    args t
                    (fun a => substitution_dots_term a v)
                    m DTN) as q.
      simpl in q; repeat (autodimp q hyp).
      remember (substitution_dots_term (vec_nth args m DTN) v) as opt; symmetry in Heqopt.
      destruct opt; tcsp; subst.

      eapply IHargs in Heqopt;[| |eauto]; auto.
      repnd; auto. }

    { introv ltm vb.
      apply (vec2bool_map_true_implies DTN) in vb; exrepnd.

      pose proof (ani m0) as ni; autodimp ni hyp.

      pose proof (vec_opt2opt_vec_map_some_implies_some
                    args t
                    (fun a => substitution_dots_term a v)
                    m0 DTN) as q.
      simpl in q; repeat (autodimp q hyp).
      remember (substitution_dots_term (vec_nth args m0 DTN) v) as opt; symmetry in Heqopt.
      destruct opt; tcsp; subst.

      eapply IHargs in Heqopt;[| |eauto]; auto.
      repnd; auto. }
  }

  { Case "KTdifferential".
    unfold on_test in *; dest_cases w.
    dest_sub y; ginv; symmetry in Heqy; simpl in *.
    eapply IHt in Heqy;[|eauto]; auto.
  }
Qed.

(*
Lemma substitution_dots_term_assign_not_in_some_implies :
  forall d t {n} (v : Vector.t Term n) u x,
    substitution_dots_term t v = Some u
    -> ~ In x (term_assignables u)
    -> ~ In x (term_assignables t)
       /\ (forall m,
              m < n
              -> containsDotN m t = true
              -> ~ In x (term_assignables (vec_nth v m d))).
Proof.
  term_ind t Case; introv sub ni; simpl in *;
    unfold ret in *; ginv; simpl in *;
      try (complete (dands; auto));
      try (complete (dest_sub w; ginv; symmetry in Heqw; simpl in *;
                     eapply IHt in Heqw;[|eauto]; auto));
      try (complete (dest_sub w; ginv; dest_sub y; ginv;
                     symmetry in Heqw, Heqy; simpl in *;
                     rewrite in_app_iff in ni; apply not_or in ni; repnd;
                     rewrite in_app_iff;
                     eapply IHt1 in Heqw;[|eauto];
                     eapply IHt2 in Heqy;[|eauto];
                     repnd; dands;[tcsp|];
                     introv ltmn cd;
                     apply orb_true_iff in cd; repndors;
                     [apply Heqw in cd|apply Heqy in cd]; auto)).


  { Case "KTdot".
    dands; auto.
    introv ltmn cd.
    dest_cases w; subst; auto.
    erewrite vec_nth_change_default; eauto. }

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => substitution_dots_term a v) args)) as vop.
    destruct vop; symmetry in Heqvop; simpl in *; ginv.
    simpl in *.
    rewrite in_vec_flatten in ni.
    assert (forall m, m < n -> ~ In x (term_assignables (vec_nth t m DTN))) as ani.
    { introv ltm j.
      destruct ni.
      eexists;dands;[|eauto].
      apply in_vec_map; eexists; dands;[|eauto];auto. }
    clear ni.

    dands.

    { intro i.
      apply in_vec_flatten in i; exrepnd.
      apply in_vec_map in i1; exrepnd; subst.
      apply (vec_in_implies_nth DTN) in i1; exrepnd; subst.

      pose proof (ani m) as ni; autodimp ni hyp.

      pose proof (vec_opt2opt_vec_map_some_implies_some
                    args t
                    (fun a => substitution_dots_term a v)
                    m DTN) as q.
      simpl in q; repeat (autodimp q hyp).
      remember (substitution_dots_term (vec_nth args m DTN) v) as opt; symmetry in Heqopt.
      destruct opt; tcsp; subst.

      eapply IHargs in Heqopt;[| |eauto]; auto.
      repnd; auto. }

    { introv ltm vb.
      apply (vec2bool_map_true_implies DTN) in vb; exrepnd.

      pose proof (ani m0) as ni; autodimp ni hyp.

      pose proof (vec_opt2opt_vec_map_some_implies_some
                    args t
                    (fun a => substitution_dots_term a v)
                    m0 DTN) as q.
      simpl in q; repeat (autodimp q hyp).
      remember (substitution_dots_term (vec_nth args m0 DTN) v) as opt; symmetry in Heqopt.
      destruct opt; tcsp; subst.

      eapply IHargs in Heqopt;[| |eauto]; auto.
      repnd; auto. }
  }

  { Case "KTdifferential".
    unfold on_test in *; dest_cases w.
    dest_sub y; ginv; symmetry in Heqy; simpl in *.
    allrw in_app_iff.
    apply not_or in ni; repnd.
    symmetry in Heqw; apply nullb_prop in Heqw.

    pose proof (IHt n v t0 x) as h.
    repeat (autodimp h hyp).
    repnd.
    dands; auto.
    introv xx; repndors; tcsp.
    apply in_map_iff in xx; exrepnd; subst.
    destruct ni.
    apply in_map_iff; eexists; dands; eauto.

    rewrite in_map_iff in ni.

    pose proof (IHt n v t0 (KD x)) as h2.
    repeat (autodimp h2 hyp).
    { intro xx.
      destruct ni.
      apply in_map_iff; eexists; dands.

  }
Qed.*)

(*
Lemma dynamic_semantics_term_upd_interpretation_dots_remove_when_no_dot_gen :
  forall t (b : nat -> bool) X I n (v : Vector.t Term n) F s,
    dynamic_semantics_term (upd_interpretation_dots I n (Vector.map F v)) s t
    = dynamic_semantics_term
        (upd_interpretation_dots
           I
           n
           (Vector.map
              F
              (vec_mapn
                 (fun u m => if containsDotN (n - S m) t || b m then u else X)
                 v)))
        s
        t.
Proof.
  term_ind t Case; introv; simpl; auto;
    try (complete (rewrite (IHt1 (fun m => containsDotN (n - S m) t2 || b m) X);
                   rewrite (IHt2 (fun m => containsDotN (n - S m) t1 || b m) X);
                   f_equal; f_equal; f_equal;
                   apply (eq_vec_map2 X); introv ltn; f_equal;
                   repeat (rewrite (vec_nth_mapn_cases X)); dest_cases w;
                   rewrite orb_assoc;auto;
                   rewrite (orb_comm (containsDotN _ _)); auto)).

  { Case "KTdot".
    repeat (rewrite (vec_nth_map_cases X)).
    dest_cases w.
    rewrite (vec_nth_mapn_cases X).
    dest_cases w; try omega.
    rewrite minus_Sn_m; auto.
    autorewrite with core.
    rewrite sub_sub_same_prop1; try omega.
    repeat (dest_cases w).
  }

  { Case "KTfuncOf".
    f_equal.
    apply eq_vec_map; introv i.

    rewrite (IHargs
               a i
               (fun m => vec2bool (Vector.map (containsDotN (n0 - S m)) args) || b m)
               X);
      auto.
    f_equal.
    f_equal.
    apply (eq_vec_map2 X); introv ltm.
    f_equal.
    repeat (rewrite (vec_nth_mapn_cases X)).
    repeat (dest_cases w;[]).
    dest_cases w; dest_cases y; symmetry in Heqw, Heqy;
      autorewrite with core in *; ginv.

    apply orb_false_iff in Heqy; repnd.
    apply (vec_in_implies_nth X) in i; exrepnd; subst.
    apply (vec2bool_map_false_implies X m0) in Heqy0; auto.
    rewrite Heqy0 in Heqw; ginv.
  }

  { Case "KTneg".
    f_equal; auto. }

  { Case "KTdifferential".
    apply big_sum_ext; introv i.
    f_equal.
    apply Derive_ext; introv.
    apply IHt. }
Qed.
*)

(*
(* replaces nth term in vector [v] by a dummy term ([DTN]) if dot(n) is not in t *)
Definition trim_useless {n} (v : Vector.t Term n) (t : Term) : Vector.t Term n :=
  vec_mapn
    (fun u m => if containsDotN (n - S m) t then u else DTN)
    v.

Lemma dynamic_semantics_term_upd_interpretation_dots_remove_when_no_dot :
  forall t I n (v : Vector.t Term n) F s,
    dynamic_semantics_term (upd_interpretation_dots I n (Vector.map F v)) s t
    = dynamic_semantics_term
        (upd_interpretation_dots I n (Vector.map F (trim_useless v t)))
        s
        t.
Proof.
  introv.
  rewrite (dynamic_semantics_term_upd_interpretation_dots_remove_when_no_dot_gen
             _ (fun _ => false) DTN).
  f_equal.
  f_equal.
  apply (eq_vec_map2 DTN); introv ltm.
  f_equal.
  unfold trim_useless.
  repeat (rewrite (vec_nth_mapn_cases DTN)).
  repeat (dest_cases w;[]).
  autorewrite with core; auto.
Qed.
*)

Definition on_substitution_dots_term
           (t : Term)
           {n}
           (v : Vector.t Term n)
           (Q : Term -> Prop) : Prop :=
  match substitution_dots_term t v with
  | Some u => Q u
  | None => True
  end.

Lemma null_free_vars_vec_term_implies_null_vec_term_variables :
  forall n (v : Vector.t Term n),
    null (free_vars_vec_term v)
    -> null (vec_term_variables v).
Proof.
  induction n; introv.

  { apply Vector.case0 with (v := v).
    simpl; clear v; introv h; reflexivity. }

  { apply (Vector.caseS' v); introv; clear v; simpl.
    intro q.
    unfold free_vars_vec_term in q; simpl in q.
    apply null_app in q; repnd.
    apply null_app; dands; auto.
    apply null_free_vars_term_implies_null_term_variables; auto. }
Qed.

Lemma null_vec_term_variables :
  forall n (v : Vector.t Term n) t,
    Vector.In t v
    -> null (vec_term_variables v)
    -> null (term_variables t).
Proof.
  induction n; introv.

  { apply Vector.case0 with (v := v).
    simpl; clear v.
    intro h; inversion h.
  }

  { apply (Vector.caseS' v); introv; clear v; simpl.
    introv i nl.
    apply null_app in nl; repnd.
    inversion i; subst; eqDepDec; subst; auto.
    eapply IHn; eauto. }
Qed.

Lemma null_free_vars_vec_term :
  forall n (v : Vector.t Term n) t,
    Vector.In t v
    -> null (free_vars_vec_term v)
    -> null (free_vars_term t).
Proof.
  induction n; introv.

  { apply Vector.case0 with (v := v).
    simpl; clear v.
    intro h; inversion h.
  }

  { apply (Vector.caseS' v); introv; clear v; simpl.
    introv i nl.
    unfold free_vars_vec_term in nl; simpl in nl.
    apply null_app in nl; repnd.
    inversion i; subst; eqDepDec; subst; auto.
    eapply IHn; eauto. }
Qed.

Lemma term_variables_substitution_dots_term_if_null :
  forall n (u : Vector.t Term n) t z,
    null (free_vars_vec_term u)
    -> substitution_dots_term t u = Some z
    -> term_variables t = term_variables z.
Proof.
  term_ind t Case; simpl; introv nl e; unfold ret in *; ginv; tcsp;
    try (complete (dest_sub w; ginv; simpl; eapply IHt; eauto));
    try (complete (dest_sub w; ginv; dest_sub y; ginv; simpl;
                   erewrite IHt1; eauto; erewrite IHt2; eauto)).

  { Case "KTdot".
    apply null_free_vars_vec_term_implies_null_vec_term_variables in nl; auto.
    destruct (le_gt_dec n n0) as [d|d].
    { rewrite vec_nth_default; simpl; auto. }
    { apply (null_vec_term_variables _ _ (vec_nth u n0 (KTdot n0))) in nl; auto. }
  }

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a => substitution_dots_term a u) args)) as opv.
    destruct opv; symmetry in Heqopv; simpl in *; ginv; simpl.
    f_equal.
    apply (eq_vec_map2 DTN); introv ltmn.
    pose proof (vec_opt2opt_vec_map_some_implies_some
                  args t
                  (fun a => substitution_dots_term a u)
                  m DTN) as q.
    simpl in q; repeat (autodimp q hyp).
    remember (substitution_dots_term (vec_nth args m DTN) u) as opt.
    destruct opt; tcsp; subst.
    apply IHargs; auto.
  }

  { Case "KTdifferential".
    unfold on_test in e.
    dest_cases w.
    clear Heqw.
    dest_sub x; ginv.
    simpl.
    erewrite IHt; eauto. }
Qed.

Lemma free_vars_term_substitution_dots_term_if_null :
  forall n (u : Vector.t Term n) t z,
    null (free_vars_vec_term u)
    -> substitution_dots_term t u = Some z
    -> free_vars_term t = free_vars_term z.
Proof.
  term_ind t Case; simpl; introv nl e; unfold ret in *; ginv; tcsp;
    try (complete (dest_sub w; ginv; simpl; eapply IHt; eauto));
    try (complete (dest_sub w; ginv; dest_sub y; ginv; simpl;
                   erewrite IHt1; eauto; erewrite IHt2; eauto)).

  { Case "KTdot".
    destruct (le_gt_dec n n0) as [d|d].
    { rewrite vec_nth_default; simpl; auto. }
    { apply (null_free_vars_vec_term _ _ (vec_nth u n0 (KTdot n0))) in nl; auto. }
  }

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a => substitution_dots_term a u) args)) as opv.
    destruct opv; symmetry in Heqopv; simpl in *; ginv; simpl.
    f_equal.
    apply (eq_vec_map2 DTN); introv ltmn.
    pose proof (vec_opt2opt_vec_map_some_implies_some
                  args t
                  (fun a => substitution_dots_term a u)
                  m DTN) as q.
    simpl in q; repeat (autodimp q hyp).
    remember (substitution_dots_term (vec_nth args m DTN) u) as opt.
    destruct opt; tcsp; subst.
    apply IHargs; auto.
  }

  { Case "KTdifferential".
    unfold on_test in e.
    dest_cases w.
    clear Heqw.
    dest_sub x; ginv.
    simpl.
    erewrite IHt; eauto. }
Qed.

Lemma dynamic_semantics_term_substitution_dots_term :
  forall t {n} (u : Vector.t Term n) I v,
    on_substitution_dots_term
      t u
      (fun x =>
         dynamic_semantics_term I v x
         = dynamic_semantics_term
             (upd_interpretation_dots I (Vector.map (dynamic_semantics_term I v) u))
             v t).
Proof.
  term_ind t Case;
    unfold on_substitution_dots_term in *;
    introv; simpl; tcsp;
      try (complete (pose proof (IHt n u I v) as h; clear IHt;
                     dest_sub x; congruence));
      try (complete (pose proof (IHt1 n u I v) as h1; clear IHt1;
                     pose proof (IHt2 n u I v) as h2; clear IHt2;
                     dest_sub x; dest_sub y; congruence)).

  { Case "KTdot".
    rewrite (vec_nth_map_cases DTN).
    dest_cases w.

    { rewrite vec_nth_default; simpl; auto. }

    { erewrite vec_nth_change_default;[reflexivity|]; auto. }
  }

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => substitution_dots_term a u) args)) as opv.
    destruct opv; symmetry in Heqopv; simpl in *; ginv; simpl.
    f_equal.
    apply (eq_vec_map2 DTN); introv ltmn.
    pose proof (vec_opt2opt_vec_map_some_implies_some
                  args t
                  (fun a => substitution_dots_term a u)
                  m DTN) as q.
    simpl in q; repeat (autodimp q hyp).
    remember (substitution_dots_term (vec_nth args m DTN) u) as opt.
    destruct opt; tcsp; subst.
    pose proof (IHargs (vec_nth args m DTN)) as q; clear IHargs.
    autodimp q hyp.
    pose proof (q n0 u I v) as h; clear q.
    rewrite <- Heqopt in h; auto.
  }

  { Case "KTdifferential".
    unfold on_test.
    dest_cases fv.
    dest_sub x.
    symmetry in Heqx.
    symmetry in Heqfv; apply nullb_prop in Heqfv.

    unfold free_vars_vec_term_restrict_term in Heqfv.
    dest_cases w; symmetry in Heqw.

    { applydup free_vars_term_substitution_dots_term_if_null in Heqx; auto;[].
      apply (f_equal (remove_duplicates KAssignable_dec)) in Heqx0.
      allrw fold_free_vars_term_nodup.
      rewrite Heqx0.
      apply big_sum_ext; introv i.
      f_equal.

      apply Derive_ext; introv.

      pose proof (IHt n u I (upd_state v v0 t1)) as h; clear IHt.
      rewrite Heqx in h.
      rewrite h; clear h.

      f_equal.
      f_equal.
      apply eq_vec_map; introv j.
      rewrite (coincidence_term a (upd_state v v0 t1) v I I); auto.
      eapply null_free_vars_vec_term in Heqfv;[|eauto].
      rewrite Heqfv; auto. }

    { applydup substitution_dots_term_if_no_dot in Heqx; subst; auto.
      apply big_sum_ext; introv i.
      f_equal.

      apply Derive_ext; introv.

      pose proof (IHt n u I (upd_state v v0 t)) as h; clear IHt.
      rewrite Heqx in h.
      rewrite h; clear h.

      apply dynamic_semantics_term_upd_interpretation_dots_if_not_dot; auto. }
  }
Qed.

Lemma free_vars_uniform_substitution_entry_nil_implies1 :
  forall a f n t,
    free_vars_uniform_substitution_entry a = EA_assignables []
    -> find_function_in_uniform_substitution_entry a f n = Some t
    -> free_vars_term t = [].
Proof.
  destruct a; simpl; unfold EA_assignables; introv h w; ginv;
    repeat (dest_cases z; subst; GC); ginv; tcsp.
  inversion h; auto.
Qed.

Lemma free_vars_sub_restrict_term_KTfuncOf_nil_implies_free_vars_lookup_func_nil :
  forall f {n} (args : Vector.t Term n) s,
    free_vars_sub_restrict_term s (KTfuncOf f n args) = EA_assignables []
    -> free_vars_term (lookup_func s f n) = [].
Proof.
  induction s; introv e; simpl in *.

  { autorewrite with core; auto. }

  unfold lookup_func; simpl.
  unfold free_vars_sub_restrict_term in e; simpl in e.
  dest_cases w; symmetry in Heqw; simpl in *.

  { apply EAssignables_app_eq_nil_implies in e; repnd.
    autodimp IHs hyp.
    remember (find_function_in_uniform_substitution_entry a f n) as z.
    symmetry in Heqz; destruct z.

    { apply free_vars_uniform_substitution_entry_nil_implies1 in Heqz; auto. }

    { remember (find_function_in_uniform_substitution s f n) as r.
      symmetry in Heqr; destruct r; simpl; autorewrite with core; auto.
      unfold lookup_func in IHs.
      rewrite Heqr in IHs; auto. }
  }

  { remember (find_function_in_uniform_substitution_entry a f n) as z.
    symmetry in Heqz; destruct z.

    { destruct a; simpl in *; repeat (dest_cases w; ginv; GC); simpl in *; ginv.
      unfold in_signature in *; dest_cases w; simpl in *.
      apply not_or in n; repnd; tcsp. }

    { remember (find_function_in_uniform_substitution s f n) as r.
      symmetry in Heqr; destruct r; simpl; autorewrite with core; auto.
      unfold lookup_func in IHs.
      rewrite Heqr in IHs; auto. }
  }
Qed.

Lemma dynamic_semantics_term_adjoint_interpretation_upd_state_if_not_in :
  forall t s I v1 v2 w,
    free_vars_sub_restrict_term s t = EA_assignables []
    -> dynamic_semantics_term (adjoint_interpretation s I v1) w t
       = dynamic_semantics_term (adjoint_interpretation s I v2) w t.
Proof.
  term_ind t Case; introv e; simpl in *; auto.

  { Case "KTfuncOf".
    apply coincidence_term; auto.

    { apply free_vars_sub_restrict_term_KTfuncOf_nil_implies_free_vars_lookup_func_nil in e.
      rewrite e; auto. }

    { assert (Vector.map (dynamic_semantics_term (adjoint_interpretation s I v1) w) args
              = Vector.map (dynamic_semantics_term (adjoint_interpretation s I v2) w) args) as xx;
        [|rewrite xx; auto].
      apply eq_vec_map; introv i.
      apply IHargs; auto.
      pose proof (eassignables_subset_funcof s f n args a i) as q.
      rewrite e in q.
      apply eassignables_subset_nil_implies in q; auto. }
  }

  { Case "KTneg".
    f_equal.
    apply IHt.
    pose proof (eassignables_subset_neg s t) as q; rewrite e in q.
    apply eassignables_subset_nil_implies in q; auto. }

  { Case "KTplus".
    f_equal.
    { apply IHt1.
      pose proof (eassignables_subset_plus1 s t1 t2) as q; rewrite e in q.
      apply eassignables_subset_nil_implies in q; auto. }
    { apply IHt2.
      pose proof (eassignables_subset_plus2 s t1 t2) as q; rewrite e in q.
      apply eassignables_subset_nil_implies in q; auto. }
  }

  { Case "KTminus".
    f_equal.
    { apply IHt1.
      pose proof (eassignables_subset_minus1 s t1 t2) as q; rewrite e in q.
      apply eassignables_subset_nil_implies in q; auto. }
    { apply IHt2.
      pose proof (eassignables_subset_minus2 s t1 t2) as q; rewrite e in q.
      apply eassignables_subset_nil_implies in q; auto. }
  }

  { Case "KTtimes".
    f_equal.
    { apply IHt1.
      pose proof (eassignables_subset_times1 s t1 t2) as q; rewrite e in q.
      apply eassignables_subset_nil_implies in q; auto. }
    { apply IHt2.
      pose proof (eassignables_subset_times2 s t1 t2) as q; rewrite e in q.
      apply eassignables_subset_nil_implies in q; auto. }
  }

  { Case "KTdifferential".
    apply big_sum_ext; introv i.
    f_equal.
    apply Derive_ext; introv.
    apply IHt; auto.
    pose proof (eassignables_subset_diff s t) as q.
    rewrite e in q.
    apply eassignables_subset_nil_implies; auto. }
Qed.

(*
Lemma dynamic_semantics_adjoint_interpretation_upd_state_not_in :
  forall t s u x v z I,
    uniform_substitution_term t s = Some u
    -> ~ In x (term_assignables u)
    -> dynamic_semantics_term (adjoint_interpretation s I v) (upd_state v x z) t
       = dynamic_semantics_term (adjoint_interpretation s I v) v t.
Proof.
  term_ind t Case; introv ust ni; simpl in *; auto;
    unfold ret in *; ginv; simpl in *; tcsp;
      try (complete (dest_sub w; ginv; symmetry in Heqw; simpl in *;
                     dest_sub y; ginv; symmetry in Heqy; simpl in *;
                     rw in_app_iff in ni; apply not_or in ni; repnd;
                     rewrite (IHt1 s t x v z I); auto;
                     rewrite (IHt2 s t0 x v z I); auto)).

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => uniform_substitution_term a s) args)) as vop.
    destruct vop; symmetry in Heqvop; simpl in *; ginv.

    pose proof (substitution_dots_term_assign_not_in_some_implies
                  DTN (lookup_func s f n) t u x) as q.
    repeat (autodimp q hyp); repnd.

    repeat (rewrite (dynamic_semantics_term_upd_interpretation_dots_remove_when_no_dot
                       _ _ _ args)).

    f_equal.
    f_equal.
    apply eq_vec_map; introv i.
    apply (in_vec_mapn DTN) in i; exrepnd; subst.
    dest_cases w; symmetry in Heqw.
    rewrite minus_Sn_m in Heqw; auto.
    autorewrite with core in Heqw.
    rewrite sub_sub_same_prop1 in Heqw; try omega.

    pose proof (q m) as h; clear q; repeat (autodimp h hyp).

    pose proof (vec_opt2opt_vec_map_some_implies_some
                  args t
                  (fun a => uniform_substitution_term a s)
                  m (KTnumber 0)) as q.
    simpl in q; repeat (autodimp q hyp).
    remember (uniform_substitution_term (vec_nth args m (KTnumber 0)) s) as opt; symmetry in Heqopt.
    destruct opt; tcsp; subst.

    eapply IHargs;[|eauto|]; auto. }

  { Case "KTread".
    unfold upd_state_var, upd_state; dest_cases w; subst.
    simpl in *; apply not_or in ni; tcsp. }

  { Case "KTneg".
    dest_sub w; ginv; symmetry in Heqw; simpl in *.
    rewrite (IHt s t0 x v z I); auto. }

  { Case "KTdifferential".
    apply big_sum_ext; introv i.
    unfold on_test in ust; dest_cases w; symmetry in Heqw.
    dest_sub y; ginv; symmetry in Heqy; simpl in *.

    unfold upd_state at 1.
    dest_cases z.
    apply Rmult_eq_compat_l.

    apply U_admissible_term_all_implies in Heqw.

    unfold upd_state_var at 3, upd_state at 1.
    dest_cases k; ginv.

    {
      symmetry.
      erewrite Derive_ext;[|introv; apply (IHt s t0); auto].
      rewrite Derive_const.

      erewrite Derive_ext;
        [|introv;
          apply (substitution_adjoint_admissible_term0 _ _ _ (upd_state_var v x z));
          rewrite Heqw; apply equal_states_on_ea_nil].
      erewrite Derive_ext;[|introv; apply (IHt s t0); auto].
      rewrite Derive_const; auto.
    }

    {
      apply Derive_ext; introv.
      rewrite upd_state_var_swap; dest_cases z.
      rewrite (substitution_adjoint_admissible_term0 t s v (upd_state_var v v0 t1) I);
        [|rewrite Heqw; apply equal_states_on_ea_nil].
      rewrite (substitution_adjoint_admissible_term0 t s v (upd_state_var v v0 t1) I);
        [|rewrite Heqw; apply equal_states_on_ea_nil].
      eapply IHt; eauto.
    }
  }
Qed.
*)

(** Uniform substitution for terms --- see Lemma 7. Section 3.1 *)
Lemma us_lemma_term :
  forall s t I v,
    on_uniform_substitution_term
      t s
      (fun x =>
         dynamic_semantics_term I v x
         = dynamic_semantics_term (adjoint_interpretation s I v) v t).
Proof.
  term_ind t Case; introv; simpl; auto;
    unfold on_uniform_substitution_term in *; simpl; auto;
      try (complete (dest_sub w1; dest_sub w2;
                     pose proof (IHt1 I v) as q1 ; repeat (autodimp q1 hyp);
                     pose proof (IHt2 I v) as q2 ; repeat (autodimp q2 hyp);
                     congruence)).

  { Case "KTfuncOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => uniform_substitution_term a s) args)) as vop.
    destruct vop; symmetry in Heqvop; simpl in *; ginv.
    dest_sub ust; symmetry in Hequst.

    pose proof (dynamic_semantics_term_substitution_dots_term
                  (lookup_func s f n) t I v) as q.
    unfold on_substitution_dots_term in q.
    rewrite Hequst in q.
    rewrite q.

    f_equal.
    f_equal.
    apply (eq_vec_map2 DTN); introv ltmn.

    pose proof (vec_opt2opt_vec_map_some_implies_some
                  args t
                  (fun a => uniform_substitution_term a s)
                  m DTN) as w.
    simpl in w; repeat (autodimp w hyp).
    remember (uniform_substitution_term (vec_nth args m DTN) s) as opt; symmetry in Heqopt.
    destruct opt; tcsp; subst.

    pose proof (IHargs (vec_nth args m DTN)) as h; clear IHargs.
    autodimp h hyp.
    pose proof (h I v) as z; clear h.
    rewrite Heqopt in z; auto.
  }

  { Case "KTneg".
    dest_sub w.
    pose proof (IHt I v) as q1 ; repeat (autodimp q1 hyp).
    congruence.
  }

  { Case "KTdifferential".
    unfold on_test; simpl.
    repeat (dest_cases w).
    dest_sub z; ginv; simpl.

    symmetry in Heqz.
    symmetry in Heqw0.
    apply U_admissible_term_all_implies in Heqw0.

    apply big_sum_ext2; auto; introv i j;[| |].

    {
      f_equal.
      apply Derive_ext; introv.
      rewrite IHt.
      apply (substitution_adjoint_admissible_term0 _ _ _ v).
      rewrite Heqw0; apply equal_states_on_ea_nil.
    }

    {
      (* trivial because assumptions of this one are false *)

      pose proof (free_vars_term_closed_uniform_substitution_term t s t0) as h.
      repeat (autodimp h hyp).
      apply h in i; tcsp.
    }

    {
      apply Rmult_eq_0_compat_l.

      erewrite Derive_ext;
        [|introv;
          apply (dynamic_semantics_term_adjoint_interpretation_upd_state_if_not_in
                   _ _ _ _ (upd_state v v0 t1)); auto].

      erewrite Derive_ext;
        [|introv; rewrite <- IHt; reflexivity].

      erewrite Derive_ext;
        [|introv;apply (coincidence_term _ _ v I I); auto].

      { apply Derive_const. }

      { introv xx.
        unfold upd_state; dest_cases w; subst; tcsp. }
    }
  }
Qed.

Lemma var_sub_find_combine_implies_in_domain :
  forall vs rs v t,
    var_sub_find (combine vs rs) v = Some t
    -> In v vs.
Proof.
  induction vs; introv h; simpl in *; ginv.
  destruct rs; simpl in *; ginv.
  dest_cases w.
  apply IHvs in h; tcsp.
Qed.

Lemma equal_states_on_upd_list_state_if_disjoint :
  forall l vars rs v,
    disjoint (vars2assign vars) l
    -> equal_states_on (upd_list_state v (combine vars rs)) v l.
Proof.
  introv d i.
  revert rs.
  induction vars; introv; simpl; auto.
  destruct rs; simpl; auto.
  simpl in *.
  apply disjoint_cons_l in d; repnd.
  unfold upd_state; dest_cases w; subst; tcsp.
Qed.

Ltac dest_sub_n t w :=
  match goal with
  | [ |- context[substitution_dot_term t ?u] ] =>
    remember (substitution_dot_term t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dot_term t ?u] |- _ ] =>
    remember (substitution_dot_term t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dots_term t ?u] ] =>
    remember (substitution_dots_term t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dots_term t ?u] |- _ ] =>
    remember (substitution_dots_term t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dot_term_in_formula t ?u] ] =>
    remember (substitution_dot_term_in_formula t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dot_term_in_formula t ?u] |- _ ] =>
    remember (substitution_dot_term_in_formula t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dots_term_in_formula t ?u] ] =>
    remember (substitution_dots_term_in_formula t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dots_term_in_formula t ?u] |- _ ] =>
    remember (substitution_dots_term_in_formula t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dot_term_in_program t ?u] ] =>
    remember (substitution_dot_term_in_program t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dot_term_in_program t ?u] |- _ ] =>
    remember (substitution_dot_term_in_program t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dots_term_in_program t ?u] ] =>
    remember (substitution_dots_term_in_program t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dots_term_in_program t ?u] |- _ ] =>
    remember (substitution_dots_term_in_program t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dot_term_in_atomic_ode t ?u] ] =>
    remember (substitution_dot_term_in_atomic_ode t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dot_term_in_atomic_ode t ?u] |- _ ] =>
    remember (substitution_dot_term_in_atomic_ode t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dots_term_in_atomic_ode t ?u] ] =>
    remember (substitution_dots_term_in_atomic_ode t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dots_term_in_atomic_ode t ?u] |- _ ] =>
    remember (substitution_dots_term_in_atomic_ode t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dot_term_in_ode t ?u] ] =>
    remember (substitution_dot_term_in_ode t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dot_term_in_ode t ?u] |- _ ] =>
    remember (substitution_dot_term_in_ode t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dots_term_in_ode t ?u] ] =>
    remember (substitution_dots_term_in_ode t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dots_term_in_ode t ?u] |- _ ] =>
    remember (substitution_dots_term_in_ode t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dot_formula_in_formula t ?u] ] =>
    remember (substitution_dot_formula_in_formula t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dot_formula_in_formula t ?u] |- _ ] =>
    remember (substitution_dot_formula_in_formula t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[substitution_dot_formula_in_program t ?u] ] =>
    remember (substitution_dot_formula_in_program t u) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[substitution_dot_formula_in_program t ?u] |- _ ] =>
    remember (substitution_dot_formula_in_program t u) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[uniform_substitution_term t ?s] ] =>
    remember (uniform_substitution_term t s) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[uniform_substitution_term t ?s] |- _ ] =>
    remember (uniform_substitution_term t s) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[uniform_substitution_formula t ?s] ] =>
    remember (uniform_substitution_formula t s) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[uniform_substitution_formula t ?s] |- _ ] =>
    remember (uniform_substitution_formula t s) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[uniform_substitution_program t ?s] ] =>
    remember (uniform_substitution_program t s) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[uniform_substitution_program t ?s] |- _ ] =>
    remember (uniform_substitution_program t s) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[uniform_substitution_atomic_ode t ?s] ] =>
    remember (uniform_substitution_atomic_ode t s) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[uniform_substitution_atomic_ode t ?s] |- _ ] =>
    remember (uniform_substitution_atomic_ode t s) as w;
    destruct w;
    simpl in *;
    auto

  | [ |- context[uniform_substitution_ode t ?s] ] =>
    remember (uniform_substitution_ode t s) as w;
    destruct w;
    simpl in *;
    auto
  | [ H : context[uniform_substitution_ode t ?s] |- _ ] =>
    remember (uniform_substitution_ode t s) as w;
    destruct w;
    simpl in *;
    auto
  end.

Lemma equal_states_on_free_vars_term_if_disj :
  forall l e v w,
    eassignables_disj e (EA_assignables l) = true
    -> equal_states_on_complement v w e
    -> equal_states_on v w l.
Proof.
  introv d ec i.
  apply ec.
  eapply eassignables_disj_prop;[apply eassignables_disj_sym; eauto|].
  simpl; dest_cases w.
Qed.
Hint Resolve equal_states_on_free_vars_term_if_disj : core.

Hint Resolve equal_states_on_sym : core.

Lemma bound_vars_program_KPcomposeN_eq :
  forall p n,
    eassignables_subset
      (bound_vars_program (KPcomposeN p n))
      (bound_vars_program p)
    = true.
Proof.
  induction n; simpl; auto.

  { destruct (bound_vars_program p); auto. }

  { apply eassignables_subset_app_l_true_iff; dands; auto. }
Qed.

Lemma equal_states_on_complement_if_subset :
  forall v w e1 e2,
    equal_states_on_complement v w e1
    -> eassignables_subset e1 e2 = true
    -> equal_states_on_complement v w e2.
Proof.
  introv eqc ss i.
  apply eqc.
  remember (in_eassignables a e1) as b1; destruct b1; auto; symmetry in Heqb1.
  eapply eassignables_subset_prop in ss; eauto.
Qed.

Definition on_uniform_substitution_ode
           (ode : ODE)
           (s   : UniformSubstitution)
           (Q   : ODE -> Prop) : Prop :=
  match uniform_substitution_ode ode s with
  | Some u => Q u
  | None => True
  end.

Definition on_substitution_dot_term_in_ode
           (ode : ODE)
           (u   : Term)
           (Q   : ODE -> Prop) : Prop :=
  match substitution_dot_term_in_ode ode u with
  | Some u => Q u
  | None => True
  end.

Lemma substitution_dot_term_in_ode_upd_interpretation_dot_eqset :
  forall ode I t u,
    on_substitution_dot_term_in_ode
      ode t
      (fun o =>
         eqset
           (ode_footprint_diff I o)
           (ode_footprint_diff
              (upd_interpretation_dot I u)
              ode)).
Proof.
  induction ode; introv.

  { destruct child; simpl.

    { unfold on_substitution_dot_term_in_ode.
      dest_sub w; ginv; simpl; auto. }

    { unfold on_substitution_dot_term_in_ode; simpl.
      dest_sub w. }
  }

  { unfold on_substitution_dot_term_in_ode; simpl.
    dest_sub_n ode1 w; symmetry in Heqw.
    dest_sub z; simpl; symmetry in Heqz.

    pose proof (IHode1 I t u) as q1.
    unfold on_substitution_dot_term_in_ode in q1.
    rewrite Heqw in q1.

    pose proof (IHode2 I t u) as q2.
    unfold on_substitution_dot_term_in_ode in q2.
    rewrite Heqz in q2.

    eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
    apply eqset_sym.
    eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
    apply eqset_sym.

    apply implies_eqset_app_lr; auto.
  }
Qed.

Lemma substitution_dot_term_in_ode_preserves_ode_footprint :
  forall I ode1 ode2 t,
    substitution_dot_term_in_ode ode1 t = Some ode2
    -> eqset (ode_footprint I ode1) (ode_footprint I ode2).
Proof.
  induction ode1; introv sdt; simpl in *.

  { destruct child; simpl in *; ginv; auto.
    dest_sub w; ginv. }

  { dest_sub w; symmetry in Heqw; ginv.
    dest_sub z; symmetry in Heqz; ginv.
    apply IHode1_1 in Heqw.
    apply IHode1_2 in Heqz.

    eapply eqset_trans;[apply eqset_ode_footprint_prod|].
    apply eqset_sym.
    eapply eqset_trans;[apply eqset_ode_footprint_prod|].
    apply eqset_sym.

    apply implies_eqset_app_lr; auto. }
Qed.

Lemma substitution_dot_term_in_ode_preserves_ode_footprint_diff :
  forall I ode1 ode2 t,
    substitution_dot_term_in_ode ode1 t = Some ode2
    -> eqset (ode_footprint_diff I ode1) (ode_footprint_diff I ode2).
Proof.
  induction ode1; introv sdt; simpl in *.

  { destruct child; simpl in *; ginv; auto.
    dest_sub w; ginv. }

  { dest_sub w; symmetry in Heqw; ginv.
    dest_sub z; symmetry in Heqz; ginv.
    apply IHode1_1 in Heqw.
    apply IHode1_2 in Heqz.

    eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
    apply eqset_sym.
    eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
    apply eqset_sym.

    apply implies_eqset_app_lr; auto. }
Qed.

Lemma ode_footprint_ODEsing :
  forall I ds t,
    ode_footprint I (ODEsing ds t)
    = [ds, KD ds].
Proof.
  introv.
  unfold ode_footprint, ode_footprint_diff, ode_footprint_vars; simpl.
  destruct ds; simpl; auto.
Qed.
Hint Rewrite ode_footprint_ODEsing : core.

Lemma ode_vars_upd_interpretation_dot :
  forall I t ode,
    ode_assign (upd_interpretation_dot I t) ode = ode_assign I ode.
Proof.
  induction ode; simpl.

  { destruct child; simpl; auto. }

  { rewrite IHode1, IHode2; auto. }
Qed.
Hint Rewrite ode_vars_upd_interpretation_dot : core.

Lemma ode_vars_upd_interpretation_dots :
  forall I {n} (v : Vector.t R n) ode,
    ode_assign (upd_interpretation_dots I v) ode = ode_assign I ode.
Proof.
  induction ode; simpl.

  { destruct child; simpl; auto. }

  { rewrite IHode1, IHode2; auto. }
Qed.
Hint Rewrite ode_vars_upd_interpretation_dots : core.

Lemma substitution_dot_term_in_ode_preserves_ode_vars :
  forall I ode1 ode2 t,
    substitution_dot_term_in_ode ode1 t = Some ode2
    -> ode_assign I ode1 = ode_assign I ode2.
Proof.
  induction ode1; introv sdt; simpl in *.

  { destruct child; simpl in *; ginv; auto.
    dest_sub w; ginv. }

  { dest_sub w; symmetry in Heqw; ginv.
    dest_sub z; symmetry in Heqz; ginv.
    apply IHode1_1 in Heqw.
    apply IHode1_2 in Heqz.
    rewrite Heqw, Heqz; auto. }
Qed.

Lemma substitution_dots_term_in_ode_preserves_ode_assign :
  forall I ode1 ode2 {n} (v : Vector.t Term n),
    substitution_dots_term_in_ode ode1 v = Some ode2
    -> ode_assign I ode1 = ode_assign I ode2.
Proof.
  induction ode1; introv sdt; simpl in *.

  { destruct child; simpl in *; ginv; auto.
    dest_sub w; ginv. }

  { dest_sub w; symmetry in Heqw; ginv.
    dest_sub z; symmetry in Heqz; ginv.
    apply IHode1_1 in Heqw.
    apply IHode1_2 in Heqz.
    rewrite Heqw, Heqz; auto. }
Qed.

Lemma substitution_dot_term_in_ode_dynamic_semantics_ode_fun :
  forall ode t I v s a,
    equal_states_on v s (free_vars_term t)
    -> eassignables_disj (bound_vars_ode ode) (EA_assignables (free_vars_term t)) = true
    -> on_substitution_dot_term_in_ode
         ode t
         (fun o =>
            (
              dynamic_semantics_ode_fun I o s a
              =
              dynamic_semantics_ode_fun
                (upd_interpretation_dot I (dynamic_semantics_term I v t))
                ode s a
            )).
Proof.
  induction ode; introv eqs disj; simpl in *.

  { destruct child; simpl in *.

    { unfold on_substitution_dot_term_in_ode.
      dest_sub w; ginv; simpl; tcsp. }

    { unfold on_substitution_dot_term_in_ode; simpl.
      dest_sub w; symmetry in Heqw.
      repeat (dest_cases w; GC).
      pose proof (dynamic_semantics_term_substitution_dot_term e t I s) as h.
      unfold on_substitution_dot_term in h.
      rewrite Heqw in h.
      rewrite h.
      f_equal; f_equal.
      apply coincidence_term; auto.
    }
  }

  { unfold on_substitution_dot_term_in_ode; simpl.
    dest_sub_n ode1 w; symmetry in Heqw.
    dest_sub z; simpl; symmetry in Heqz.
    apply eassignables_disj_EAssignables_app_l in disj; repnd.

    pose proof (IHode1 t I v s a) as q1.
    repeat (autodimp q1 hyp).
    unfold on_substitution_dot_term_in_ode in q1.
    rewrite Heqw in q1.

    pose proof (IHode2 t I v s a) as q2.
    repeat (autodimp q2 hyp).
    unfold on_substitution_dot_term_in_ode in q2.
    rewrite Heqz in q2.

    rewrite q1, q2; sp.
  }
Qed.

Lemma substitution_dot_term_in_ode_dynamic_semantics_ode :
  forall ode t I r v (phi : R -> state),
    (forall zeta : preal_upto r, equal_states_on v (phi zeta) (free_vars_term t))
    -> eassignables_disj (bound_vars_ode ode) (EA_assignables (free_vars_term t)) = true
    -> on_substitution_dot_term_in_ode
         ode t
         (fun o =>
            (
              dynamic_semantics_ode I o r phi
              <->
              dynamic_semantics_ode
                (upd_interpretation_dot I (dynamic_semantics_term I v t))
                ode r phi
            )).
Proof.
  introv eqs disj.
  unfold on_substitution_dot_term_in_ode.
  dest_sub z; symmetry in Heqz.
  applydup (substitution_dot_term_in_ode_preserves_ode_vars I) in Heqz as eqodev.
  split; introv h i; simpl in *; autorewrite with core in *.

  { pose proof (h zeta v0) as q; simpl in *.
    rewrite <- eqodev in q; autodimp q hyp; repnd.
    dands; auto.
    rewrite q.
    pose proof (substitution_dot_term_in_ode_dynamic_semantics_ode_fun
                  ode t I v (phi zeta) (KD v0)) as z.
    repeat (autodimp z hyp).
    unfold on_substitution_dot_term_in_ode in z.
    dest_sub w; ginv. }

  { pose proof (h zeta v0) as q; simpl in *.
    autorewrite with core in *.
    rewrite eqodev in q; autodimp q hyp; repnd.
    dands; auto.
    rewrite q.
    pose proof (substitution_dot_term_in_ode_dynamic_semantics_ode_fun
                  ode t I v (phi zeta) (KD v0)) as z.
    repeat (autodimp z hyp).
    unfold on_substitution_dot_term_in_ode in z.
    dest_sub w; ginv. }
Qed.

Lemma ode_footprint_diff_subset_ode_footprint :
  forall I ode, subset (ode_footprint_diff I ode) (ode_footprint I ode).
Proof.
  introv i.
  unfold ode_footprint.
  apply in_app_iff; auto.
Qed.

Lemma eqset_ode_footprint_upd_interpretation_dot :
  forall I t ode,
    eqset
      (ode_footprint (upd_interpretation_dot I t) ode)
      (ode_footprint I ode).
Proof.
  induction ode; simpl.

  { destruct child; simpl; auto. }

  { eapply eqset_trans;[apply eqset_ode_footprint_prod|].
    apply eqset_sym.
    eapply eqset_trans;[apply eqset_ode_footprint_prod|].
    apply eqset_sym.
    apply implies_eqset_app_lr; auto. }
Qed.

Lemma eqset_ode_footprint_diff_upd_interpretation_dot :
  forall I t ode,
    eqset
      (ode_footprint_diff (upd_interpretation_dot I t) ode)
      (ode_footprint_diff I ode).
Proof.
  induction ode; simpl.

  { destruct child; simpl; auto. }

  { eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
    apply eqset_sym.
    eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
    apply eqset_sym.
    apply implies_eqset_app_lr; auto. }
Qed.

Lemma dynamic_semantics_formula_program_substitution_dot_term :
  (forall f (t : Term) I v,
      on_substitution_dot_term_in_formula
        f t
        (fun x =>
           dynamic_semantics_formula I x v
           <-> dynamic_semantics_formula
                 (upd_interpretation_dot I (dynamic_semantics_term I v t))
                 f
                 v))
  /\
  (forall p (t : Term) I v w,
      on_substitution_dot_term_in_program
        p t
        (fun x =>
           dynamic_semantics_program I x v w
           <-> dynamic_semantics_program
                 (upd_interpretation_dot I (dynamic_semantics_term I v t))
                 p
                 v w)).
Proof.
  form_prog_ind Case;
    introv;
    unfold on_substitution_dot_term_in_formula, on_substitution_dot_term_in_program;
    simpl in *; tcsp; auto;
      try (complete (pose proof (dynamic_semantics_term_substitution_dot_term left t I v) as q1;
                     pose proof (dynamic_semantics_term_substitution_dot_term right t I v) as q2;
                     unfold on_substitution_dot_term in *;
                     dest_sub w; dest_sub y; rewrite q1, q2; tcsp));
      try(complete (introv IH1 IH2; introv;
                    pose proof (IH1 t I v) as h1; clear IH1;
                    pose proof (IH2 t I v) as h2; clear IH2;
                    remember (substitution_dot_term_in_formula left t ) as sl; destruct sl; simpl; auto;
                    remember (substitution_dot_term_in_formula right t) as sr; destruct sr; simpl; auto;
                    rewrite h1, h2; tcsp)).

  { Case "KFpredOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => substitution_dot_term a t) a)) as vop.
    destruct vop; symmetry in Heqvop; simpl in *; ginv.
    match goal with
    | [ |- _ _ ?x <-> _ _ ?y ] => assert (x = y) as xx;[|rewrite xx;tcsp];[]
    end.

    apply (eq_vec_map2 DTN); introv ltm.

    pose proof (dynamic_semantics_term_substitution_dot_term
                  (vec_nth a m DTN) t I v) as q.
    unfold on_substitution_dot_term in q.

    pose proof (vec_opt2opt_vec_map_some_implies_some
                  a t0
                  (fun a => substitution_dot_term a t)
                  m DTN) as w.
    simpl in w; repeat (autodimp w hyp).
    remember (substitution_dot_term (vec_nth a m DTN) t) as opt; symmetry in Heqopt.
    destruct opt; tcsp; subst; auto.
  }

  { Case "KFquantifier".
    introv IH1; introv.
    unfold on_test; dest_cases z; symmetry in Heqz.
    apply nullb_prop in Heqz.
    dest_sub w; symmetry in Heqw.

    remember (I (SymbolQuantifier f)) as F; simpl in F.
    destruct F as [F ext]; simpl.
    apply ext; auto; introv.
    pose proof (IH1 t I) as q1; clear IH1.
    rewrite Heqw in q1; auto.
    rewrite q1; clear q1.

    rewrite (coincidence_term t s v I I); tcsp.
    rewrite Heqz; auto.
  }

  { Case "KFnot".
    introv IH1. introv.
    pose proof (IH1 t I v) as q.
    remember (substitution_dot_term_in_formula child t) as pp. destruct pp. simpl. auto.
    rewrite q. tcsp. auto.
  }

  { Case "KFforallVars".
    introv IH1; introv.
    unfold on_test; dest_cases z; symmetry in Heqz.
    apply KAssignables_disj_prop in Heqz.
    dest_sub w; symmetry in Heqw.

    split; introv h len.

    { applydup h in len as dsf.
      pose proof (IH1 t I (upd_list_state v (combine vars rs))) as q; clear IH1.
      rewrite Heqw in q.
      apply q in dsf; clear q.

      rewrite (coincidence_term _ _ v _ I) in dsf; auto.
      apply equal_states_on_upd_list_state_if_disjoint; auto. }

    { applydup h in len as dsf.
      pose proof (IH1 t I (upd_list_state v (combine vars rs))) as q; clear IH1.
      rewrite Heqw in q.
      apply q; clear q.

      rewrite (coincidence_term _ _ v _ I); auto.
      apply equal_states_on_upd_list_state_if_disjoint; auto. }
  }

  { Case "KFexistsVars".
    introv IH1; introv.
    unfold on_test; dest_cases z; symmetry in Heqz.
    apply KAssignables_disj_prop in Heqz.
    dest_sub w; symmetry in Heqw.

    split; introv h; exrepnd; exists rs; dands; auto.

    { pose proof (IH1 t I (upd_list_state v (combine vars rs))) as q; clear IH1.
      rewrite Heqw in q.
      apply q in h0; clear q.

      rewrite (coincidence_term _ _ v _ I) in h0; auto.
      apply equal_states_on_upd_list_state_if_disjoint; auto. }

    { pose proof (IH1 t I (upd_list_state v (combine vars rs))) as q; clear IH1.
      rewrite Heqw in q.
      apply q; clear q.

      rewrite (coincidence_term _ _ v _ I); auto.
      apply equal_states_on_upd_list_state_if_disjoint; auto. }
  }

  { Case "KFbox".
    introv IH1 IH2; introv.
    dest_sub_n prog w; ginv; symmetry in Heqw.
    unfold on_test; dest_cases z; symmetry in Heqz.
    dest_sub y; symmetry in Heqy.

    split; intro h; introv q.

    { pose proof (IH1 t I v w) as h1.
      rewrite Heqw in h1.
      apply h1 in q; clear h1.

      applydup bound_effect_lemma in q as eqsc.

      apply h in q; clear h.

      pose proof (IH2 t I w) as h2.
      rewrite Heqy in h2.
      apply h2 in q; clear h2.

      rewrite (coincidence_term _ _ w _ I); eauto 3 with core. }

    { pose proof (IH2 t I w) as h2.
      rewrite Heqy in h2.
      apply h2; clear h2.

      applydup bound_effect_lemma in q as eqsc.

      rewrite (coincidence_term _ _ v _ I); eauto 3 with core.

      pose proof (IH1 t I v w) as h1.
      rewrite Heqw in h1.
      apply h1 in q; clear h1; auto.
    }
  }

  { Case "KFdiamond".
    introv IH1 IH2; introv.
    dest_sub_n prog w; ginv; symmetry in Heqw.
    unfold on_test; dest_cases z; symmetry in Heqz.
    dest_sub y; symmetry in Heqy.

    split; intro h; exrepnd; exists w.

    { pose proof (IH1 t I v w) as q1.
      rewrite Heqw in q1.
      applydup bound_effect_lemma in h0 as eqsc.
      apply q1 in h0; clear q1.

      pose proof (IH2 t I w) as q2.
      rewrite Heqy in q2.
      apply q2 in h1; clear q2.

      dands; auto.

      rewrite (coincidence_term _ _ w _ I); eauto 3 with core. }

    { pose proof (IH2 t I w) as q2.
      rewrite Heqy in q2.
      rewrite q2; clear q2.

      pose proof (IH1 t I v w) as q1.
      rewrite Heqw in q1.
      apply q1 in h0; clear q1.

      applydup bound_effect_lemma in h0 as eqsc.
      dands; auto.

      rewrite (coincidence_term _ _ v _ I); eauto 3 with core. }
  }

  { Case "KPassign".
    pose proof (dynamic_semantics_term_substitution_dot_term e t I v) as h.
    unfold on_substitution_dot_term in h.
    destruct (substitution_dot_term e t); simpl in *; auto.
    rewrite <-h.
    unfold differ_state_except in *.

    split.

    { introv IH1.
      split.
      destruct IH1. auto.
      destruct IH1. rewrite H0. auto. }

    { introv IH1.
      split.
      destruct IH1. auto.
      destruct IH1. rewrite H0. auto. }
  }

  { Case "KPtest".
    introv IH; introv.
    pose proof (IH t I v) as q; clear IH.
    dest_sub z.
    rewrite q; tcsp.
  }

  { Case "KPchoice".
    introv IH1 IH2. introv.
    pose proof (IH1 t I v w) as q1.
    pose proof (IH2 t I v w) as q2.
    dest_sub p1; dest_sub p2.
    rewrite q1; simpl in *; auto.
    rewrite q2; simpl in *; auto. tcsp.
  }

  { Case "KPcompose".
    introv IH1 IH2; introv.
    dest_sub z; symmetry in Heqz.
    unfold on_test.
    dest_cases x; symmetry in Heqx.
    dest_sub y; symmetry in Heqy.

    split; intro h; exrepnd; exists s.

    { pose proof (IH1 t I v s) as q1.
      pose proof (IH2 t I s w) as q2.
      rewrite Heqz in q1.
      rewrite Heqy in q2.
      rewrite <- q1.
      dands; auto.

      applydup bound_effect_lemma in h1 as eqsc.

      rewrite (coincidence_term _ _ s _ I); eauto 3 with core.
      apply q2;auto. }

    { pose proof (IH1 t I v s) as q1.
      pose proof (IH2 t I s w) as q2.
      rewrite Heqz in q1.
      rewrite Heqy in q2.
      rewrite <- q1 in h1; clear q1.
      dands; auto.

      applydup bound_effect_lemma in h1 as eqsc.

      apply q2.
      rewrite (coincidence_term _ _ v _ I); eauto 3 with core. }
  }

  { Case "KPloop".
    introv IH1; introv.
    dest_sub x; symmetry in Heqx.
    unfold on_test.
    dest_cases z; symmetry in Heqz.
    simpl.

    split; intro h; allrw program_close_implies_all;
      exrepnd; exists n; revert w h0;
        induction n; introv dsp; simpl in *; auto;
          exrepnd;
          exists s; dands; auto.

    { pose proof (IH1 t I s w) as q.
      rewrite Heqx in q.
      applydup bound_effect_lemma in dsp1 as eqsc.
      eapply equal_states_on_complement_if_subset in eqsc;
        [|apply bound_vars_program_KPcomposeN_eq].
      rewrite (coincidence_term _ _ s _ I);
        eauto 3 with core.
      apply q; auto.
    }

    { pose proof (IH1 t I s w) as q.
      rewrite Heqx in q; apply q; clear q.
      apply IHn in dsp1.
      applydup bound_effect_lemma in dsp1 as eqsc.
      eapply equal_states_on_complement_if_subset in eqsc;
        [|apply bound_vars_program_KPcomposeN_eq].
      rewrite (coincidence_term _ _ v _ I);
        eauto 3 with core.
    }
  }

  { Case "KPodeSystem".
    introv IH1; introv.
    unfold on_test.
    dest_cases y; symmetry in Heqy.
    dest_sub_n ode z; symmetry in Heqz.
    dest_sub r; symmetry in Heqr.

    split; intro h; exrepnd; subst; exists r phi; dands; auto.

    { introv i; apply h0; intro xx.
      pose proof (substitution_dot_term_in_ode_upd_interpretation_dot_eqset
                    ode I t (dynamic_semantics_term I v t)) as q.
      unfold on_substitution_dot_term_in_ode in q.
      rewrite Heqz in q; apply q in xx; auto. }

    { assert (forall zeta : preal_upto r,
                 equal_states_except v (phi zeta) (ode_footprint I o)) as eqs.
      { introv i.
        pose proof (h1 zeta) as q; repnd.
        rewrite <- q; auto.
        apply h0; intro xx.
        unfold ode_footprint in i; rewrite in_app_iff in i; apply not_or in i; tcsp. }

      assert (forall zeta : preal_upto r,
                 equal_states_on v (phi zeta) (free_vars_term t)) as eqs2.
      {
        apply (substitution_dot_term_in_ode_preserves_ode_footprint I) in Heqz.
        introv i.
        apply eqs.
        intro j.
        apply (eassignables_disj_prop _ _ x) in Heqy.
        { simpl in Heqy; dest_cases w. }
        apply Heqz in j.
        eapply in_ode_footprint_implies_in_bound_vars; eauto.
      }

      pose proof (substitution_dot_term_in_ode_dynamic_semantics_ode
                    ode t I r v phi) as q.
      repeat (autodimp q hyp).
      unfold on_substitution_dot_term_in_ode in q.
      rewrite Heqz in q; apply q; auto. }

    { introv.

      assert (forall zeta : preal_upto r,
                 equal_states_except v (phi zeta) (ode_footprint I o)) as eqs.
      { introv i.
        pose proof (h1 zeta0) as q; repnd.
        rewrite (h0 x);[|intro xx; apply ode_footprint_diff_subset_ode_footprint in xx; tcsp].
        apply q; auto. }

      assert (forall zeta : preal_upto r,
                 equal_states_on v (phi zeta) (free_vars_term t)) as eqs2.
      {
        apply (substitution_dot_term_in_ode_preserves_ode_footprint I) in Heqz.
        introv i.
        apply eqs.
        intro j.
        apply (eassignables_disj_prop _ _ x) in Heqy.
        { simpl in Heqy; dest_cases w. }
        apply Heqz in j.
        eapply in_ode_footprint_implies_in_bound_vars; eauto.
      }

      pose proof (h1 zeta) as q; clear h1; repnd; dands; auto.

      { pose proof (IH1 t I (phi zeta)) as h.
        rewrite Heqr in h.
        apply h in q0; clear h.
        match goal with
        | [ H : dynamic_semantics_formula (_ _ ?x) _ _ |- dynamic_semantics_formula (_ _ ?y) _ _ ] =>
          assert (x = y) as xx;[|rewrite <- xx;auto]
        end.
        apply coincidence_term; auto. }

      { introv i; apply q; intro z; destruct i.
        apply eqset_ode_footprint_upd_interpretation_dot; auto.
        apply (substitution_dot_term_in_ode_preserves_ode_footprint I) in Heqz.
        apply Heqz; auto. }
    }

    { introv i; apply h0; intro j; destruct i.
      apply eqset_ode_footprint_diff_upd_interpretation_dot in j.
      apply (substitution_dot_term_in_ode_preserves_ode_footprint_diff I) in Heqz.
      apply Heqz; auto. }

    { assert (forall zeta : preal_upto r,
                 equal_states_except v (phi zeta) (ode_footprint I o)) as eqs.
      {
        introv i.
        pose proof (h1 zeta) as q; repnd.
        rewrite (h0 x);[apply q|]; intro xx.
        { apply eqset_ode_footprint_upd_interpretation_dot in xx.
          apply (substitution_dot_term_in_ode_preserves_ode_footprint I) in Heqz.
          apply Heqz in xx; tcsp. }
        { apply eqset_ode_footprint_diff_upd_interpretation_dot in xx.
          apply (substitution_dot_term_in_ode_preserves_ode_footprint_diff I) in Heqz.
          apply Heqz in xx; tcsp.
          apply ode_footprint_diff_subset_ode_footprint in xx; tcsp. }
      }

      assert (forall zeta : preal_upto r,
                 equal_states_on v (phi zeta) (free_vars_term t)) as eqs2.
      {
        apply (substitution_dot_term_in_ode_preserves_ode_footprint I) in Heqz.
        introv i.
        apply eqs.
        intro j.
        apply (eassignables_disj_prop _ _ x) in Heqy.
        { simpl in Heqy; dest_cases w. }
        apply Heqz in j.
        eapply in_ode_footprint_implies_in_bound_vars; eauto.
      }

      pose proof (substitution_dot_term_in_ode_dynamic_semantics_ode
                    ode t I r v phi) as q.
      repeat (autodimp q hyp).
      unfold on_substitution_dot_term_in_ode in q.
      rewrite Heqz in q; apply q; auto. }

    { introv.

      assert (forall zeta : preal_upto r,
                 equal_states_except v (phi zeta) (ode_footprint I o)) as eqs.
      {
        introv i.
        pose proof (h1 zeta0) as q; repnd.
        rewrite (h0 x);[apply q|]; intro xx.
        { apply eqset_ode_footprint_upd_interpretation_dot in xx.
          apply (substitution_dot_term_in_ode_preserves_ode_footprint I) in Heqz.
          apply Heqz in xx; tcsp. }
        { apply eqset_ode_footprint_diff_upd_interpretation_dot in xx.
          apply (substitution_dot_term_in_ode_preserves_ode_footprint_diff I) in Heqz.
          apply Heqz in xx; tcsp.
          apply ode_footprint_diff_subset_ode_footprint in xx; tcsp. }
      }

      assert (forall zeta : preal_upto r,
                 equal_states_on v (phi zeta) (free_vars_term t)) as eqs2.
      {
        apply (substitution_dot_term_in_ode_preserves_ode_footprint I) in Heqz.
        introv i.
        apply eqs.
        intro j.
        apply (eassignables_disj_prop _ _ x) in Heqy.
        { simpl in Heqy; dest_cases w. }
        apply Heqz in j.
        eapply in_ode_footprint_implies_in_bound_vars; eauto.
      }

      pose proof (h1 zeta) as q; repnd.

      dands; auto.

      { pose proof (IH1 t I (phi zeta)) as h.
        rewrite Heqr in h.
        apply h; clear h.
        match goal with
        | [ H : dynamic_semantics_formula (_ _ ?x) _ _ |- dynamic_semantics_formula (_ _ ?y) _ _ ] =>
          assert (x = y) as xx;[|rewrite <- xx;auto]
        end.
        apply coincidence_term; auto. }

      { introv i; apply q; intro z; destruct i.
        apply eqset_ode_footprint_upd_interpretation_dot in z; auto.
        apply (substitution_dot_term_in_ode_preserves_ode_footprint I) in Heqz.
        apply Heqz; auto. }
    }
  }
Qed.

Lemma dynamic_semantics_formula_substitution_dot_term :
  forall f (t : Term) I v,
    on_substitution_dot_term_in_formula
      f t
      (fun x =>
         dynamic_semantics_formula I x v
         <-> dynamic_semantics_formula
               (upd_interpretation_dot I (dynamic_semantics_term I v t))
               f
               v).
Proof.
  pose proof dynamic_semantics_formula_program_substitution_dot_term; tcsp.
Qed.

Lemma dynamic_semantics_program_substitution_dot_term :
  forall p (t : Term) I v w,
    on_substitution_dot_term_in_program
      p t
      (fun x =>
         dynamic_semantics_program I x v w
         <-> dynamic_semantics_program
               (upd_interpretation_dot I (dynamic_semantics_term I v t))
               p
               v w).
Proof.
  pose proof dynamic_semantics_formula_program_substitution_dot_term; tcsp.
Qed.

Lemma equal_states_on_complement_EA_all :
  forall v w, equal_states_on_complement v w (EA_all []).
Proof.
  introv i; simpl in *; ginv.
Qed.
Hint Resolve equal_states_on_complement_EA_all : core.

Definition on_substitution_dot_formula_in_formula
           (F : Formula)
           (u : Formula)
           (Q : Formula -> Prop) : Prop :=
  match substitution_dot_formula_in_formula F u with
  | Some u => Q u
  | None => True
  end.

Definition on_substitution_dot_formula_in_program
           (P : Program)
           (u : Formula)
           (Q : Program -> Prop) : Prop :=
  match substitution_dot_formula_in_program P u with
  | Some u => Q u
  | None => True
  end.

Lemma dynamic_semantics_term_upd_interpretation_dot_form :
  forall t I v f,
    dynamic_semantics_term
      (upd_interpretation_dot_form I f)
      v
      t
    = dynamic_semantics_term I v t.
Proof.
  term_ind t Case; introv; simpl; tcsp;
    try (complete (rewrite IHt; auto));
    try (complete (rewrite IHt1; rewrite IHt2; auto)).

  { Case "KTfuncOf".
    f_equal.
    apply eq_vec_map; introv i; auto.
  }

  { Case "KTdifferential".
    apply big_sum_ext; introv i.
    apply Rmult_eq_compat_l.
    apply Derive_ext; introv.
    rewrite IHt; auto.
  }
Qed.
Hint Rewrite dynamic_semantics_term_upd_interpretation_dot_form : core.

Lemma eqset_ode_footprint_upd_interpretation_dot_form :
  forall I t ode,
    eqset
      (ode_footprint (upd_interpretation_dot_form I t) ode)
      (ode_footprint I ode).
Proof.
  induction ode; simpl.

  { destruct child; simpl; auto. }

  { eapply eqset_trans;[apply eqset_ode_footprint_prod|].
    apply eqset_sym.
    eapply eqset_trans;[apply eqset_ode_footprint_prod|].
    apply eqset_sym.
    apply implies_eqset_app_lr; auto. }
Qed.

Lemma eqset_ode_footprint_diff_upd_interpretation_dot_form :
  forall I t ode,
    eqset
      (ode_footprint_diff (upd_interpretation_dot_form I t) ode)
      (ode_footprint_diff I ode).
Proof.
  induction ode; simpl.

  { destruct child; simpl; auto. }

  { eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
    apply eqset_sym.
    eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
    apply eqset_sym.
    apply implies_eqset_app_lr; auto. }
Qed.

Lemma dynamic_semantics_ode_fun_upd_interpretation_dot_form :
  forall ode I f s a,
    dynamic_semantics_ode_fun (upd_interpretation_dot_form I f) ode s a
    = dynamic_semantics_ode_fun I ode s a.
Proof.
  induction ode; introv; simpl in *.

  { destruct child; simpl; tcsp.
    dest_cases w.
    apply dynamic_semantics_term_upd_interpretation_dot_form. }

  { simpl.
    rewrite IHode1, IHode2; sp. }
Qed.

Lemma ode_assign_upd_interpretation_dot_form :
  forall I f ode,
    ode_assign (upd_interpretation_dot_form I f) ode = ode_assign I ode.
Proof.
  induction ode; simpl.

  { destruct child; simpl; auto. }

  { rewrite IHode1, IHode2; auto. }
Qed.
Hint Rewrite ode_assign_upd_interpretation_dot_form : core.

Lemma dynamic_semantics_ode_upd_interpretation_dot_form :
  forall ode I r phi f,
    dynamic_semantics_ode (upd_interpretation_dot_form I f) ode r phi
    <-> dynamic_semantics_ode I ode r phi.
Proof.
  introv; split; introv h i; simpl in *.

  { pose proof (h zeta v) as q; simpl in *; autorewrite with core in *.
    autodimp q hyp; repnd.
    dands; auto.
    rewrite q.
    apply dynamic_semantics_ode_fun_upd_interpretation_dot_form. }

  { pose proof (h zeta v) as q; simpl in *; autorewrite with core in *.
    autodimp q hyp; repnd.
    dands; auto.
    rewrite q.
    symmetry.
    apply dynamic_semantics_ode_fun_upd_interpretation_dot_form. }
Qed.

Lemma dynamic_semantics_formula_program_substitution_dot_formula :
  (forall f g I v,
      on_substitution_dot_formula_in_formula
        f g
        (fun x =>
           dynamic_semantics_formula I x v
           <-> dynamic_semantics_formula
                 (upd_interpretation_dot_form
                    I
                    (dynamic_semantics_formula I g))
                 f
                 v))
  /\
  (forall p g I v w,
      on_substitution_dot_formula_in_program
        p g
        (fun x =>
           dynamic_semantics_program I x v w
           <-> dynamic_semantics_program
                 (upd_interpretation_dot_form
                    I
                    (dynamic_semantics_formula I g))
                 p
                 v
                 w)).
Proof.
  form_prog_ind Case;
    introv;
    unfold on_substitution_dot_formula_in_formula, on_substitution_dot_formula_in_program;
    simpl in *; tcsp; auto;
      try (complete (autorewrite with core; tcsp));
      try (complete (introv ih1 ih2; introv;
                     pose proof (ih1 g I v) as h1; clear ih1;
                     pose proof (ih2 g I v) as h2; clear ih2;
                     dest_sub w; dest_sub x; symmetry in Heqw; symmetry in Heqx;
                     rewrite <- h1, <- h2; sp)).

  { Case "KFpredOf".
    match goal with
    | [ |- _ _ ?x <-> _ _ ?y ] => assert (x = y) as xx;[|rewrite xx;tcsp];[]
    end.
    apply (eq_vec_map2 DTN); introv ltm.
    rewrite dynamic_semantics_term_upd_interpretation_dot_form; auto.
  }

  { Case "KFquantifier".
    introv IH1; introv.

    dest_sub w; symmetry in Heqw.

    remember (I (SymbolQuantifier f)) as F; simpl in F.
    destruct F as [F ext]; simpl.
    apply ext; auto; introv.
    pose proof (IH1 g I) as q1; clear IH1.
    rewrite Heqw in q1; auto.
  }

  { Case "KFnot".
    introv IH1. introv.
    pose proof (IH1 g I v) as q.
    dest_sub w.
    rewrite q; tcsp.
  }

  { Case "KFforallVars".
    introv IH1; introv.

    dest_sub w; symmetry in Heqw.

    split; introv h len; applydup h in len as dsf.

    { pose proof (IH1 g I (upd_list_state v (combine vars rs))) as q; clear IH1.
      rewrite Heqw in q.
      apply q in dsf; clear q; auto. }

    { pose proof (IH1 g I (upd_list_state v (combine vars rs))) as q; clear IH1.
      rewrite Heqw in q.
      apply q; clear q; auto. }
  }

  { Case "KFexistsVars".
    introv IH1; introv.
    dest_sub w; symmetry in Heqw.

    split; introv h; exrepnd; exists rs; dands; auto.

    { pose proof (IH1 g I (upd_list_state v (combine vars rs))) as q; clear IH1.
      rewrite Heqw in q.
      apply q in h0; clear q; auto. }

    { pose proof (IH1 g I (upd_list_state v (combine vars rs))) as q; clear IH1.
      rewrite Heqw in q.
      apply q; clear q; auto. }
  }

  { Case "KFbox".
    introv IH1 IH2; introv.
    dest_sub_n prog w; ginv; symmetry in Heqw.
    dest_sub y; symmetry in Heqy.

    split; intro h; introv q.

    { pose proof (IH1 g I v w) as h1.
      rewrite Heqw in h1.
      apply h1 in q; clear h1.
      apply h in q; clear h.

      pose proof (IH2 g I w) as h2.
      rewrite Heqy in h2.
      apply h2 in q; clear h2; auto. }

    { pose proof (IH2 g I w) as h2.
      rewrite Heqy in h2.
      apply h2; clear h2.

      pose proof (IH1 g I v w) as h1.
      rewrite Heqw in h1.
      apply h1 in q; clear h1; auto. }
  }

  { Case "KFdiamond".
    introv IH1 IH2; introv.
    dest_sub_n prog w; ginv; symmetry in Heqw.
    dest_sub y; symmetry in Heqy.

    split; intro h; exrepnd; exists w.

    { pose proof (IH1 g I v w) as q1.
      rewrite Heqw in q1.
      apply q1 in h0; clear q1.

      pose proof (IH2 g I w) as q2.
      rewrite Heqy in q2.
      apply q2 in h1; clear q2; auto. }

    { pose proof (IH2 g I w) as q2.
      rewrite Heqy in q2.
      rewrite q2; clear q2.

      pose proof (IH1 g I v w) as q1.
      rewrite Heqw in q1.
      apply q1 in h0; clear q1; auto. }
  }

  { Case "KPtest".
    introv IH; introv.
    pose proof (IH g I v) as q; clear IH.
    dest_sub z.
    rewrite q; tcsp.
  }

  { Case "KPchoice".
    introv IH1 IH2. introv.
    pose proof (IH1 g I v w) as q1.
    pose proof (IH2 g I v w) as q2.
    dest_sub p1; dest_sub p2.
    rewrite q1; simpl in *; auto.
    rewrite q2; simpl in *; auto; tcsp.
  }

  { Case "KPcompose".
    introv IH1 IH2; introv.
    dest_sub z; symmetry in Heqz.
    dest_sub y; symmetry in Heqy.

    split; intro h; exrepnd; exists s.

    { pose proof (IH1 g I v s) as q1.
      pose proof (IH2 g I s w) as q2.
      rewrite Heqz in q1.
      rewrite Heqy in q2.
      rewrite <- q1.
      dands; auto.
      apply q2;auto. }

    { pose proof (IH1 g I v s) as q1.
      pose proof (IH2 g I s w) as q2.
      rewrite Heqz in q1.
      rewrite Heqy in q2.
      rewrite <- q1 in h1; clear q1.
      dands; auto.
      apply q2; auto. }
  }

  { Case "KPloop".
    introv IH1; introv.
    dest_sub x; symmetry in Heqx.

    split; intro h; allrw program_close_implies_all;
      exrepnd; exists n; revert w h0;
        induction n; introv dsp; simpl in *; auto;
          exrepnd;
          exists s; dands; auto.

    { pose proof (IH1 g I s w) as q.
      rewrite Heqx in q.
      apply q; auto. }

    { pose proof (IH1 g I s w) as q.
      rewrite Heqx in q; apply q; clear q.
      apply IHn in dsp1; auto. }
  }

  { Case "KPodeSystem".
    introv IH1; introv.
    dest_sub y; symmetry in Heqy.

    split; intro h; exrepnd; subst; exists r phi; simpl; dands; auto.

    { introv i; apply h0; intro j; destruct i.
      apply eqset_ode_footprint_diff_upd_interpretation_dot_form; auto. }

    { apply dynamic_semantics_ode_upd_interpretation_dot_form; auto. }

    { introv; pose proof (h1 zeta) as q; clear h1; repnd.
      dands; auto.

      { pose proof (IH1 g I (phi zeta)) as h; clear IH1.
        rewrite Heqy in h; apply h; auto. }

      { introv i; apply q; intro j; destruct i.
        apply eqset_ode_footprint_upd_interpretation_dot_form; auto. }
    }

    { introv i; apply h0; intro j; destruct i.
      apply eqset_ode_footprint_diff_upd_interpretation_dot_form in j; auto. }

    { apply dynamic_semantics_ode_upd_interpretation_dot_form in h3; auto. }

    { introv; pose proof (h1 zeta) as q; clear h1; repnd.
      pose proof (IH1 g I (phi zeta)) as h; clear IH1.
      rewrite Heqy in h.
      apply h in q0; dands; auto.
      introv i; apply q; intro j; destruct i.
      apply eqset_ode_footprint_upd_interpretation_dot_form in j; auto. }
  }
Qed.

Lemma dynamic_semantics_formula_substitution_dot_formula :
  forall f g I v,
    on_substitution_dot_formula_in_formula
      f g
      (fun x =>
         dynamic_semantics_formula I x v
         <-> dynamic_semantics_formula
               (upd_interpretation_dot_form
                  I
                  (dynamic_semantics_formula I g))
               f
               v).
Proof.
  pose proof dynamic_semantics_formula_program_substitution_dot_formula; sp.
Qed.

Lemma dynamic_semantics_program_substitution_dot_formula :
  forall p g I v w,
    on_substitution_dot_formula_in_program
      p g
      (fun x =>
         dynamic_semantics_program I x v w
         <-> dynamic_semantics_program
               (upd_interpretation_dot_form
                  I
                  (dynamic_semantics_formula I g))
               p
               v
               w).
Proof.
  pose proof dynamic_semantics_formula_program_substitution_dot_formula; sp.
Qed.

Definition on_substitution_dots_term_in_formula
           (F : Formula)
           {n}
           (v : Vector.t Term n)
           (Q : Formula -> Prop) : Prop :=
  match substitution_dots_term_in_formula F v with
  | Some u => Q u
  | None => True
  end.

Definition on_substitution_dots_term_in_program
           (P : Program)
           {n}
           (v : Vector.t Term n)
           (Q : Program -> Prop) : Prop :=
  match substitution_dots_term_in_program P v with
  | Some u => Q u
  | None => True
  end.

Lemma subset_free_vars_vec_term :
  forall (n : nat) (v : Vector.t Term n) (t : Term),
    Vector.In t v -> subset (free_vars_term t) (free_vars_vec_term v).
Proof.
  induction n; introv.

  { apply (@Vector.case0
             Term
             (fun v =>
                Vector.In t v -> subset (free_vars_term t) (free_vars_vec_term v)));
      simpl; clear v.
    intro h; inversion h.
  }

  { apply (Vector.caseS' v); introv; clear v; simpl.
    introv i j.
    unfold free_vars_vec_term; simpl.
    apply in_app_iff.
    inversion i; subst; eqDepDec; subst; auto.
    right.
    eapply IHn; eauto. }
Qed.

Definition on_substitution_dots_term_in_ode
           (ode : ODE)
           {n}
           (u   : Vector.t Term n)
           (Q   : ODE -> Prop) : Prop :=
  match substitution_dots_term_in_ode ode u with
  | Some u => Q u
  | None => True
  end.

Lemma substitution_dot_term_in_ode_upd_interpretation_dots_eqset :
  forall ode I {m} (t : Vector.t Term m) {n} (u : Vector.t R n),
    on_substitution_dots_term_in_ode
      ode t
      (fun o =>
         eqset
           (ode_footprint_diff I o)
           (ode_footprint_diff
              (upd_interpretation_dots I u)
              ode)).
Proof.
  induction ode; introv.

  { destruct child; simpl.

    { unfold on_substitution_dots_term_in_ode.
      dest_sub w; ginv; simpl; auto. }

    { unfold on_substitution_dots_term_in_ode; simpl.
      dest_sub w. }
  }

  { unfold on_substitution_dots_term_in_ode; simpl.
    dest_sub_n ode1 w; symmetry in Heqw.
    dest_sub z; simpl; symmetry in Heqz.

    pose proof (IHode1 I m t n u) as q1.
    unfold on_substitution_dots_term_in_ode in q1.
    rewrite Heqw in q1.

    pose proof (IHode2 I m t n u) as q2.
    unfold on_substitution_dots_term_in_ode in q2.
    rewrite Heqz in q2.

    eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
    apply eqset_sym.
    eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
    apply eqset_sym.

    apply implies_eqset_app_lr; auto.
  }
Qed.

Lemma eqset_ode_footprint_upd_interpretation_dots :
  forall I {n} (t : Vector.t R n) ode,
    eqset
      (ode_footprint (upd_interpretation_dots I t) ode)
      (ode_footprint I ode).
Proof.
  induction ode; simpl.

  { destruct child; simpl; auto. }

  { eapply eqset_trans;[apply eqset_ode_footprint_prod|].
    apply eqset_sym.
    eapply eqset_trans;[apply eqset_ode_footprint_prod|].
    apply eqset_sym.
    apply implies_eqset_app_lr; auto. }
Qed.

Lemma eqset_ode_footprint_diff_upd_interpretation_dots :
  forall I {n} (t : Vector.t R n) ode,
    eqset
      (ode_footprint_diff (upd_interpretation_dots I t) ode)
      (ode_footprint_diff I ode).
Proof.
  induction ode; simpl.

  { destruct child; simpl; auto. }

  { eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
    apply eqset_sym.
    eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
    apply eqset_sym.
    apply implies_eqset_app_lr; auto. }
Qed.

Lemma substitution_dots_term_in_ode_preserves_ode_footprint :
  forall I ode1 ode2 {n} (t : Vector.t Term n),
    substitution_dots_term_in_ode ode1 t = Some ode2
    -> eqset (ode_footprint I ode1) (ode_footprint I ode2).
Proof.
  induction ode1; introv sdt; simpl in *.

  { destruct child; simpl in *; ginv; auto.
    dest_sub w; ginv. }

  { dest_sub w; symmetry in Heqw; ginv.
    dest_sub z; symmetry in Heqz; ginv.
    apply IHode1_1 in Heqw.
    apply IHode1_2 in Heqz.

    eapply eqset_trans;[apply eqset_ode_footprint_prod|].
    apply eqset_sym.
    eapply eqset_trans;[apply eqset_ode_footprint_prod|].
    apply eqset_sym.

    apply implies_eqset_app_lr; auto. }
Qed.

Lemma substitution_dots_term_in_ode_preserves_ode_footprint_diff :
  forall I ode1 ode2 {n} (t : Vector.t Term n),
    substitution_dots_term_in_ode ode1 t = Some ode2
    -> eqset (ode_footprint_diff I ode1) (ode_footprint_diff I ode2).
Proof.
  induction ode1; introv sdt; simpl in *.

  { destruct child; simpl in *; ginv; auto.
    dest_sub w; ginv. }

  { dest_sub w; symmetry in Heqw; ginv.
    dest_sub z; symmetry in Heqz; ginv.
    apply IHode1_1 in Heqw.
    apply IHode1_2 in Heqz.

    eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
    apply eqset_sym.
    eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
    apply eqset_sym.

    apply implies_eqset_app_lr; auto. }
Qed.

Lemma substitution_dots_term_in_ode_dynamic_semantics_ode_fun :
  forall ode {n} (t : Vector.t Term n) I v s a,
    equal_states_on v s (free_vars_vec_term t)
    -> eassignables_disj (bound_vars_ode ode) (EA_assignables (free_vars_vec_term t)) = true
    -> on_substitution_dots_term_in_ode
         ode t
         (fun o =>
            (
              dynamic_semantics_ode_fun I o s a
              =
              dynamic_semantics_ode_fun
                (upd_interpretation_dots I (Vector.map (dynamic_semantics_term I v) t))
                ode s a
            )).
Proof.
  induction ode; introv eqs disj; simpl in *.

  { destruct child; simpl in *.

    { unfold on_substitution_dots_term_in_ode.
      dest_sub w; ginv; simpl; tcsp. }

    { unfold on_substitution_dots_term_in_ode; simpl.
      dest_sub w; symmetry in Heqw.
      repeat (dest_cases w; GC).
      pose proof (dynamic_semantics_term_substitution_dots_term e t I s) as h.
      unfold on_substitution_dots_term in h.
      rewrite Heqw in h.
      rewrite h.
      f_equal; f_equal.
      autorewrite with core in *.

      apply eq_vec_map; introv i.

      apply coincidence_term; auto.
      apply equal_states_on_sym; introv j; apply eqs.
      eapply subset_free_vars_vec_term; eauto.
    }
  }

  { unfold on_substitution_dots_term_in_ode; simpl.
    dest_sub_n ode1 w; symmetry in Heqw.
    dest_sub z; simpl; symmetry in Heqz.
    apply eassignables_disj_EAssignables_app_l in disj; repnd.

    pose proof (IHode1 n t I v s a) as q1.
    repeat (autodimp q1 hyp).
    unfold on_substitution_dots_term_in_ode in q1.
    rewrite Heqw in q1.

    pose proof (IHode2 n t I v s a) as q2.
    repeat (autodimp q2 hyp).
    unfold on_substitution_dots_term_in_ode in q2.
    rewrite Heqz in q2.

    rewrite q1, q2; sp.
  }
Qed.

Lemma substitution_dots_term_in_ode_dynamic_semantics_ode :
  forall ode {n} (t : Vector.t Term n) I r v (phi : R -> state),
    (forall zeta : preal_upto r, equal_states_on v (phi zeta) (free_vars_vec_term t))
    -> eassignables_disj (bound_vars_ode ode) (EA_assignables (free_vars_vec_term t)) = true
    -> on_substitution_dots_term_in_ode
         ode t
         (fun o =>
            (
              dynamic_semantics_ode I o r phi
              <->
              dynamic_semantics_ode
                (upd_interpretation_dots I (Vector.map (dynamic_semantics_term I v) t))
                ode r phi
            )).
Proof.
  introv eqs disj.
  unfold on_substitution_dots_term_in_ode.
  dest_sub w; ginv; simpl; tcsp.
  symmetry in Heqw.
  applydup (substitution_dots_term_in_ode_preserves_ode_assign I) in Heqw as eqodev.
  split; introv h i; simpl in *; autorewrite with core in *.

  { pose proof (h zeta v0) as q; simpl in *.
    rewrite <- eqodev in q; autodimp q hyp; repnd.
    dands; auto.
    rewrite q.
    pose proof (substitution_dots_term_in_ode_dynamic_semantics_ode_fun
                  ode t I v (phi zeta) (KD v0)) as z.
    repeat (autodimp z hyp).
    unfold on_substitution_dots_term_in_ode in z.
    dest_sub w; ginv. }

  { pose proof (h zeta v0) as q; simpl in *.
    autorewrite with core in *.
    rewrite eqodev in q; autodimp q hyp; repnd.
    dands; auto.
    rewrite q.
    pose proof (substitution_dots_term_in_ode_dynamic_semantics_ode_fun
                  ode t I v (phi zeta) (KD v0)) as z.
    repeat (autodimp z hyp).
    unfold on_substitution_dots_term_in_ode in z.
    dest_sub w; ginv. }
Qed.

Lemma dynamic_semantics_formula_program_substitution_dots_term :
  (forall f {n} (t : Vector.t Term n) I v,
      on_substitution_dots_term_in_formula
        f t
        (fun x =>
           dynamic_semantics_formula I x v
           <-> dynamic_semantics_formula
                 (upd_interpretation_dots
                    I
                    (Vector.map (dynamic_semantics_term I v) t))
                 f
                 v))
  /\
  (forall p {n} (t : Vector.t Term n) I v w,
      on_substitution_dots_term_in_program
        p t
        (fun x =>
           dynamic_semantics_program I x v w
           <-> dynamic_semantics_program
                 (upd_interpretation_dots
                    I
                    (Vector.map (dynamic_semantics_term I v) t))
                 p
                 v w)).
Proof.
  form_prog_ind Case;
    introv;
    unfold on_substitution_dots_term_in_formula, on_substitution_dots_term_in_program;
    simpl in *; tcsp; auto;
      try (complete (pose proof (dynamic_semantics_term_substitution_dots_term left  t I v) as q1;
                     pose proof (dynamic_semantics_term_substitution_dots_term right t I v) as q2;
                     unfold on_substitution_dots_term in *;
                     dest_sub w; dest_sub y; rewrite q1, q2; tcsp));
      try(complete (introv IH1 IH2; introv;
                    pose proof (IH1 n t I v) as h1; clear IH1;
                    pose proof (IH2 n t I v) as h2; clear IH2;
                    remember (substitution_dots_term_in_formula left  t) as sl; destruct sl; simpl; auto;
                    remember (substitution_dots_term_in_formula right t) as sr; destruct sr; simpl; auto;
                    rewrite h1, h2; tcsp)).

  { Case "KFpredOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => substitution_dots_term a t) a)) as vop.
    destruct vop; symmetry in Heqvop; simpl in *; ginv.
    match goal with
    | [ |- _ _ ?x <-> _ _ ?y ] => assert (x = y) as xx;[|rewrite xx;tcsp];[]
    end.

    apply (eq_vec_map2 DTN); introv ltm.

    pose proof (dynamic_semantics_term_substitution_dots_term
                  (vec_nth a m DTN) t I v) as q.
    unfold on_substitution_dots_term in q.

    pose proof (vec_opt2opt_vec_map_some_implies_some
                  a t0
                  (fun a => substitution_dots_term a t)
                  m DTN) as w.
    simpl in w; repeat (autodimp w hyp).
    remember (substitution_dots_term (vec_nth a m DTN) t) as opt; symmetry in Heqopt.
    destruct opt; tcsp; subst; auto.
  }

  { Case "KFquantifier".
    introv IH1; introv.
    unfold on_test; dest_cases z; symmetry in Heqz.
    apply nullb_prop in Heqz.
    dest_sub w; symmetry in Heqw.

    remember (I (SymbolQuantifier f)) as F; simpl in F.
    destruct F as [F ext]; simpl.
    apply ext; auto; introv.
    pose proof (IH1 n t I) as q1; clear IH1.
    rewrite Heqw in q1; auto.
    rewrite q1; clear q1.

    match goal with
    | [ |- _ (_ _ _ ?x) _ _ <-> _ (_ _ _ ?y) _ _ ] => assert (x = y) as xx;[|rewrite xx;tcsp];[]
    end.
    apply eq_vec_map; introv i.

    rewrite (coincidence_term a0 s v I I); tcsp.
    eapply null_free_vars_vec_term in Heqz;[|eauto].
    rewrite Heqz; auto.
  }

  { Case "KFnot".
    introv IH1. introv.
    pose proof (IH1 n t I v) as q.
    remember (substitution_dots_term_in_formula child t) as pp. destruct pp. simpl. auto.
    rewrite q. tcsp. auto.
  }

  { Case "KFforallVars".
    introv IH1; introv.
    unfold on_test; dest_cases z; symmetry in Heqz.
    apply KAssignables_disj_prop in Heqz.
    dest_sub w; symmetry in Heqw.

    split; introv h len.

    { applydup h in len as dsf.
      pose proof (IH1 n t I (upd_list_state v (combine vars rs))) as q; clear IH1.
      rewrite Heqw in q.
      apply q in dsf; clear q.

      match goal with
      | [ H : _ (_ _ _ ?x) _ _ |- _ (_ _ _ ?y) _ _ ] => assert (x = y) as xx;[|rewrite <- xx;tcsp];[]
      end.
      apply eq_vec_map; introv i.

      apply coincidence_term; auto.
      apply equal_states_on_upd_list_state_if_disjoint; auto.
      introv i1 i2.
      eapply subset_free_vars_vec_term in i2;[|eauto].
      apply Heqz in i1; tcsp. }

    { applydup h in len as dsf.
      pose proof (IH1 n t I (upd_list_state v (combine vars rs))) as q; clear IH1.
      rewrite Heqw in q.
      apply q; clear q.

      match goal with
      | [ H : _ (_ _ _ ?x) _ _ |- _ (_ _ _ ?y) _ _ ] => assert (x = y) as xx;[|rewrite <- xx;tcsp];[]
      end.
      apply eq_vec_map; introv i.

      apply coincidence_term; auto.
      apply equal_states_on_sym.
      apply equal_states_on_upd_list_state_if_disjoint; auto.
      introv i1 i2.
      eapply subset_free_vars_vec_term in i2;[|eauto].
      apply Heqz in i1; tcsp. }
  }

  { Case "KFexistsVars".
    introv IH1; introv.
    unfold on_test; dest_cases z; symmetry in Heqz.
    apply KAssignables_disj_prop in Heqz.
    dest_sub w; symmetry in Heqw.

    split; introv h; exrepnd; exists rs; dands; auto.

    { pose proof (IH1 n t I (upd_list_state v (combine vars rs))) as q; clear IH1.
      rewrite Heqw in q.
      apply q in h0; clear q.

      match goal with
      | [ H : _ (_ _ _ ?x) _ _ |- _ (_ _ _ ?y) _ _ ] => assert (x = y) as xx;[|rewrite <- xx;tcsp];[]
      end.
      apply eq_vec_map; introv i.

      apply coincidence_term; auto.
      apply equal_states_on_upd_list_state_if_disjoint; auto.
      introv i1 i2.
      eapply subset_free_vars_vec_term in i2;[|eauto].
      apply Heqz in i1; tcsp. }

    { pose proof (IH1 n t I (upd_list_state v (combine vars rs))) as q; clear IH1.
      rewrite Heqw in q.
      apply q; clear q.

      match goal with
      | [ H : _ (_ _ _ ?x) _ _ |- _ (_ _ _ ?y) _ _ ] => assert (x = y) as xx;[|rewrite <- xx;tcsp];[]
      end.
      apply eq_vec_map; introv i.

      apply coincidence_term; auto.
      apply equal_states_on_sym.
      apply equal_states_on_upd_list_state_if_disjoint; auto.
      introv i1 i2.
      eapply subset_free_vars_vec_term in i2;[|eauto].
      apply Heqz in i1; tcsp. }
  }

  { Case "KFbox".
    introv IH1 IH2; introv.
    dest_sub_n prog w; ginv; symmetry in Heqw.
    unfold on_test; dest_cases z; symmetry in Heqz.
    dest_sub y; symmetry in Heqy.

    split; intro h; introv q.

    { pose proof (IH1 n t I v w) as h1.
      rewrite Heqw in h1.
      apply h1 in q; clear h1.

      applydup bound_effect_lemma in q as eqsc.

      apply h in q; clear h.

      pose proof (IH2 n t I w) as h2.
      rewrite Heqy in h2.
      apply h2 in q; clear h2.

      match goal with
      | [ H : _ (_ _ _ ?x) _ _ |- _ (_ _ _ ?y) _ _ ] => assert (x = y) as xx;[|rewrite <- xx;tcsp];[]
      end.
      apply eq_vec_map; introv i.

      apply coincidence_term; auto.
      apply equal_states_on_sym.
      eapply equal_states_on_free_vars_term_if_disj;[|eauto].
      eapply eassignables_disj_subset;[|eauto]; simpl.
      apply included_dec_prop.
      apply subset_free_vars_vec_term; auto. }

    { pose proof (IH2 n t I w) as h2.
      rewrite Heqy in h2.
      apply h2; clear h2.

      applydup bound_effect_lemma in q as eqsc.

      pose proof (IH1 n t I v w) as h1.
      rewrite Heqw in h1.
      apply h1 in q; clear h1; auto.
      apply h in q; clear h.

      match goal with
      | [ H : _ (_ _ _ ?x) _ _ |- _ (_ _ _ ?y) _ _ ] => assert (x = y) as xx;[|rewrite <- xx;tcsp];[]
      end.
      apply eq_vec_map; introv i.

      apply coincidence_term; auto.
      eapply equal_states_on_free_vars_term_if_disj;[|eauto].
      eapply eassignables_disj_subset;[|eauto]; simpl.
      apply included_dec_prop.
      apply subset_free_vars_vec_term; auto. }
  }

  { Case "KFdiamond".
    introv IH1 IH2; introv.
    dest_sub_n prog w; ginv; symmetry in Heqw.
    unfold on_test; dest_cases z; symmetry in Heqz.
    dest_sub y; symmetry in Heqy.

    split; intro h; exrepnd; exists w.

    { pose proof (IH1 n t I v w) as q1.
      rewrite Heqw in q1.
      applydup bound_effect_lemma in h0 as eqsc.
      apply q1 in h0; clear q1.

      pose proof (IH2 n t I w) as q2.
      rewrite Heqy in q2.
      apply q2 in h1; clear q2.

      dands; auto.

      match goal with
      | [ H : _ (_ _ _ ?x) _ _ |- _ (_ _ _ ?y) _ _ ] => assert (x = y) as xx;[|rewrite <- xx;tcsp];[]
      end.
      apply eq_vec_map; introv i.

      apply coincidence_term; auto.
      apply equal_states_on_sym.
      eapply equal_states_on_free_vars_term_if_disj;[|eauto].
      eapply eassignables_disj_subset;[|eauto]; simpl.
      apply included_dec_prop.
      apply subset_free_vars_vec_term; auto. }

    { pose proof (IH2 n t I w) as q2.
      rewrite Heqy in q2.
      rewrite q2; clear q2.

      pose proof (IH1 n t I v w) as q1.
      rewrite Heqw in q1.
      apply q1 in h0; clear q1.

      applydup bound_effect_lemma in h0 as eqsc.
      dands; auto.

      match goal with
      | [ H : _ (_ _ _ ?x) _ _ |- _ (_ _ _ ?y) _ _ ] => assert (x = y) as xx;[|rewrite <- xx;tcsp];[]
      end.
      apply eq_vec_map; introv i.

      apply coincidence_term; auto.
      eapply equal_states_on_free_vars_term_if_disj;[|eauto].
      eapply eassignables_disj_subset;[|eauto]; simpl.
      apply included_dec_prop.
      apply subset_free_vars_vec_term; auto. }
  }

  { Case "KPassign".
    pose proof (dynamic_semantics_term_substitution_dots_term e t I v) as h.
    unfold on_substitution_dots_term in h.
    destruct (substitution_dots_term e t); simpl in *; auto.
    rewrite <-h.
    unfold differ_state_except in *.

    split.

    { introv IH1.
      split.
      destruct IH1. auto.
      destruct IH1. rewrite H0. auto. }

    { introv IH1.
      split.
      destruct IH1. auto.
      destruct IH1. rewrite H0. auto. }
  }

  { Case "KPtest".
    introv IH; introv.
    pose proof (IH n t I v) as q; clear IH.
    dest_sub z.
    rewrite q; tcsp.
  }

  { Case "KPchoice".
    introv IH1 IH2. introv.
    pose proof (IH1 n t I v w) as q1.
    pose proof (IH2 n t I v w) as q2.
    dest_sub p1; dest_sub p2.
    rewrite q1; simpl in *; auto.
    rewrite q2; simpl in *; auto. tcsp.
  }

  { Case "KPcompose".
    introv IH1 IH2; introv.
    dest_sub z; symmetry in Heqz.
    unfold on_test.
    dest_cases x; symmetry in Heqx.
    dest_sub y; symmetry in Heqy.

    split; intro h; exrepnd; exists s.

    { pose proof (IH1 n t I v s) as q1.
      pose proof (IH2 n t I s w) as q2.
      rewrite Heqz in q1.
      rewrite Heqy in q2.
      rewrite <- q1; clear q1.
      dands; auto.

      applydup bound_effect_lemma in h1 as eqsc.
      apply q2 in h0; clear q2.

      match goal with
      | [ H : _ (_ _ _ ?x) _ _ _ |- _ (_ _ _ ?y) _ _ _ ] => assert (x = y) as xx;[|rewrite <- xx;tcsp];[]
      end.
      apply eq_vec_map; introv i.

      apply coincidence_term; auto.
      apply equal_states_on_sym.
      eapply equal_states_on_free_vars_term_if_disj;[|eauto].
      eapply eassignables_disj_subset;[|eauto]; simpl.
      apply included_dec_prop.
      apply subset_free_vars_vec_term; auto. }

    { pose proof (IH1 n t I v s) as q1.
      pose proof (IH2 n t I s w) as q2.
      rewrite Heqz in q1.
      rewrite Heqy in q2.
      rewrite <- q1 in h1; clear q1.
      dands; auto.

      applydup bound_effect_lemma in h1 as eqsc.
      apply q2; clear q2.

      match goal with
      | [ H : _ (_ _ _ ?x) _ _ _ |- _ (_ _ _ ?y) _ _ _ ] => assert (x = y) as xx;[|rewrite <- xx;tcsp];[]
      end.
      apply eq_vec_map; introv i.

      apply coincidence_term; auto.
      eapply equal_states_on_free_vars_term_if_disj;[|eauto].
      eapply eassignables_disj_subset;[|eauto]; simpl.
      apply included_dec_prop.
      apply subset_free_vars_vec_term; auto. }
  }

  { Case "KPloop".
    introv IH1; introv.
    dest_sub x; symmetry in Heqx.
    unfold on_test.
    dest_cases z; symmetry in Heqz.
    simpl.

    split; intro h; allrw program_close_implies_all;
      exrepnd; exists n0; revert w h0;
        induction n0; introv dsp; simpl in *; auto;
          exrepnd;
          exists s; dands; auto.

    { pose proof (IH1 n t I s w) as q.
      rewrite Heqx in q.
      applydup bound_effect_lemma in dsp1 as eqsc.
      eapply equal_states_on_complement_if_subset in eqsc;
        [|apply bound_vars_program_KPcomposeN_eq].
      apply q in dsp0; clear q.

      match goal with
      | [ H : _ (_ _ _ ?x) _ _ _ |- _ (_ _ _ ?y) _ _ _ ] => assert (x = y) as xx;[|rewrite <- xx;tcsp];[]
      end.
      apply eq_vec_map; introv i.

      apply coincidence_term; auto.
      apply equal_states_on_sym.
      eapply equal_states_on_free_vars_term_if_disj;[|eauto].
      eapply eassignables_disj_subset;[|eauto]; simpl.
      apply included_dec_prop.
      apply subset_free_vars_vec_term; auto. }

    { pose proof (IH1 n t I s w) as q.
      rewrite Heqx in q; apply q; clear q.
      apply IHn0 in dsp1; clear IHn0.
      applydup bound_effect_lemma in dsp1 as eqsc.
      eapply equal_states_on_complement_if_subset in eqsc;
        [|apply bound_vars_program_KPcomposeN_eq].

      match goal with
      | [ H : _ (_ _ _ ?x) _ _ _ |- _ (_ _ _ ?y) _ _ _ ] => assert (x = y) as xx;[|rewrite <- xx;tcsp];[]
      end.
      apply eq_vec_map; introv i.

      apply coincidence_term; auto.
      eapply equal_states_on_free_vars_term_if_disj;[|eauto].
      eapply eassignables_disj_subset;[|eauto]; simpl.
      apply included_dec_prop.
      apply subset_free_vars_vec_term; auto. }
  }

  { Case "KPodeSystem".
    introv IH1; introv.
    unfold on_test.
    dest_cases y; symmetry in Heqy.
    dest_sub_n ode z; symmetry in Heqz.
    dest_sub r; symmetry in Heqr.

    split; intro h; exrepnd; subst; exists r phi; dands; auto.

    { introv i; apply h0; intro j; destruct i.
      apply eqset_ode_footprint_diff_upd_interpretation_dots.
      apply (substitution_dots_term_in_ode_preserves_ode_footprint_diff I) in Heqz.
      apply Heqz; auto. }

    { assert (forall zeta : preal_upto r,
                 equal_states_except v (phi zeta) (ode_footprint I o)) as eqs.
      { introv i.
        pose proof (h1 zeta) as q; repnd.
        rewrite <- q; auto.
        apply h0; intro xx.
        unfold ode_footprint in i; rewrite in_app_iff in i; apply not_or in i; tcsp. }

      assert (forall zeta : preal_upto r,
                 equal_states_on v (phi zeta) (free_vars_vec_term t)) as eqs2.
      {
        apply (substitution_dots_term_in_ode_preserves_ode_footprint I) in Heqz.
        introv i.
        apply eqs.
        intro j.
        apply (eassignables_disj_prop _ _ x) in Heqy.
        { simpl in Heqy; dest_cases w. }
        apply Heqz in j.
        eapply in_ode_footprint_implies_in_bound_vars; eauto.
      }

      pose proof (substitution_dots_term_in_ode_dynamic_semantics_ode
                    ode t I r v phi) as q.
      repeat (autodimp q hyp).
      unfold on_substitution_dots_term_in_ode in q.
      rewrite Heqz in q; apply q; auto. }

    { introv.

      assert (forall zeta : preal_upto r,
                 equal_states_except v (phi zeta) (ode_footprint I o)) as eqs.
      { introv i.
        pose proof (h1 zeta0) as q; repnd.
        rewrite (h0 x);[|intro xx; apply ode_footprint_diff_subset_ode_footprint in xx; tcsp].
        apply q; auto. }

      assert (forall zeta : preal_upto r,
                 equal_states_on v (phi zeta) (free_vars_vec_term t)) as eqs2.
      {
        apply (substitution_dots_term_in_ode_preserves_ode_footprint I) in Heqz.
        introv i.
        apply eqs.
        intro j.
        apply (eassignables_disj_prop _ _ x) in Heqy.
        { simpl in Heqy; dest_cases w. }
        apply Heqz in j.
        eapply in_ode_footprint_implies_in_bound_vars; eauto.
      }

      pose proof (h1 zeta) as q; clear h1; repnd; dands; auto.

      { pose proof (IH1 n t I (phi zeta)) as h.
        rewrite Heqr in h.
        apply h in q0; clear h.
        match goal with
        | [ H : dynamic_semantics_formula (_ _ ?x) _ _ |- dynamic_semantics_formula (_ _ ?y) _ _ ] =>
          assert (x = y) as xx;[|rewrite <- xx;auto]
        end.

        apply eq_vec_map; introv i.
        apply coincidence_term; auto.
        apply equal_states_on_sym; introv j; apply eqs2.
        eapply subset_free_vars_vec_term; eauto.
      }

      { introv i; apply q; intro z; destruct i.
        apply eqset_ode_footprint_upd_interpretation_dots; auto.
        apply (substitution_dots_term_in_ode_preserves_ode_footprint I) in Heqz.
        apply Heqz; auto. }
    }

    { introv i; apply h0; intro j; destruct i.
      apply eqset_ode_footprint_diff_upd_interpretation_dots in j.
      apply (substitution_dots_term_in_ode_preserves_ode_footprint_diff I) in Heqz.
      apply Heqz; auto. }

    { assert (forall zeta : preal_upto r,
                 equal_states_except v (phi zeta) (ode_footprint I o)) as eqs.
      {
        introv i.
        pose proof (h1 zeta) as q; repnd.
        rewrite (h0 x);[apply q|]; intro xx.
        { apply eqset_ode_footprint_upd_interpretation_dots in xx.
          apply (substitution_dots_term_in_ode_preserves_ode_footprint I) in Heqz.
          apply Heqz in xx; tcsp. }
        { apply eqset_ode_footprint_diff_upd_interpretation_dots in xx.
          apply (substitution_dots_term_in_ode_preserves_ode_footprint_diff I) in Heqz.
          apply Heqz in xx; tcsp.
          apply ode_footprint_diff_subset_ode_footprint in xx; tcsp. }
      }

      assert (forall zeta : preal_upto r,
                 equal_states_on v (phi zeta) (free_vars_vec_term t)) as eqs2.
      {
        apply (substitution_dots_term_in_ode_preserves_ode_footprint I) in Heqz.
        introv i.
        apply eqs.
        intro j.
        apply (eassignables_disj_prop _ _ x) in Heqy.
        { simpl in Heqy; dest_cases w. }
        apply Heqz in j.
        eapply in_ode_footprint_implies_in_bound_vars; eauto.
      }

      pose proof (substitution_dots_term_in_ode_dynamic_semantics_ode
                    ode t I r v phi) as q.
      repeat (autodimp q hyp).
      unfold on_substitution_dots_term_in_ode in q.
      rewrite Heqz in q; apply q; auto. }

    { introv.

      assert (forall zeta : preal_upto r,
                 equal_states_except v (phi zeta) (ode_footprint I o)) as eqs.
      {
        introv i.
        pose proof (h1 zeta0) as q; repnd.
        rewrite (h0 x);[apply q|]; intro xx.
        { apply eqset_ode_footprint_upd_interpretation_dots in xx.
          apply (substitution_dots_term_in_ode_preserves_ode_footprint I) in Heqz.
          apply Heqz in xx; tcsp. }
        { apply eqset_ode_footprint_diff_upd_interpretation_dots in xx.
          apply (substitution_dots_term_in_ode_preserves_ode_footprint_diff I) in Heqz.
          apply Heqz in xx; tcsp.
          apply ode_footprint_diff_subset_ode_footprint in xx; tcsp. }
      }

      assert (forall zeta : preal_upto r,
                 equal_states_on v (phi zeta) (free_vars_vec_term t)) as eqs2.
      {
        apply (substitution_dots_term_in_ode_preserves_ode_footprint I) in Heqz.
        introv i.
        apply eqs.
        intro j.
        apply (eassignables_disj_prop _ _ x) in Heqy.
        { simpl in Heqy; dest_cases w. }
        apply Heqz in j.
        eapply in_ode_footprint_implies_in_bound_vars; eauto.
      }

      pose proof (h1 zeta) as q; repnd.

      dands; auto.

      { pose proof (IH1 n t I (phi zeta)) as h.
        rewrite Heqr in h.
        apply h; clear h.
        match goal with
        | [ H : dynamic_semantics_formula (_ _ ?x) _ _ |- dynamic_semantics_formula (_ _ ?y) _ _ ] =>
          assert (x = y) as xx;[|rewrite <- xx;auto]
        end.

        apply eq_vec_map; introv i.
        apply coincidence_term; auto.
        introv j; apply eqs2.
        eapply subset_free_vars_vec_term; eauto. }

      { introv i; apply q; intro z; destruct i.
        apply eqset_ode_footprint_upd_interpretation_dots in z; auto.
        apply (substitution_dots_term_in_ode_preserves_ode_footprint I) in Heqz.
        apply Heqz; auto. }
    }
  }
Qed.

Lemma dynamic_semantics_formula_substitution_dots_term :
  forall f {n} (t : Vector.t Term n) I v,
    on_substitution_dots_term_in_formula
      f t
      (fun x =>
         dynamic_semantics_formula I x v
         <-> dynamic_semantics_formula
               (upd_interpretation_dots
                  I
                  (Vector.map (dynamic_semantics_term I v) t))
               f
               v).
Proof.
  pose proof dynamic_semantics_formula_program_substitution_dots_term; tcsp.
Qed.

Lemma dynamic_semantics_program_substitution_dots_term :
  forall p {n} (t : Vector.t Term n) I v w,
    on_substitution_dots_term_in_program
      p t
      (fun x =>
         dynamic_semantics_program I x v w
         <-> dynamic_semantics_program
               (upd_interpretation_dots
                  I
                  (Vector.map (dynamic_semantics_term I v) t))
               p
               v w).
Proof.
  pose proof dynamic_semantics_formula_program_substitution_dots_term; tcsp.
Qed.

(*
Lemma eqset_ode_footprint_diff_adjoint_interpretation :
  forall sub I v ode,
    eqset
      (ode_footprint_diff (adjoint_interpretation sub I v) ode)
      (ode_footprint_diff I ode).
Proof.
  induction ode; simpl; auto.

  eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
  apply eqset_sym.
  eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
  apply eqset_sym.

  apply implies_eqset_app_lr; auto.
Qed.

Lemma eqset_ode_footprint_adjoint_interpretation :
  forall sub I v ode,
    eqset
      (ode_footprint (adjoint_interpretation sub I v) ode)
      (ode_footprint I ode).
Proof.
  induction ode; simpl; auto.

  eapply eqset_trans;[apply eqset_ode_footprint_prod|].
  apply eqset_sym.
  eapply eqset_trans;[apply eqset_ode_footprint_prod|].
  apply eqset_sym.

  apply implies_eqset_app_lr; auto.
Qed.

Lemma uniform_substitution_ode_preserves_ode_footprint :
  forall I ode1 ode2 sub,
    uniform_substitution_ode ode1 sub = Some ode2
    -> eqset (ode_footprint I ode1) (ode_footprint I ode2).
Proof.
  induction ode1; introv sdt; simpl in *.

  { destruct child; simpl in *; unfold ret in *; ginv; auto.
    dest_sub w; ginv. }

  { dest_sub w; symmetry in Heqw; ginv.
    dest_sub z; symmetry in Heqz; ginv.
    apply IHode1_1 in Heqw.
    apply IHode1_2 in Heqz.

    eapply eqset_trans;[apply eqset_ode_footprint_prod|].
    apply eqset_sym.
    eapply eqset_trans;[apply eqset_ode_footprint_prod|].
    apply eqset_sym.

    apply implies_eqset_app_lr; auto. }
Qed.

Lemma uniform_substitution_ode_preserves_ode_footprint_diff :
  forall I ode1 ode2 sub,
    uniform_substitution_ode ode1 sub = Some ode2
    -> eqset (ode_footprint_diff I ode1) (ode_footprint_diff I ode2).
Proof.
  induction ode1; introv sdt; simpl in *.

  { destruct child; simpl in *; ginv; auto.
    dest_sub w; ginv. }

  { dest_sub w; symmetry in Heqw; ginv.
    dest_sub z; symmetry in Heqz; ginv.
    apply IHode1_1 in Heqw.
    apply IHode1_2 in Heqz.

    eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
    apply eqset_sym.
    eapply eqset_trans;[apply eqset_ode_footprint_diff_prod|].
    apply eqset_sym.

    apply implies_eqset_app_lr; auto. }
Qed.
*)

Lemma implies_uniform_substitution_entry_in_terms :
  forall a t ode,
    In t (ode2terms ode)
    -> uniform_substitution_entry_in_term a t = true
    -> uniform_substitution_entry_in_terms a (ode2terms ode) = true.
Proof.
  introv i e;
    allrw uniform_substitution_entry_in_term_eq;
    allrw uniform_substitution_entry_in_terms_eq.
  unfold in_signature in *; destruct a; auto; repeat (dest_cases w; GC).
  destruct n0.
  unfold terms_signature.
  rewrite in_flat_map; eexists; dands; eauto.
Qed.

Lemma eassignables_subset_free_vars_sub_restrict_terms :
  forall ode t sub,
    In t (ode2terms ode)
    -> eassignables_subset
         (free_vars_sub_restrict_term sub t)
         (free_vars_sub_restrict_terms sub (ode2terms ode)) = true.
Proof.
  induction sub; introv i; simpl; auto.
  autodimp IHsub hyp.
  unfold free_vars_sub_restrict_term; simpl.
  unfold free_vars_sub_restrict_terms; simpl.
  dest_cases w; dest_cases y; symmetry in Heqw, Heqy; simpl.

  { apply eassignables_subset_app_left_right; auto. }

  { eapply implies_uniform_substitution_entry_in_terms in Heqw;[|eauto].
    rewrite Heqy in Heqw; ginv. }

  { apply implies_eassignables_subset_app_r_true; auto. }
Qed.

Lemma norepeatsb_app :
  forall {T} dec (l1 l2 : list T),
    norepeatsb dec (l1 ++ l2) = true
    <->
    (
      norepeatsb dec l1 = true
      /\ norepeatsb dec l2 = true
      /\ disjoint l1 l2
    ).
Proof.
  induction l1; simpl in *; introv; tcsp.

  { split; introv h; repnd; dands; auto. }

  { repeat (dest_cases w; tcsp).

    { split; tcsp. }

    { apply in_app_iff in i; repndors; tcsp.
      split; intro h; tcsp; repnd.
      apply disjoint_cons_l in h; repnd; tcsp. }

    { rewrite in_app_iff in n.
      apply not_or in n; repnd; tcsp. }

    { rewrite IHl1; clear IHl1.
      rewrite in_app_iff in n.
      apply not_or in n; repnd; GC.
      rewrite disjoint_cons_l.
      split; tcsp. }
  }
Qed.

Lemma wf_ode_prod :
  forall I ode1 ode2,
    wf_ode I (ODEprod ode1 ode2) = true
    <-> (wf_ode I ode1 = true
         /\ wf_ode I ode2 = true
         /\ disjoint (ode_assign I ode1) (ode_assign I ode2)).
Proof.
  introv.
  unfold wf_ode; simpl.
  rewrite norepeatsb_app; tcsp.
Qed.


(*
Lemma dynamic_semantics_ode_iff :
  forall ode I r phi,
    wf_ode I ode = true
    ->
    (
      dynamic_semantics_ode I ode r phi
      <-> (forall
              (zeta : preal_upto r)
              (v : KVariable),
              In v (ode_assign I ode)
              -> ex_derive_R (fun t : R => phi t (KAssignVar v)) zeta
                 /\ phi zeta (DVar v) = Derive (fun t : R => phi t (KAssignVar v)) zeta
                 /\ phi zeta (DVar v) = dynamic_semantics_ode_fun I ode r phi zeta (DVar v))
    ).
Proof.
  induction ode; introv wf; simpl.

  {
    destruct child; simpl; tcsp.

    split; introv h.

    { introv i; repndors; tcsp; subst.
      dest_cases w; tcsp.
      destruct xp; simpl in *; apply h. }

    { introv.
      pose proof (h zeta xp) as q; dest_cases w; autodimp q hyp.
      destruct xp; simpl in *; tcsp. }
  }

  {
    apply wf_ode_prod in wf; repnd.
    rewrite IHode1; auto.
    rewrite IHode2; auto.
    split; intro h; repnd.

    { introv i; apply in_app_iff in i; repndors.
      { pose proof (h0 zeta v i) as q; repnd; dands; auto.

      }
    }
  }
Qed
*)

(*
Lemma dynamic_semantics_ode_fun_var :
  forall I ode s v,
    dynamic_semantics_ode_fun I ode s v = 0%R.
Proof.
  induction ode; introv; simpl.

  { destruct child; simpl; auto. }

  { rewrite IHode1, IHode2; autorewrite with core; auto. }
Qed.
Hint Rewrite dynamic_semantics_ode_fun_var : core.

Lemma dynamic_semantics_ode_fun_diff_diff :
  forall I ode s a,
    dynamic_semantics_ode_fun I ode s (KAssignDiff (KAssignDiff a)) = 0%R.
Proof.
  induction ode; introv; simpl.

  { destruct child; simpl; auto. }

  { rewrite IHode1, IHode2; autorewrite with core; auto. }
Qed.
Hint Rewrite dynamic_semantics_ode_fun_diff_diff : core.
*)

Lemma uniform_substitution_ode_dynamic_semantics_ode_fun :
  forall ode sub I v s a,
    (forall (t : Term),
        In t (ode2terms ode) ->
        equal_states_on_ea v s (free_vars_sub_restrict_term sub t))
    -> on_uniform_substitution_ode
         ode sub
         (fun o =>
            (
              dynamic_semantics_ode_fun I o s a
              =
              dynamic_semantics_ode_fun (adjoint_interpretation sub I v) ode s a
            )
         ).
Proof.
  induction ode; unfold on_uniform_substitution_ode in *; introv cond; simpl in *.

  { destruct child; simpl in *; tcsp.

    dest_sub w; symmetry in Heqw.
    dest_cases w; subst.

    pose proof (us_lemma_term sub e I s) as h.
    unfold on_uniform_substitution_term in h; rewrite Heqw in h.
    rewrite h.
    apply substitution_adjoint_admissible_term0.
    apply equal_states_on_ea_sym.
    apply cond; auto.
  }

  {
    dest_sub_n ode1 w; symmetry in Heqw.
    dest_sub z; simpl; symmetry in Heqz.

    pose proof (IHode1 sub I v s a) as q1.
    repeat (autodimp q1 hyp).
    { introv i; apply cond; apply in_app_iff; auto. }
    rewrite Heqw in q1.

    pose proof (IHode2 sub I v s a) as q2.
    repeat (autodimp q2 hyp).
    { introv i; apply cond; apply in_app_iff; auto. }
    rewrite Heqz in q2.

    rewrite q1, q2; sp.
  }
Qed.

Lemma uniform_substitution_ode_preserves_ode_assign :
  forall ode1 ode2 sub I v,
    uniform_substitution_ode ode1 sub = Some ode2
    -> ode_assign (adjoint_interpretation sub I v) ode1 = ode_assign I ode2.
Proof.
  induction ode1; introv uso; simpl in *.

  { destruct child; simpl in *; unfold ret in *; ginv; auto.
    dest_sub w; ginv. }

  { dest_sub w; symmetry in Heqw; ginv.
    dest_sub z; symmetry in Heqz; ginv.
    apply (IHode1_1 _ _ I v) in Heqw.
    apply (IHode1_2 _ _ I v) in Heqz.
    rewrite Heqw, Heqz; auto. }
Qed.

Lemma uniform_substitution_ode_preserves_ode_footprint_diff :
  forall ode1 ode2 sub I v,
    uniform_substitution_ode ode1 sub = Some ode2
    -> ode_footprint_diff (adjoint_interpretation sub I v) ode1
       = ode_footprint_diff I ode2.
Proof.
  introv uso.
  unfold ode_footprint_diff.
  rewrite (uniform_substitution_ode_preserves_ode_assign _ ode2); auto.
Qed.

Lemma uniform_substitution_ode_preserves_ode_footprint_vars :
  forall ode1 ode2 sub I v,
    uniform_substitution_ode ode1 sub = Some ode2
    -> ode_footprint_vars (adjoint_interpretation sub I v) ode1
       = ode_footprint_vars I ode2.
Proof.
  introv uso.
  unfold ode_footprint_vars.
  rewrite (uniform_substitution_ode_preserves_ode_assign _ ode2); auto.
Qed.

Lemma uniform_substitution_ode_preserves_ode_footprint :
  forall ode1 ode2 sub I v,
    uniform_substitution_ode ode1 sub = Some ode2
    -> ode_footprint (adjoint_interpretation sub I v) ode1
       = ode_footprint I ode2.
Proof.
  introv uso.
  unfold ode_footprint.
  rewrite (uniform_substitution_ode_preserves_ode_footprint_vars _ ode2); auto.
  rewrite (uniform_substitution_ode_preserves_ode_footprint_diff _ ode2); auto.
Qed.

Lemma uniform_substitution_ode_dynamic_semantics_ode :
  forall ode sub I r v (phi : R -> state),
    (forall (t : Term) (zeta : preal_upto r),
        In t (ode2terms ode) ->
        equal_states_on_ea v (phi zeta) (free_vars_sub_restrict_term sub t))
    -> on_uniform_substitution_ode
         ode sub
         (fun o =>
            (
              dynamic_semantics_ode I o r phi
              <->
              dynamic_semantics_ode (adjoint_interpretation sub I v) ode r phi
            )
         ).
Proof.
  introv eqs.
  unfold on_uniform_substitution_ode in *.
  dest_sub w; symmetry in Heqw.
  applydup (uniform_substitution_ode_preserves_ode_assign ode o sub I v) in Heqw as xx.
  split; introv h i; simpl in *.

  { rewrite xx in i.
    applydup (h zeta) in i as q; simpl in q; repnd.
    dands; auto.
    rewrite q.
    pose proof (uniform_substitution_ode_dynamic_semantics_ode_fun
                  ode sub I v (phi zeta) (KD v0)) as ed.
    autodimp ed hyp.
    unfold on_uniform_substitution_ode in *.
    rewrite Heqw in ed; auto. }

  { rewrite <- xx in i.
    applydup (h zeta) in i as q; simpl in q; repnd.
    dands; auto.
    rewrite q.
    pose proof (uniform_substitution_ode_dynamic_semantics_ode_fun
                  ode sub I v (phi zeta) (KD v0)) as ed.
    autodimp ed hyp.
    unfold on_uniform_substitution_ode in *.
    rewrite Heqw in ed; auto. }
Qed.

Lemma in_eassignables_bound_vars_ode_false_implies_in_ode_footprint :
  forall ode sub I v x,
    in_eassignables x (bound_vars_ode ode) = false
    -> In x (ode_footprint (adjoint_interpretation sub I v) ode)
    -> In x (ode_footprint I ode).
Proof.
  induction ode; introv i j; simpl in *.

  { destruct child; simpl in *; ginv. }

  { apply in_eassignables_app_false_implies in i; repnd.
    apply eqset_ode_footprint_prod in j.
    apply eqset_ode_footprint_prod.
    allrw in_app_iff; repndors.
    { apply IHode1 in j; tcsp. }
    { apply IHode2 in j; tcsp. }
  }
Qed.

Lemma in_eassignables_bound_vars_ode_false_implies_in_ode_footprint_diff :
  forall ode sub I v x,
    in_eassignables x (bound_vars_ode ode) = false
    -> In x (ode_footprint_diff (adjoint_interpretation sub I v) ode)
    -> In x (ode_footprint_diff I ode).
Proof.
  induction ode; introv i j; simpl in *.

  { destruct child; simpl in *; ginv. }

  { apply in_eassignables_app_false_implies in i; repnd.
    apply eqset_ode_footprint_diff_prod in j.
    apply eqset_ode_footprint_diff_prod.
    allrw in_app_iff; repndors.
    { apply IHode1 in j; tcsp. }
    { apply IHode2 in j; tcsp. }
  }
Qed.

Lemma us_lemma_formula_program :
  (forall f sub I v,
      on_uniform_substitution_formula
        f sub
        (fun F =>
           dynamic_semantics_formula I F v
           <-> dynamic_semantics_formula (adjoint_interpretation sub I v) f v))
  /\
  (forall p sub I v w,
      on_uniform_substitution_program
        p sub
        (fun P =>
           dynamic_semantics_program I P v w
           <-> dynamic_semantics_program (adjoint_interpretation sub I v) p v w)).
Proof.
  form_prog_ind Case;
    introv;
    unfold on_uniform_substitution_formula, on_uniform_substitution_program;
    simpl in *; tcsp; auto;
      try (complete (pose proof (us_lemma_term sub left  I v) as q1;
                     pose proof (us_lemma_term sub right I v) as q2;
                     unfold on_uniform_substitution_term in *;
                     remember (uniform_substitution_term left sub) as sl; destruct sl; simpl; auto;
                     remember (uniform_substitution_term right sub) as sr; destruct sr; simpl; auto;
                     rewrite  <- q1; rewrite <- q2; tcsp));
      try (complete (introv IH1 IH2; introv;
                     pose proof (IH1 sub I v) as h1; clear IH1;
                     pose proof (IH2 sub I v) as h2; clear IH2;
                     remember (uniform_substitution_formula left sub) as sl; destruct sl; simpl; auto;
                     remember (uniform_substitution_formula right sub) as sr; destruct sr; simpl; auto;
                     rewrite h1, h2; tcsp)).

  { Case "KFpredOf".
    remember (vec_opt2opt_vec (Vector.map (fun a : Term => uniform_substitution_term a sub) a)) as vop.
    destruct vop; symmetry in Heqvop; simpl in *; ginv.
    dest_sub w; symmetry in Heqw.

    pose proof (dynamic_semantics_formula_substitution_dots_term
                  (lookup_pred sub f n) t I v) as q.
    unfold on_substitution_dots_term_in_formula in q.
    rewrite Heqw in q.
    rewrite q; clear q.

    match goal with
    | [ |- _ (_ _ _ ?x) _ _ <-> _ (_ _ _ ?y) _ _ ] => assert (x = y) as xx;[|rewrite <- xx;tcsp];[]
    end.
    apply (eq_vec_map2 DTN); introv i.

    pose proof (vec_opt2opt_vec_map_some_implies_some
                  a t
                  (fun a => uniform_substitution_term a sub)
                  m DTN) as w.
    simpl in w; repeat (autodimp w hyp).
    remember (uniform_substitution_term (vec_nth a m DTN) sub) as opt; symmetry in Heqopt.
    destruct opt; tcsp; subst; auto.

    pose proof (us_lemma_term sub (vec_nth a m DTN) I v) as q.
    unfold on_uniform_substitution_term in q.
    rewrite Heqopt in q; auto.
  }

  { Case "KFquantifier".
    introv IH1; introv.
    unfold on_test.
    dest_cases w; symmetry in Heqw.
    dest_sub x; symmetry in Heqx.
    unfold lookup_quant.
    remember (find_quantifier_in_uniform_substitution sub f) as ff;
      destruct ff; simpl in *; symmetry in Heqff.

    {
      dest_sub k; symmetry in Heqk.

      pose proof (IH1 sub I) as xx; rewrite Heqx in xx; clear Heqx.

      pose proof (dynamic_semantics_formula_substitution_dot_formula f1 f0 I v) as yy.
      unfold on_substitution_dot_formula_in_formula in yy.
      rewrite Heqk in yy; clear Heqk.
      rewrite yy; clear yy.
      apply ext_dynamic_semantics_formula; auto.
      apply ext_interpretations_upd_interpretation_dot_form; auto; introv.
      rewrite xx; clear xx.
      eapply substitution_adjoint_admissible_formula; eauto with core.
    }

    {
      remember (I (SymbolQuantifier f)) as F; simpl in F.
      destruct F as [F ext]; simpl.
      apply ext; auto; introv.
      pose proof (IH1 sub I s) as q1; clear IH1.
      rewrite Heqx in q1; clear Heqx.
      rewrite q1; clear q1.
      eapply substitution_adjoint_admissible_formula; eauto with core.
    }
  }

  {  Case "KFnot".
     introv IH1. introv.
     pose proof (IH1 sub I v) as h1; clear IH1.
     remember (uniform_substitution_formula child sub) as sl; destruct sl; simpl; auto.
     rewrite h1. tcsp.
  }

  { Case "KFforallVars".
    introv IH1; introv.
    unfold on_test.
    dest_cases w; symmetry in Heqw.
    pose proof (IH1 sub I) as q; clear IH1.
    remember (uniform_substitution_formula child sub) as sl; destruct sl; simpl; auto.
    split; introv h; introv z; pose proof (h rs z) as xx.

    { apply q in xx.
      eapply substitution_adjoint_admissible_formula; try (exact xx); try (exact Heqw).
      introv i.
      unfold vars2ext in i; simpl in i; dest_cases w; ginv.
      allrw in_map_iff.
      rewrite upd_list_state_decomp.
      destruct a; simpl; auto.
      dest_cases w.
      symmetry in Heqw0.
      destruct n.
      eexists; dands; eauto.
      eapply var_sub_find_combine_implies_in_domain; eauto. }

    { apply q.
      eapply substitution_adjoint_admissible_formula; try (exact xx); try (exact Heqw).
      introv i.
      unfold vars2ext in i; simpl in i; dest_cases w; ginv.
      allrw in_map_iff.
      rewrite upd_list_state_decomp.
      destruct a; simpl; auto.
      dest_cases w.
      symmetry in Heqw0.
      destruct n.
      eexists; dands; eauto.
      eapply var_sub_find_combine_implies_in_domain; eauto. }
  }

  { Case "KFexistsVars".
    introv IH1; introv.
    unfold on_test.
    dest_cases w; symmetry in Heqw.
    pose proof (IH1 sub I) as q; clear IH1.
    remember (uniform_substitution_formula child sub) as sl; destruct sl; simpl; auto.
    split; introv h; exrepnd; exists rs; dands; auto.

    { apply q in h0.
      eapply substitution_adjoint_admissible_formula; try (exact h0); try (exact Heqw).
      introv i.
      unfold vars2ext in i; simpl in i; dest_cases w; ginv.
      allrw in_map_iff.
      rewrite upd_list_state_decomp.
      destruct a; simpl; auto.
      dest_cases w.
      symmetry in Heqw0.
      destruct n.
      eexists; dands; eauto.
      eapply var_sub_find_combine_implies_in_domain; eauto. }

    { apply q.
      eapply substitution_adjoint_admissible_formula; try (exact h0); try (exact Heqw).
      introv i.
      unfold vars2ext in i; simpl in i; dest_cases w; ginv.
      allrw in_map_iff.
      rewrite upd_list_state_decomp.
      destruct a; simpl; auto.
      dest_cases w.
      symmetry in Heqw0.
      destruct n.
      eexists; dands; eauto.
      eapply var_sub_find_combine_implies_in_domain; eauto. }
  }

  { Case "KFbox".
    introv ih1 ih2; introv.
    dest_sub_n prog w; ginv; symmetry in Heqw.
    unfold on_test.
    dest_cases x; symmetry in Heqx.
    dest_sub y; symmetry in Heqy.

    split; intro h; introv q.

    { pose proof (ih1 sub I v w) as h1.
      rewrite Heqw in h1.
      apply h1 in q; clear h1.

      applydup bound_effect_lemma in q as eqsc.

      apply h in q; clear h.

      pose proof (ih2 sub I w) as h2.
      rewrite Heqy in h2.
      apply h2 in q; clear h2; auto.

      eapply substitution_adjoint_admissible_formula; try exact q; try exact Heqx; auto.
    }

    { pose proof (ih2 sub I w) as h2.
      rewrite Heqy in h2.
      apply h2; clear h2.

      applydup bound_effect_lemma in q as eqsc.

      pose proof (ih1 sub I v w) as h1.
      rewrite Heqw in h1.
      apply h1 in q; clear h1; auto.
      apply h in q.

      eapply substitution_adjoint_admissible_formula;
        try exact Heqx; try exact q.
      apply equal_states_on_complement_sym; auto.
    }
  }

  { Case "KFdiamond".
    introv ih1 ih2; introv.
    dest_sub_n prog w; ginv; symmetry in Heqw.
    unfold on_test.
    dest_cases x; symmetry in Heqx.
    dest_sub y; symmetry in Heqy.

    split; intro h; exrepnd; exists w.

    { pose proof (ih1 sub I v w) as q1.
      rewrite Heqw in q1.

      applydup bound_effect_lemma in h0 as eqsc.

      apply q1 in h0; clear q1.
      dands; auto.

      pose proof (ih2 sub I w) as q2.
      rewrite Heqy in q2.
      apply q2 in h1; clear q2.

      eapply substitution_adjoint_admissible_formula;
        try exact Heqx; try exact h1; auto.
    }

    { pose proof (ih2 sub I w) as q2.
      rewrite Heqy in q2.
      rewrite q2; clear q2.

      pose proof (ih1 sub I v w) as q1.
      rewrite Heqw in q1.
      rewrite <- q1 in h0; clear q1.

      applydup bound_effect_lemma in h0 as eqsc.
      dands; auto.

      eapply substitution_adjoint_admissible_formula;
        try exact Heqx; try exact h1.
      apply equal_states_on_complement_sym; auto.
    }
  }

  { Case "KPassign".

    pose proof (us_lemma_term sub e I v) as q1.
    unfold on_uniform_substitution_term in *.
    destruct (uniform_substitution_term e sub). simpl in *.
    rewrite <- q1.

    unfold differ_state_except in *.

    {
      split.

      introv IH1.
      split.
      destruct IH1. auto.
      destruct IH1. rewrite H0. auto.

      introv IH1.
      split.
      destruct IH1. auto.
      destruct IH1. rewrite H0. auto.
    }
    auto.
  }

  { Case "KPtest".
    introv IH; introv.
    pose proof (IH sub I v) as q; clear IH.
    remember (uniform_substitution_formula cond sub) as sl; destruct sl; simpl; auto.
    rewrite q; tcsp.
  }

  { Case "KPchoice".
    introv IH1 IH2. introv.
    pose proof (IH1 sub I v w) as q1.
    pose proof (IH2 sub I v w) as q2.

    remember (uniform_substitution_program left sub) as p1; destruct p1; simpl in *; auto.
    remember (uniform_substitution_program right sub) as p2; destruct p2; simpl in *; auto.
    rewrite q1; simpl in *; auto.
    rewrite q2; simpl in *; auto. tcsp.
  }

  { Case "KPcompose".
    introv IH1 IH2; introv.
    pose proof (IH1 sub I) as q1; clear IH1.
    pose proof (IH2 sub I) as q2; clear IH2.
    remember (uniform_substitution_program left sub) as sl; destruct sl; simpl; auto.
    remember (uniform_substitution_program right sub) as sr; destruct sr; simpl; auto;
      unfold on_test; dest_cases w; simpl.
    symmetry in Heqw0.

    split; introv h; exrepnd.

    {
      applydup q1 in h1.
      applydup q2 in h0.

      exists s; dands; auto.

      apply (substitution_adjoint_admissible_program
               right
               (bound_vars_program p)
               sub s v I s w); auto.
      apply equal_states_on_complement_sym.
      eapply bound_effect_lemma; eauto.
    }

    {
      applydup q1 in h1.

      exists s; dands; auto.
      apply q2.

      apply (substitution_adjoint_admissible_program
               right
               (bound_vars_program p)
               sub s v I s w); auto.
      apply equal_states_on_complement_sym.
      eapply bound_effect_lemma; eauto.
    }
  }

  { Case "KPloop".
    introv ih1; introv.
    dest_sub x; symmetry in Heqx.
    unfold on_test.
    dest_cases z; symmetry in Heqz.
    simpl.

    split; intro h; allrw program_close_implies_all;
      exrepnd; exists n; revert w h0;
        induction n; introv dsp; simpl in *; auto;
          exrepnd;
          exists s; dands; auto.

    { pose proof (ih1 sub I s w) as q.
      rewrite Heqx in q.

      apply q in dsp0; clear q.

      eapply substitution_adjoint_admissible_program;
        try exact Heqz; try exact dsp0.

      applydup bound_effect_lemma in dsp1 as eqsc.
      eapply equal_states_on_complement_if_subset in eqsc;
        [|apply bound_vars_program_KPcomposeN_eq].
      auto.
    }

    { pose proof (ih1 sub I s w) as q.
      rewrite Heqx in q; apply q; clear q.
      apply IHn in dsp1; auto.

      eapply substitution_adjoint_admissible_program;
        try exact Heqz; try exact dsp0.

      applydup bound_effect_lemma in dsp1 as eqsc.
      eapply equal_states_on_complement_if_subset in eqsc;
        [|apply bound_vars_program_KPcomposeN_eq].
      apply equal_states_on_complement_sym; auto.
    }
  }

  { Case "KPodeSystem".
    introv IH1; introv.
    unfold on_test.
    dest_cases y; symmetry in Heqy.
    apply andb_true_iff in Heqy; repnd.
    dest_sub z; symmetry in Heqz.
    dest_sub_n ode o; symmetry in Heqo.

    split; intro h; exrepnd; subst; exists r phi; repnd; dands; auto.

    { introv i; apply h0; intro j; destruct i.
      rewrite (uniform_substitution_ode_preserves_ode_footprint_diff _ o); auto. }

    {
      assert (forall t (zeta : preal_upto r),
                 In t (ode2terms ode)
                 -> equal_states_on_ea v (phi zeta) (free_vars_sub_restrict_term sub t))
        as eqs.
      {
        introv i.
        pose proof (h1 zeta) as q; clear h1; repnd.
        introv j.
        rewrite h0;[rewrite <- q;auto|]; intro z.

        { rewrite <- (uniform_substitution_ode_preserves_ode_footprint ode o sub I (phi zeta)) in z; auto.
          apply in_ode_footprint_implies_in_bound_vars in z.
          unfold U_admissible_terms in Heqy0.
          eapply eassignables_disj_prop in Heqy0;[|exact z].
          pose proof (eassignables_subset_free_vars_sub_restrict_terms ode t sub) as xx.
          autodimp xx hyp.
          eapply eassignables_subset_prop in xx;[|exact j].
          rewrite xx in Heqy0; ginv. }

        { rewrite <- (uniform_substitution_ode_preserves_ode_footprint_diff ode o sub I (phi zeta)) in z; auto.
          apply ode_footprint_diff_subset_ode_footprint in z.
          apply in_ode_footprint_implies_in_bound_vars in z.
          unfold U_admissible_terms in Heqy0.
          eapply eassignables_disj_prop in Heqy0;[|exact z].
          pose proof (eassignables_subset_free_vars_sub_restrict_terms ode t sub) as xx.
          autodimp xx hyp.
          eapply eassignables_subset_prop in xx;[|exact j].
          rewrite xx in Heqy0; ginv. }
      }

      pose proof (uniform_substitution_ode_dynamic_semantics_ode ode sub I r v phi) as q.
      autodimp q hyp.
      unfold on_uniform_substitution_ode in q.
      rewrite Heqo in q; apply q; auto.
    }

    {
      introv; pose proof (h1 zeta) as q; repnd; clear h1.
      dands.

      { pose proof (IH1 sub I (phi zeta)) as h; clear IH1.
        rewrite Heqz in h; apply h in q0; clear h.
        eapply substitution_adjoint_admissible_formula;[exact Heqy| |exact q0].
        introv i.
        rewrite h0;[rewrite <- q;auto|]; intro j.

        { rewrite <- (uniform_substitution_ode_preserves_ode_footprint ode o sub I (phi zeta)) in j; auto.
          apply in_ode_footprint_implies_in_bound_vars in j.
          rewrite i in j; ginv. }

        { rewrite <- (uniform_substitution_ode_preserves_ode_footprint_diff ode o sub I (phi zeta)) in j; auto.
          apply ode_footprint_diff_subset_ode_footprint in j.
          apply in_ode_footprint_implies_in_bound_vars in j.
          rewrite i in j; ginv. }
      }

      { introv i; apply q; intro j; destruct i.
        rewrite (uniform_substitution_ode_preserves_ode_footprint ode o sub I v); auto. }
    }

    {
      introv i; apply h0; intro j; destruct i.
      rewrite (uniform_substitution_ode_preserves_ode_footprint_diff ode o sub I v) in j; auto. }

    {
      pose proof (uniform_substitution_ode_dynamic_semantics_ode ode sub I r v phi) as q.
      autodimp q hyp;
        [|unfold on_uniform_substitution_ode in q;
          rewrite Heqo in q; apply q; auto].

      introv i.
      pose proof (h1 zeta) as q; clear h1; repnd.
      introv j.
      rewrite h0;[apply q|]; intro z.

      { pose proof (in_eassignables_bound_vars_ode_false_implies_in_ode_footprint ode sub I v x) as z1.
        repeat (autodimp z1 hyp).
        { unfold U_admissible_terms in Heqy0.
          apply (eassignables_subset_free_vars_sub_restrict_terms _ _ sub) in i.
          eapply eassignables_disj_subset in Heqy0;[|exact i].
          apply eassignables_disj_sym in Heqy0.
          eapply eassignables_disj_prop in Heqy0;[|exact j]; auto. }
        clear z; rename z1 into z.
        apply in_ode_footprint_implies_in_bound_vars in z.
        unfold U_admissible_terms in Heqy0.
        eapply eassignables_disj_prop in Heqy0;[|exact z].
        pose proof (eassignables_subset_free_vars_sub_restrict_terms ode t sub) as xx.
        autodimp xx hyp.
        eapply eassignables_subset_prop in xx;[|exact j].
        rewrite xx in Heqy0; ginv. }

      { pose proof (in_eassignables_bound_vars_ode_false_implies_in_ode_footprint_diff ode sub I v x) as z1.
        repeat (autodimp z1 hyp).
        { unfold U_admissible_terms in Heqy0.
          apply (eassignables_subset_free_vars_sub_restrict_terms _ _ sub) in i.
          eapply eassignables_disj_subset in Heqy0;[|exact i].
          apply eassignables_disj_sym in Heqy0.
          eapply eassignables_disj_prop in Heqy0;[|exact j]; auto. }
        clear z; rename z1 into z.
        apply ode_footprint_diff_subset_ode_footprint in z.
        apply in_ode_footprint_implies_in_bound_vars in z.
        unfold U_admissible_terms in Heqy0.
        eapply eassignables_disj_prop in Heqy0;[|exact z].
        pose proof (eassignables_subset_free_vars_sub_restrict_terms ode t sub) as xx.
        autodimp xx hyp.
        eapply eassignables_subset_prop in xx;[|exact j].
        rewrite xx in Heqy0; ginv. }
    }

    {
      introv; pose proof (h1 zeta) as q; repnd; clear h1.
      dands.

      { pose proof (IH1 sub I (phi zeta)) as h; clear IH1.
        rewrite Heqz in h; apply h; clear h.
        eapply substitution_adjoint_admissible_formula;[exact Heqy| |exact q0].
        introv i.
        rewrite h0;[rewrite <- q;auto|]; intro j.

        { pose proof (in_eassignables_bound_vars_ode_false_implies_in_ode_footprint ode sub I v a) as z1.
          repeat (autodimp z1 hyp).
          clear j; rename z1 into j.
          apply in_ode_footprint_implies_in_bound_vars in j.
          rewrite i in j; ginv. }

        { pose proof (in_eassignables_bound_vars_ode_false_implies_in_ode_footprint_diff ode sub I v a) as z1.
          repeat (autodimp z1 hyp).
          clear j; rename z1 into j.
          apply ode_footprint_diff_subset_ode_footprint in j.
          apply in_ode_footprint_implies_in_bound_vars in j.
          rewrite i in j; ginv. }
      }

      { introv i; apply q; intro j; destruct i.
        rewrite (uniform_substitution_ode_preserves_ode_footprint ode o sub I v) in j; auto. }
    }
  }
Qed.


(** Uniform substitution for formulas --- see Lemma 8. Section 3.1 *)
Lemma us_lemma_formula :
  forall f sub I v,
    on_uniform_substitution_formula
      f sub
      (fun F =>
         dynamic_semantics_formula I F v
         <-> dynamic_semantics_formula (adjoint_interpretation sub I v) f v).
Proof.
  pose proof us_lemma_formula_program; tcsp.
Qed.

(** Uniform substitution for programs --- see Lemma 9. Section 3.1 *)
Lemma us_lemma_program :
  forall p sub I v w,
    on_uniform_substitution_program
      p sub
      (fun P =>
         dynamic_semantics_program I P v w
         <-> dynamic_semantics_program (adjoint_interpretation sub I v) p v w).
Proof.
  pose proof us_lemma_formula_program; tcsp.
Qed.
