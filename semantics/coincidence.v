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


Require Export static_sem_lemmas.
Require Export ext_interpretation.


(** Coincidence of terms --- see Lemma 2, Section 2.4 *)
Lemma coincidence_term :
  forall t v w I J,
    equal_states_on v w (free_vars_term t)
    -> equal_interpretations_on_ext I J (term_signature t)
    -> dynamic_semantics_term I v t
       = dynamic_semantics_term J w t.
Proof.
  term_ind t Case; simpl; introv h1 h2; auto.

  { Case "KTdot".
    unfold dynamic_semantics_term; simpl.
    apply equal_interpretations_on_ext_cons in h2; sp.
  }

  { Case "KTfuncOf".
    apply equal_interpretations_on_ext_cons in h2; repnd.
    rewrite h0.
    f_equal.
    apply eq_vec_map; introv i.
    apply IHargs; eauto 3 with core.
  }

  { Case "KTread".
    apply equal_states_on_cons in h1; repnd.
    unfold dynamic_semantics_term; simpl; auto.
  }

  { Case "KTneg".
    pose proof (IHt v w I J) as q; repeat (autodimp q hyp).
    rewrite q; auto.
  }

  { Case "KTplus".
    apply equal_states_on_app in h1; repnd.
    apply equal_interpretations_on_ext_app in h2; repnd.
    pose proof (IHt1 v w I J) as q1; repeat (autodimp q1 hyp).
    pose proof (IHt2 v w I J) as q2; repeat (autodimp q2 hyp).
    rewrite q1, q2; auto.
  }

  { Case "KTminus".
    apply equal_states_on_app in h1; repnd.
    apply equal_interpretations_on_ext_app in h2; repnd.
    pose proof (IHt1 v w I J) as q1; repeat (autodimp q1 hyp).
    pose proof (IHt2 v w I J) as q2; repeat (autodimp q2 hyp).
    rewrite q1, q2; auto.
  }

  { Case "KTtimes".
    apply equal_states_on_app in h1; repnd.
    apply equal_interpretations_on_ext_app in h2; repnd.
    pose proof (IHt1 v w I J) as q1; repeat (autodimp q1 hyp).
    pose proof (IHt2 v w I J) as q2; repeat (autodimp q2 hyp).
    rewrite q1, q2; auto.
  }

  { Case "KTdifferential".
    apply equal_states_on_app in h1; repnd.

    pose proof (IHt v w I J) as q; repeat (autodimp q hyp).

    apply big_sum_ext; introv i.
    apply term_assignables_nodup_subset_free_vars_term in i.
    applydup implies_KD_in_map_prime_kassignable in i.
    apply h1 in i0; rewrite i0.
    apply h0 in i; rewrite i.
    f_equal.
    apply Derive_ext; introv.

    pose proof (IHt
                  (upd_state v v0 t0)
                  (upd_state w v0 t0)
                  I J) as z.
    repeat (autodimp z hyp).
    {
      introv j.
      unfold upd_state; dest_cases w.
    }
  }
Qed.

Lemma equal_interpretations_on_ext_implies_eq_dynamic_semantics_ode_fun :
  forall I J ode s a,
    equal_interpretations_on_ext I J (ode_signature ode)
    -> dynamic_semantics_ode_fun I ode s a = dynamic_semantics_ode_fun J ode s a.
Proof.
  induction ode; introv eqi; simpl in *.

  { destruct child; simpl; simpl in *; auto.

    { pose proof (eqi (SymbolODE name)) as q; simpl in q.
      repeat (autodimp q hyp); repnd; auto. }

    { dest_cases w; subst.
      apply coincidence_term; auto. }
  }

  { apply equal_interpretations_on_ext_app in eqi; repnd.
    rewrite IHode1, IHode2; auto. }
Qed.

Lemma dynamic_semantics_ode_upd_solution_at_list :
  forall ode I V s s' vs a,
    eassignables_subset (free_vars_ode ode) V = true
    -> dynamic_semantics_ode_fun I ode s a
       = dynamic_semantics_ode_fun
           I ode
           (fun a : KAssignable =>
              if in_dec KAssignable_dec a vs
              then s a
              else if in_eassignables a V then s a else s' a)
           a.
Proof.
  induction ode; introv eqs; simpl in *.

  { destruct child; simpl; auto.

    { remember (I (SymbolODE name)) as C; simpl in C; destruct C as [bv sem ext].
      clear HeqC; simpl in *.
      apply ext; introv.
      repeat (dest_cases w).
      symmetry in Heqw.
      destruct V; simpl in *; repeat (dest_cases w; GC).
      apply included_dec_nil_implies in eqs; subst; simpl in *; tcsp. }

    { dest_cases w; simpl in *.
      apply coincidence_term; auto.
      introv i; repeat (dest_cases w; GC).
      symmetry in Heqw.
      destruct V; simpl in *; repeat (dest_cases w; GC);
        allrw @included_dec_prop;
        allrw @disj_dec_prop;
        apply eqs in i; tcsp. }
  }

  {
    apply eassignables_subset_app_l_true_iff in eqs; repnd.
    rewrite (IHode1 I V s s' vs a); auto.
    rewrite (IHode2 I V s s' vs a); auto.
  }
Qed.

Lemma implies_dynamic_semantics_ode_upd_solution_at_list :
  forall I J ode v' r phi V vs,
    subset (ode_footprint_diff I ode) vs
    -> dynamic_semantics_ode I ode r phi
    -> equal_interpretations_on_ext I J (ode_signature ode)
    -> eassignables_subset (free_vars_ode ode) V = true
    -> eassignables_subset (EA_assignables (ode_footprint_vars I ode)) V = true
    -> dynamic_semantics_ode
         J ode r
         (upd_solution_at_list phi v' V vs).
Proof.
  introv ssode ds eqi ss1 ss2 i; simpl in *.
  pose proof (ds zeta v) as q; clear ds.
  assert (In v (ode_assign I ode)) as i1.
  { eapply equal_interpretations_on_ext_ode_signature_implies_eqset_ode_vars;
      [eauto|];auto. }
  autodimp q hyp.
  simpl in *.
  repnd.

  assert (In (KD v) (ode_footprint_diff I ode)) as i2.
  { unfold ode_footprint_diff; rewrite in_map_iff; simpl.
    exists v; dands; auto. }
  applydup ssode in i2 as i3.

  assert (In v (ode_footprint_vars I ode)) as i4 by auto.
  assert (in_eassignables v V = true) as i5.
  { destruct V; simpl in *; dest_cases w;
      allrw @included_dec_prop;
      allrw @disj_dec_prop;
      try (apply ss2 in i4; tcsp). }

  unfold upd_solution_at_list; repeat (dest_cases w; GC); dands; tcsp;
    try (complete (apply @ex_derive_const)).

  { rewrite q.
    rewrite (equal_interpretations_on_ext_implies_eq_dynamic_semantics_ode_fun I J); auto.
    apply dynamic_semantics_ode_upd_solution_at_list; auto. }

  { rewrite q.
    rewrite (equal_interpretations_on_ext_implies_eq_dynamic_semantics_ode_fun I J); auto.
    apply dynamic_semantics_ode_upd_solution_at_list; auto. }
Qed.

(** Coincidence of formulas and programs --- see Lemma 4 and Lemma 5, Section 2.4 *)
Lemma coincidence_formula_and_program :
  (forall f v w I J,
      equal_states_on_ea v w (free_vars_formula f)
      -> equal_interpretations_on_ext I J (formula_signature f)
      -> (dynamic_semantics_formula I f v <-> dynamic_semantics_formula J f w))
  /\
  (forall p v v' w I J V,
      eassignables_subset (free_vars_program p) V = true
      -> equal_states_on_ea v v' V
      -> equal_interpretations_on_ext I J (program_signature p)
      -> dynamic_semantics_program I p v w
      -> exists w',
          dynamic_semantics_program J p v' w'
          /\ equal_states_on_ea
               w w'
               (EAssignables_app V (must_bound_vars_program p))).
Proof.
  form_prog_ind Case;
    introv;
    simpl in *; auto;
      (* for comparison operators *)
      try (complete (introv eqs eqi;
                     apply equal_states_on_ea_assigns2ext in eqs;
                     apply equal_states_on_app in eqs; repnd;
                     apply equal_interpretations_on_ext_app in eqi; repnd;
                     rewrite (coincidence_term left v w I J); auto;
                     rewrite (coincidence_term right v w I J); tcsp));
      (* for logical operations *)
      try (complete (introv IH1 IH2 eqs eqi;
                     apply equal_states_on_ea_app in eqs; repnd;
                     apply equal_interpretations_on_ext_app in eqi; repnd;
                     rewrite (IH1 v w I J); auto;
                     rewrite (IH2 v w I J); tcsp)).

  { Case "KFdot".
    introv h1 h2.
    apply equal_interpretations_on_ext_cons in h2; repnd; clear h2.
    simpl in h0.
    apply h0; auto.

  }

  { Case "KFtrue".
    introv eqs eqi; reflexivity.
  }

  { Case "KFfalse".
    introv eqs eqi; reflexivity.
  }

  { Case "KFpredOf".
    introv eqs eqi.
    apply equal_interpretations_on_ext_cons in eqi; repnd.
    simpl in eqi0.
    rewrite eqi0.
    apply equal_states_on_ea_assigns2ext in eqs.
    assert (Vector.map (dynamic_semantics_term I v) a
            = Vector.map (dynamic_semantics_term J w) a) as xx;
      [|rewrite xx;tcsp].
    apply eq_vec_map; introv i.
    apply coincidence_term; eauto 3 with core.
  }

  { Case "KFquantifier".
    introv IH eqs eqi.

    rewrite equal_states_on_ea_all_nil in eqs.
    apply equal_interpretations_on_ext_cons in eqi; repnd.
    simpl in eqi0; apply eqi0; clear eqi0; tcsp.
  }

  { Case "KFnot".
    introv IH eqs eqi.
    rewrite (IH v w I J); tcsp.
  }

  { Case "KFforallVars".
    introv IH eqs eqi.
    split; introv h q; applydup h in q as z.
    - apply (IH (upd_list_state v (combine vars rs))
                (upd_list_state w (combine vars rs))
                I J); auto.
      apply equal_states_on_ea_remove_all_implies_upd_list_state; auto.
    - apply (IH (upd_list_state v (combine vars rs))
                (upd_list_state w (combine vars rs))
                I J); auto.
      apply equal_states_on_ea_remove_all_implies_upd_list_state; auto.
  }

  { Case "KFexistsVars".
    introv IH eqs eqi.
    split; introv h; exrepnd; exists rs; dands; auto.
    - apply (IH (upd_list_state v (combine vars rs))
                (upd_list_state w (combine vars rs))
                I J); auto.
      apply equal_states_on_ea_remove_all_implies_upd_list_state; auto.
    - apply (IH (upd_list_state v (combine vars rs))
                (upd_list_state w (combine vars rs))
                I J); auto.
      apply equal_states_on_ea_remove_all_implies_upd_list_state; auto.
  }

  { Case "KFbox".
    introv IHp IHf eqs eqi.
    apply equal_interpretations_on_ext_app in eqi; repnd.
    apply equal_states_on_ea_app in eqs; repnd.

    split; introv imp dp.

    {
      pose proof (IHp w v w0 J I (free_vars_formula (KFdiamond prog child))) as q;
        simpl in q; clear IHp.
      repeat (autodimp q hyp).

      { rewrite eassignables_subset_iff; introv i.
        apply in_eassignables_app_true_iff; sp. }

      { apply equal_states_on_ea_sym.
        introv i; apply in_eassignables_app_true_iff in i; repndors; tcsp. }

      { apply equal_interpretations_on_ext_sym; auto. }

      exrepnd.
      apply imp in q1.
      apply (IHf w0 w' J I); auto;
        try (complete (apply equal_interpretations_on_ext_sym; auto)).

      introv i.
      apply q0.
      repeat (rewrite in_eassignables_app_true_iff).
      remember (in_eassignables x (must_bound_vars_program prog)) as b; destruct b; tcsp.
      left; right.
      apply in_eassignables_remove_eassignables.
      rewrite <- Heqb; dands; auto.
    }

    {
      pose proof (IHp v w w0 I J (free_vars_formula (KFdiamond prog child))) as q;
        simpl in q; clear IHp.
      repeat (autodimp q hyp).

      { rewrite eassignables_subset_iff; introv i.
        apply in_eassignables_app_true_iff; sp. }

      { introv i; apply in_eassignables_app_true_iff in i; repndors; tcsp. }

      exrepnd.
      apply imp in q1.
      apply (IHf w0 w' I J); auto.

      introv i.
      apply q0.
      repeat (rewrite in_eassignables_app_true_iff).
      remember (in_eassignables x (must_bound_vars_program prog)) as b; destruct b; tcsp.
      left; right.
      apply in_eassignables_remove_eassignables.
      rewrite <- Heqb; dands; auto.
    }
  }

  { Case "KFdiamond".
    introv IHp IHf eqs eqi.
    apply equal_interpretations_on_ext_app in eqi; repnd.
    apply equal_states_on_ea_app in eqs; repnd.

    split; introv q; exrepnd.

    {
      pose proof (IHp v w w0 I J (free_vars_formula (KFdiamond prog child))) as q;
        simpl in q; clear IHp.
      repeat (autodimp q hyp).

      { rewrite eassignables_subset_iff; introv i.
        apply in_eassignables_app_true_iff; sp. }

      { introv i; apply in_eassignables_app_true_iff in i; repndors; tcsp. }

      exrepnd.
      exists w'; dands; auto;[].
      apply (IHf w0 w' I J); auto.

      introv i.
      apply q2.
      repeat (rewrite in_eassignables_app_true_iff).
      remember (in_eassignables x (must_bound_vars_program prog)) as b; destruct b; tcsp.
      left; right.
      apply in_eassignables_remove_eassignables.
      rewrite <- Heqb; dands; auto.
    }

    {
      pose proof (IHp w v w0 J I (free_vars_formula (KFdiamond prog child))) as q;
        simpl in q; clear IHp.
      repeat (autodimp q hyp).

      { rewrite eassignables_subset_iff; introv i.
        apply in_eassignables_app_true_iff; sp. }

      { apply equal_states_on_ea_sym.
        introv i; apply in_eassignables_app_true_iff in i; repndors; tcsp. }

      { apply equal_interpretations_on_ext_sym; auto. }

      exrepnd.
      exists w'; dands; auto;[].
      apply (IHf w0 w' J I); auto;
        try (complete (apply equal_interpretations_on_ext_sym; auto)).

      introv i.
      apply q2.
      repeat (rewrite in_eassignables_app_true_iff).
      remember (in_eassignables x (must_bound_vars_program prog)) as b; destruct b; tcsp.
      left; right.
      apply in_eassignables_remove_eassignables.
      rewrite <- Heqb; dands; auto.
    }
  }

  { Case "KFdifferentialFormula".
    introv IH eqs eqi.
    apply equal_states_on_ea_assigns2ext in eqs.

    tcsp.
  }

  { Case "KPconstant".

    introv xx eqs eqi i; ginv.

    destruct V; ginv; simpl.

    apply equal_interpretations_on_ext_cons in eqi; repnd.
    clear eqi.
    simpl in eqi0.
    exists w.
    rewrite <- (eqi0 v v' w w); tcsp.
    apply included_dec_nil_implies in xx; subst; allsimpl.
    rw equal_states_on_ea_all_nil in eqs; tcsp.
  }

  { Case "KPassign".
    intros xx eqs eqi dse.

    applydup (equal_states_on_ea_eassignables_subset
                v v' (EA_assignables (free_vars_term e)) V) in xx as yy; auto.
    apply equal_states_on_ea_assigns2ext in yy.
    pose proof (coincidence_term e v v' I J) as h.
    repeat (autodimp h hyp).
    rewrite <- h; clear h.

    exists (upd_state v' x (dynamic_semantics_term I v e)); dands.

    { rewrite differ_state_except_iff_upd; auto. }

    rewrite differ_state_except_iff_upd in dse; subst.
    rewrite equal_states_on_ea_app.
    rewrite equal_states_on_ea_assigns2ext.
    rewrite equal_states_on_cons.
    dands; auto.

    { introv i; unfold upd_state; dest_cases w. }

    { unfold upd_state; dest_cases w. }

    { introv i; simpl in *; tcsp. }
  }

  { Case "KPassignAny".
    intros xx eqs eqi dse.
    exrepnd.
    clear xx.

    exists (upd_state v' x r); dands.

    { exists r.
      rewrite differ_state_except_iff_upd; auto. }

    rewrite differ_state_except_iff_upd in dse0; subst.
    rewrite equal_states_on_ea_app.
    rewrite equal_states_on_ea_assigns2ext.
    rewrite equal_states_on_cons.
    dands; auto.

    { introv i; unfold upd_state; dest_cases w. }

    { unfold upd_state; dest_cases w. }

    { introv i; simpl in *; tcsp. }
  }

  { Case "KPtest".
    introv IH ss eqs eqi dsp; repnd; subst.
    autorewrite with core.
    exists v'; dands; auto.

    apply (IH w _ I J); auto.
    introv i; apply eqs.
    eapply eassignables_subset_prop; eauto.
  }

  { Case "KPchoice".
    introv IHl IHr ss eqs eqi dsp.
    apply eassignables_subset_app_l_true_iff in ss; repnd.
    apply equal_interpretations_on_ext_app in eqi; repnd.
    repndors.

    {
      pose proof (IHl v v' w I J V) as h; clear IHl IHr.
      repeat (autodimp h hyp); exrepnd.
      exists w'; dands; auto.
      allrw equal_states_on_ea_app; repnd.
      dands; auto.
      apply implies_equal_states_on_ea_inter; left; auto.
    }

    {
      pose proof (IHr v v' w I J V) as h; clear IHl IHr.
      repeat (autodimp h hyp); exrepnd.
      exists w'; dands; auto.
      allrw equal_states_on_ea_app; repnd.
      dands; auto.
      apply implies_equal_states_on_ea_inter; right; auto.
    }
  }

  { Case "KPcompose".

    introv IHl IHr ss eqs eqi dsp.
    apply eassignables_subset_app_l_true_iff in ss; repnd.
    apply equal_interpretations_on_ext_app in eqi; repnd.
    repndors.
    exrepnd.

    pose proof (IHl v v' s I J V) as hl.
    repeat (autodimp hl hyp); exrepnd.

    pose proof (IHr s w' w I J (EAssignables_app V (must_bound_vars_program left))) as hr.
    repeat (autodimp hr hyp); exrepnd.

    {
      apply (eassignables_subset_app_right _ (must_bound_vars_program left)) in ss.
      eapply eassignables_subset_trans;[clear ss|exact ss].
      apply eassignables_subset_app_remove.
    }

    exists w'0; dands;[exists w';dands;auto|].
    eapply equal_states_on_ea_eassignables_eq;try (exact hr0).
    apply EAssignables_app_assoc.
  }

  { Case "KPparallel".
    introv IH1 IH2 ss eqs eqi sem.
    inversion sem.
  }

  { Case "KPloop".
    introv IH ss eqs eqi ds.
    apply program_close_implies_all in ds; exrepnd.
    autorewrite with core.

    revert dependent w.
    revert dependent v'.
    revert dependent v.
    induction n; introv eqs ds; simpl in *.

    {
      repnd; subst.
      exists v'; dands; auto.
    }

    {
      exrepnd.
      pose proof (IHn v v' eqs s ds1) as q; clear IHn; exrepnd.
      pose proof (IH s w' w I J V) as h; clear IH.
      repeat (autodimp h hyp); exrepnd.
      apply equal_states_on_ea_app in h0; repnd.
      exists w'0; dands; auto.
      eapply program_close_trans; eauto.
    }
  }

  { Case "KPsend".
    introv ss eqs eqi ds; inversion ds.
  }

  { Case "KPreceive".
    introv ss eqs eqi ds; inversion ds.
  }

  { Case "KPbroadcast".
    introv ss eqs eqi ds; inversion ds.
  }

  { Case "KPodeSystem".
    introv IHc ss eqs eqi ds.

    apply eassignables_subset_app_l_true_iff in ss; repnd.
    apply equal_interpretations_on_ext_app in eqi; repnd.
    exrepnd; subst.

    assert (eassignables_subset (EA_assignables (ode_footprint_vars I ode)) V = true) as ixp.
    {
      pose proof (subset_ode_footprint_vars_free_vars_ode I ode) as q.
      eapply eassignables_subset_trans;[exact q|].
      auto.
    }

    exists (upd_solution_at_list phi v' V (ode_footprint_diff I ode) r).
    dands; auto.

    { exists r.
      exists (upd_solution_at_list phi v' V (ode_footprint_diff I ode)).
      dands; auto.

      { introv i.
        unfold upd_solution_at_list; repeat (dest_cases w); tcsp.
        { apply eqset_ode_footprint_diff_if_equal_interpretations_on_ext in eqi0.
          apply eqi0 in i0; sp. }
        { symmetry in Heqw.
          rewrite <- eqs; auto. }
      }

      { eapply implies_dynamic_semantics_ode_upd_solution_at_list;
          try (apply subset_refl); auto. }

      { introv.
        pose proof (ds1 zeta) as q; clear ds1; repnd.
        dands.

        { eapply IHc;[|apply equal_interpretations_on_ext_sym|exact q0];auto.
          introv i.
          rewrite eassignables_subset_iff in ss.
          apply ss in i.
          unfold upd_solution_at_list.
          repeat (dest_cases w). }

        { introv i.
          unfold upd_solution_at_list.
          repeat (dest_cases w).

          { apply eqset_ode_footprint_diff_if_equal_interpretations_on_ext in eqi0.
            apply eqi0 in i0; sp.
            unfold ode_footprint in i.
            rewrite in_app_iff in i; apply not_or in i; tcsp. }

          { symmetry in Heqw.
            apply q.
            apply eqset_ode_footprint_if_equal_interpretations_on_ext in eqi0.
            introv j.
            apply eqi0 in j; auto. }
        }
      }
    }

    {
      apply equal_states_on_ea_app; dands; auto;
        [apply equal_states_on_ea_upd_solution_at_list|].
      introv i.
      unfold upd_solution_at_list.
      dest_cases w.
      dest_cases w.
      symmetry in Heqw.
      destruct (in_dec KAssignable_dec x (ode_footprint_vars I ode)) as [j|j].
      { eapply eassignables_subset_prop in ixp;[rewrite Heqw in ixp;ginv|].
        simpl; dest_cases w. }
      { pose proof (in_bound_vars_ode_prop1 x I ode) as q.
        repeat (autodimp q hyp).
        { unfold ode_footprint; rewrite in_app_iff; sp. }
        apply contains_const_implies_free_vars_ode_all in q.
        rewrite q in ss0.
        apply eassignables_subset_all_implies in ss0; subst; simpl in *; ginv. }
    }
  }
Qed.

(** Coincidence of formulas --- see Lemma 4, Section 2.4 *)
Lemma coincidence_formula :
  forall f v w I J,
    equal_states_on_ea v w (free_vars_formula f)
    -> equal_interpretations_on_ext I J (formula_signature f)
    -> (dynamic_semantics_formula I f v <-> dynamic_semantics_formula J f w).
Proof.
  pose proof coincidence_formula_and_program as h; destruct h; auto.
Qed.

(** Coincidence of formulas and programs --- see Lemma 5, Section 2.4 *)
Lemma coincidence_program :
  forall p v v' w I J V,
    eassignables_subset (free_vars_program p) V = true
    -> equal_states_on_ea v v' V
    -> equal_interpretations_on_ext I J (program_signature p)
    -> dynamic_semantics_program I p v w
    -> exists w',
        dynamic_semantics_program J p v' w'
        /\ equal_states_on_ea
             w w'
             (EAssignables_app V (must_bound_vars_program p)).
Proof.
  pose proof coincidence_formula_and_program as h; destruct h; auto.
Qed.

Lemma coincidence_program_corollary1 :
  forall p v v' w I J,
    equal_states_on_ea v v' (all_vars_program p)
    -> equal_interpretations_on_ext I J (program_signature p)
    -> dynamic_semantics_program I p v w
    -> exists w',
        dynamic_semantics_program J p v' w'
        /\ equal_states_on_ea w w' (all_vars_program p).
Proof.
  introv eqs eqi ds.
  pose proof (coincidence_program p v v' w I J (all_vars_program p)) as h.
  repeat (autodimp h hyp); exrepnd;[].
  exists w'; dands; auto.
  eapply equal_states_on_ea_eassignables_subset;[|exact h0].
  apply implies_eassignables_subset_app_r_true; left; eauto 2 with core.
Qed.

(* this lemma has not been used yet *)
Lemma coincidence_program_corollary2 :
  forall p v v' w I J,
    equal_states_on_ea v v' (remove_eassignables (all_vars_program p) (must_bound_vars_program p))
    -> equal_interpretations_on_ext I J (program_signature p)
    -> dynamic_semantics_program I p v w
    -> exists w',
        dynamic_semantics_program J p v' w'
        /\ equal_states_on_ea w w' (all_vars_program p).
Proof.
  introv eqs eqi ds.
  pose proof (coincidence_program p v v' w I J (remove_eassignables (all_vars_program p) (must_bound_vars_program p))) as h.
  repeat (autodimp h hyp); exrepnd.
Abort.
