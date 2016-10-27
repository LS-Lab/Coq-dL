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

Require Export eassignables_subterm.

(**

  This file contains some additional lemmas which we used in order prove soundness of US rule.

*)


Hint Resolve subset_refl : core.



Lemma subset_uniform_substitution_restriction_term_KTplus_left :
  forall s t1 t2,
    subset (uniform_substitution_restriction_term s t1)
           (uniform_substitution_restriction_term s (KTplus t1 t2)).
Proof.
  introv.
  apply subset_uniform_substitution_restriction_term_subterm; auto.
Qed.
Hint Immediate subset_uniform_substitution_restriction_term_KTplus_left : core.

Lemma subset_uniform_substitution_restriction_term_KTplus_right :
  forall s t1 t2,
    subset (uniform_substitution_restriction_term s t2)
           (uniform_substitution_restriction_term s (KTplus t1 t2)).
Proof.
  introv.
  apply subset_uniform_substitution_restriction_term_subterm; auto.
Qed.
Hint Immediate subset_uniform_substitution_restriction_term_KTplus_right : core.

Lemma eassignables_disj_subset :
  forall e e1 e2,
    eassignables_subset e2 e1 = true
    -> eassignables_disj e e1 = true
    -> eassignables_disj e e2 = true.
Proof.
  introv h1 h2.
  destruct e, e2, e1;
    unfold eassignables_disj in *;
    simpl in *;
    allrw @disj_dec_prop;
    allrw @included_dec_prop; ginv;
    allrw @KAssignables_included_prop; ginv;
    allrw @KAssignables_disj_prop; ginv;
    try (complete (introv i j; apply h1 in j; apply h2 in i; tcsp));
    try (complete (introv i; apply h2 in i; apply h1 in i; tcsp));
    try (complete (introv i; apply h1 in i; apply h2 in i; tcsp)).
Qed.

Lemma U_admissible_term_KTplus_left :
  forall e t1 t2 s,
    U_admissible_term e (KTplus t1 t2) s = true
    -> U_admissible_term e t1 s = true.
Proof.
  unfold U_admissible_term; introv h.
  eapply eassignables_disj_subset;[|exact h]; clear h; eauto 3 with core.
  apply implies_eassignables_subset_free_vars_uniform_substitution.
  apply subset_uniform_substitution_restriction_term_KTplus_left.
Qed.
Hint Resolve U_admissible_term_KTplus_left : core.

Lemma U_admissible_term_KTplus_right :
  forall e t1 t2 s,
    U_admissible_term e (KTplus t1 t2) s = true
    -> U_admissible_term e t2 s = true.
Proof.
  unfold U_admissible_term; introv h.
  eapply eassignables_disj_subset;[|exact h]; clear h; eauto 3 with core.
  apply implies_eassignables_subset_free_vars_uniform_substitution.
  apply subset_uniform_substitution_restriction_term_KTplus_right.
Qed.
Hint Resolve U_admissible_term_KTplus_right : core.

Lemma subset_uniform_substitution_restriction_term_KTminus_left :
  forall s t1 t2,
    subset (uniform_substitution_restriction_term s t1)
           (uniform_substitution_restriction_term s (KTminus t1 t2)).
Proof.
  introv.
  apply subset_uniform_substitution_restriction_term_subterm; auto.
Qed.
Hint Resolve subset_uniform_substitution_restriction_term_KTminus_left : core.

Lemma subset_uniform_substitution_restriction_term_KTminus_right :
  forall s t1 t2,
    subset (uniform_substitution_restriction_term s t2)
           (uniform_substitution_restriction_term s (KTminus t1 t2)).
Proof.
  introv.
  apply subset_uniform_substitution_restriction_term_subterm; auto.
Qed.
Hint Resolve subset_uniform_substitution_restriction_term_KTminus_right : core.

Lemma U_admissible_term_KTminus_left :
  forall e t1 t2 s,
    U_admissible_term e (KTminus t1 t2) s = true
    -> U_admissible_term e t1 s = true.
Proof.
  unfold U_admissible_term; introv h.
  eapply eassignables_disj_subset;[|exact h]; clear h; eauto 3 with core.
  apply implies_eassignables_subset_free_vars_uniform_substitution.
  apply subset_uniform_substitution_restriction_term_KTminus_left.
Qed.
Hint Resolve U_admissible_term_KTminus_left : core.

Lemma U_admissible_term_KTminus_right :
  forall e t1 t2 s,
    U_admissible_term e (KTminus t1 t2) s = true
    -> U_admissible_term e t2 s = true.
Proof.
  unfold U_admissible_term; introv h.
  eapply eassignables_disj_subset;[|exact h]; clear h; eauto 3 with core.
  apply implies_eassignables_subset_free_vars_uniform_substitution.
  apply subset_uniform_substitution_restriction_term_KTminus_right.
Qed.
Hint Resolve U_admissible_term_KTminus_right : core.

Lemma subset_uniform_substitution_restriction_term_KTtimes_left :
  forall s t1 t2,
    subset (uniform_substitution_restriction_term s t1)
           (uniform_substitution_restriction_term s (KTtimes t1 t2)).
Proof.
  introv.
  apply subset_uniform_substitution_restriction_term_subterm; auto.
Qed.
Hint Resolve subset_uniform_substitution_restriction_term_KTtimes_left : core.

Lemma subset_uniform_substitution_restriction_term_KTtimes_right :
  forall s t1 t2,
    subset (uniform_substitution_restriction_term s t2)
           (uniform_substitution_restriction_term s (KTtimes t1 t2)).
Proof.
  introv.
  apply subset_uniform_substitution_restriction_term_subterm; auto.
Qed.
Hint Resolve subset_uniform_substitution_restriction_term_KTtimes_right : core.

Lemma U_admissible_term_KTtimes_left :
  forall e t1 t2 s,
    U_admissible_term e (KTtimes t1 t2) s = true
    -> U_admissible_term e t1 s = true.
Proof.
  unfold U_admissible_term; introv h.
  eapply eassignables_disj_subset;[|exact h]; clear h; eauto 3 with core.
  apply implies_eassignables_subset_free_vars_uniform_substitution.
  apply subset_uniform_substitution_restriction_term_KTtimes_left.
Qed.
Hint Resolve U_admissible_term_KTtimes_left : core.

Lemma U_admissible_term_KTtimes_right :
  forall e t1 t2 s,
    U_admissible_term e (KTtimes t1 t2) s = true
    -> U_admissible_term e t2 s = true.
Proof.
  unfold U_admissible_term; introv h.
  eapply eassignables_disj_subset;[|exact h]; clear h; eauto 3 with core.
  apply implies_eassignables_subset_free_vars_uniform_substitution.
  apply subset_uniform_substitution_restriction_term_KTtimes_right.
Qed.
Hint Resolve U_admissible_term_KTtimes_right : core.

Lemma subset_uniform_substitution_restriction_term_KTdivide_left :
  forall s t1 t2,
    subset (uniform_substitution_restriction_term s t1)
           (uniform_substitution_restriction_term s (KTdivide t1 t2)).
Proof.
  introv.
  apply subset_uniform_substitution_restriction_term_subterm; auto.
Qed.
Hint Resolve subset_uniform_substitution_restriction_term_KTdivide_left : core.

Lemma subset_uniform_substitution_restriction_term_KTdivide_right :
  forall s t1 t2,
    subset (uniform_substitution_restriction_term s t2)
           (uniform_substitution_restriction_term s (KTdivide t1 t2)).
Proof.
  introv.
  apply subset_uniform_substitution_restriction_term_subterm; auto.
Qed.
Hint Resolve subset_uniform_substitution_restriction_term_KTdivide_right : core.

Lemma U_admissible_term_KTdivide_left :
  forall e t1 t2 s,
    U_admissible_term e (KTdivide t1 t2) s = true
    -> U_admissible_term e t1 s = true.
Proof.
  unfold U_admissible_term; introv h.
  eapply eassignables_disj_subset;[|exact h]; clear h; eauto 3 with core.
  apply implies_eassignables_subset_free_vars_uniform_substitution.
  apply subset_uniform_substitution_restriction_term_KTdivide_left.
Qed.
Hint Resolve U_admissible_term_KTdivide_left : core.

Lemma U_admissible_term_KTdivide_right :
  forall e t1 t2 s,
    U_admissible_term e (KTdivide t1 t2) s = true
    -> U_admissible_term e t2 s = true.
Proof.
  unfold U_admissible_term; introv h.
  eapply eassignables_disj_subset;[|exact h]; clear h; eauto 3 with core.
  apply implies_eassignables_subset_free_vars_uniform_substitution.
  apply subset_uniform_substitution_restriction_term_KTdivide_right.
Qed.
Hint Resolve U_admissible_term_KTdivide_right : core.

Lemma subset_uniform_substitution_restriction_term_KTpower_left :
  forall s t1 t2,
    subset (uniform_substitution_restriction_term s t1)
           (uniform_substitution_restriction_term s (KTpower t1 t2)).
Proof.
  introv.
  apply subset_uniform_substitution_restriction_term_subterm; auto.
Qed.
Hint Resolve subset_uniform_substitution_restriction_term_KTpower_left : core.

Lemma subset_uniform_substitution_restriction_term_KTpower_right :
  forall s t1 t2,
    subset (uniform_substitution_restriction_term s t2)
           (uniform_substitution_restriction_term s (KTpower t1 t2)).
Proof.
  introv.
  apply subset_uniform_substitution_restriction_term_subterm; auto.
Qed.
Hint Resolve subset_uniform_substitution_restriction_term_KTpower_right : core.

Lemma U_admissible_term_KTpower_left :
  forall e t1 t2 s,
    U_admissible_term e (KTpower t1 t2) s = true
    -> U_admissible_term e t1 s = true.
Proof.
  unfold U_admissible_term; introv h.
  eapply eassignables_disj_subset;[|exact h]; clear h; eauto 3 with core.
  apply implies_eassignables_subset_free_vars_uniform_substitution.
  apply subset_uniform_substitution_restriction_term_KTpower_left.
Qed.
Hint Resolve U_admissible_term_KTpower_left : core.

Lemma U_admissible_term_KTpower_right :
  forall e t1 t2 s,
    U_admissible_term e (KTpower t1 t2) s = true
    -> U_admissible_term e t2 s = true.
Proof.
  unfold U_admissible_term; introv h.
  eapply eassignables_disj_subset;[|exact h]; clear h; eauto 3 with core.
  apply implies_eassignables_subset_free_vars_uniform_substitution.
  apply subset_uniform_substitution_restriction_term_KTpower_right.
Qed.
Hint Resolve U_admissible_term_KTpower_right : core.

Lemma subset_uniform_substitution_restriction_term_KTfuncOf_right :
  forall s f n (args : Vector.t Term n) t,
    Vector.In t args
    -> subset (uniform_substitution_restriction_term s t)
              (uniform_substitution_restriction_term s (KTfuncOf f n args)).
Proof.
  introv i.
  apply subset_uniform_substitution_restriction_term_subterm; auto.
Qed.
Hint Resolve subset_uniform_substitution_restriction_term_KTfuncOf_right : core.

Lemma U_admissible_term_KTfuncOf_left :
  forall e f n (args : Vector.t Term n) t s,
    Vector.In t args
    -> U_admissible_term e (KTfuncOf f n args) s = true
    -> U_admissible_term e t s = true.
Proof.
  unfold U_admissible_term; introv vin h.
  eapply eassignables_disj_subset;[|exact h]; clear h; eauto 3 with core.
  apply implies_eassignables_subset_free_vars_uniform_substitution.
  apply subset_uniform_substitution_restriction_term_KTfuncOf_right; auto.
Qed.
Hint Resolve U_admissible_term_KTfuncOf_left : core.
