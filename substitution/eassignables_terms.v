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

(*Hint Resolve subset_refl : core.*)

Lemma fold_free_vars_sub_restrict_term :
  forall s t,
    free_vars_uniform_substitution (uniform_substitution_restriction_term s t)
    = free_vars_sub_restrict_term s t.
Proof.
  auto.
Qed.

Lemma eassignables_subset_app_left_right :
  forall a b v w,
    eassignables_subset a v = true
    -> eassignables_subset b w = true
    -> eassignables_subset (EAssignables_app a b) (EAssignables_app v w) = true.
Proof.
  introv ss1 ss2.
  destruct a, b, v, w; simpl in *;
    allrw @included_dec_prop;
    allrw @disj_dec_prop;
    allrw KAssignables_included_prop;
    allrw KAssignables_disj_prop; tcsp;
      try (complete (introv i; allrw in_KAssignables_minus; repnd; dands; auto)).

  { introv i; allrw in_app_iff; repndors; tcsp. }

  { introv i j; apply in_KAssignables_minus in j; repnd.
    allrw in_app_iff; repndors; tcsp.
    apply ss2 in i; sp. }

  { introv i j.
    allrw in_KAssignables_minus; repnd.
    allrw in_app_iff; repndors; tcsp.
    apply ss1 in i; tcsp. }

  { introv i j.
    allrw in_KAssignables_inter; repnd.
    allrw in_app_iff; repndors; try (apply ss1 in i; tcsp).
    apply ss2 in i; tcsp. }

  { introv i;
      allrw in_KAssignables_minus;
      allrw in_KAssignables_inter;
      repnd; dands; auto.
    intro j; apply ss1 in j; tcsp. }

  { introv i;
      allrw in_KAssignables_minus;
      allrw in_KAssignables_inter;
      repnd; dands; auto.
    intro j; apply ss2 in j; tcsp. }

  { introv i;
      allrw in_KAssignables_inter;
      repnd; dands; auto. }
Qed.

Lemma eassignables_subset_funcof :
  forall s f n (args : Vector.t Term n) t,
    Vector.In t args
    -> eassignables_subset
         (free_vars_sub_restrict_term s t)
         (free_vars_sub_restrict_term s (KTfuncOf f n args))
       = true.
Proof.
  introv i.
  apply eassignables_subset_subterm; auto.
Qed.

Lemma eassignables_subset_neg :
  forall s t,
    eassignables_subset
      (free_vars_sub_restrict_term s t)
      (free_vars_sub_restrict_term s (KTneg t))
    = true.
Proof.
  introv.
  apply eassignables_subset_subterm; auto.
Qed.

Lemma eassignables_subset_diff :
  forall s t,
    eassignables_subset
      (free_vars_sub_restrict_term s t)
      (free_vars_sub_restrict_term s (KTdifferential t))
    = true.
Proof.
  introv.
  apply eassignables_subset_subterm; auto.
Qed.

Lemma EA_assignables_as_EAssignables_app :
  forall l1 l2,
    EA_assignables (l1 ++ l2)
    = EAssignables_app (EA_assignables l1) (EA_assignables l2).
Proof.
  sp.
Qed.

Lemma eassignables_subset_plus1 :
  forall s t1 t2,
    eassignables_subset
      (free_vars_sub_restrict_term s t1)
      (free_vars_sub_restrict_term s (KTplus t1 t2))
    = true.
Proof.
  introv.
  apply eassignables_subset_subterm; auto.
Qed.

Lemma eassignables_subset_plus2 :
  forall s t1 t2,
    eassignables_subset
      (free_vars_sub_restrict_term s t2)
      (free_vars_sub_restrict_term s (KTplus t1 t2))
    = true.
Proof.
  introv.
  apply eassignables_subset_subterm; auto.
Qed.

Lemma eassignables_subset_minus1 :
  forall s t1 t2,
    eassignables_subset
      (free_vars_sub_restrict_term s t1)
      (free_vars_sub_restrict_term s (KTminus t1 t2))
    = true.
Proof.
  introv.
  apply eassignables_subset_subterm; auto.
Qed.

Lemma eassignables_subset_minus2 :
  forall s t1 t2,
    eassignables_subset
      (free_vars_sub_restrict_term s t2)
      (free_vars_sub_restrict_term s (KTminus t1 t2))
    = true.
Proof.
  introv.
  apply eassignables_subset_subterm; auto.
Qed.

Lemma eassignables_subset_times1 :
  forall s t1 t2,
    eassignables_subset
      (free_vars_sub_restrict_term s t1)
      (free_vars_sub_restrict_term s (KTtimes t1 t2))
    = true.
Proof.
  introv.
  apply eassignables_subset_subterm; auto.
Qed.

Lemma eassignables_subset_times2 :
  forall s t1 t2,
    eassignables_subset
      (free_vars_sub_restrict_term s t2)
      (free_vars_sub_restrict_term s (KTtimes t1 t2))
    = true.
Proof.
  introv.
  apply eassignables_subset_subterm; auto.
Qed.
