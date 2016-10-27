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
Require Export US.


Inductive subterm : Term -> Term -> Prop :=
| subterm_refl : forall t, subterm t t
| subterm_trans : forall a b c, subterm a b -> subterm b c -> subterm a c
| subterm_func :
    forall f n (args : Vector.t Term n) t,
      Vector.In t args
      -> subterm t (KTfuncOf f n args)
| subterm_neg : forall t, subterm t (KTneg t)
| subterm_plus_l   : forall a b, subterm a (KTplus   a b)
| subterm_plus_r   : forall a b, subterm b (KTplus   a b)
| subterm_minus_l  : forall a b, subterm a (KTminus  a b)
| subterm_minus_r  : forall a b, subterm b (KTminus  a b)
| subterm_times_l  : forall a b, subterm a (KTtimes  a b)
| subterm_times_r  : forall a b, subterm b (KTtimes  a b)
| subterm_divide_l : forall a b, subterm a (KTdivide a b)
| subterm_divide_r : forall a b, subterm b (KTdivide a b)
| subterm_power_l  : forall a b, subterm a (KTpower  a b)
| subterm_power_r  : forall a b, subterm b (KTpower  a b)
| subterm_diff : forall t, subterm t (KTdifferential t).
Hint Constructors subterm.


Lemma implies_subset_cons_r_weak :
  forall {T} (l1 l2 : list T) x,
    subset l1 l2 -> subset l1 (x :: l2).
Proof.
  introv ss i; simpl; apply ss in i; tcsp.
Qed.

Lemma implies_subset_vec_flatten :
  forall {T} (l : list T) {n} (v : Vector.t (list T) n),
    (exists x, Vector.In x v /\ subset l x)
    -> subset l (vec_flatten v).
Proof.
  introv e i; exrepnd.
  apply in_vec_flatten.
  eexists; dands; eauto.
Qed.

Lemma subterm_implies_term_signature_subset :
  forall a b,
    subterm a b
    -> subset (term_signature a) (term_signature b).
Proof.
  introv st.
  induction st; simpl; auto; try (complete (apply implies_subset_app_r; tcsp)).
  { eapply subset_trans; eauto. }
  { apply implies_subset_cons_r_weak.
    apply implies_subset_vec_flatten.
    exists (term_signature t); dands; auto.
    apply in_vec_map; eexists; dands; eauto. }
Qed.

Lemma uniform_substitution_entry_in_term_if_subterm :
  forall e a b,
    subterm a b
    -> uniform_substitution_entry_in_term e a = true
    -> uniform_substitution_entry_in_term e b = true.
Proof.
  introv st.
  repeat (rewrite uniform_substitution_entry_in_term_eq).
  destruct e; auto.
  intro i.
  unfold in_signature in *.
  repeat (dest_cases w; GC).
  apply subterm_implies_term_signature_subset in st.
  apply st in i0; tcsp.
Qed.

Lemma subset_uniform_substitution_restriction_term_subterm :
  forall s t1 t2,
    subterm t1 t2
    -> subset (uniform_substitution_restriction_term s t1)
              (uniform_substitution_restriction_term s t2).
Proof.
  induction s; introv st; simpl; auto.
  dest_cases w; dest_cases y; symmetry in Heqw, Heqy.
  { apply subset_cons_l; simpl; dands; tcsp.
    apply implies_subset_cons_r_weak; auto. }
  { eapply uniform_substitution_entry_in_term_if_subterm in st;[|eauto].
    rewrite st in Heqy; ginv. }
  { apply implies_subset_cons_r_weak; auto. }
Qed.

Lemma implies_eassignables_subset_free_vars_uniform_substitution :
  forall s1 s2,
    subset s1 s2
    -> eassignables_subset
         (free_vars_uniform_substitution s1)
         (free_vars_uniform_substitution s2) = true.
Proof.
  introv h.
  apply eassignables_subset_iff; introv i.
  unfold free_vars_uniform_substitution in *.
  induction s1; simpl in *; ginv.
  apply subset_cons_l in h; repnd.
  autodimp IHs1 hyp.
  apply in_eassignables_app_true_iff in i; repndors; tcsp.
  clear dependent s1.

  induction s2; simpl in *; tcsp.
  apply in_eassignables_app_true_iff.
  repndors; subst; tcsp.
Qed.
Hint Resolve implies_eassignables_subset_free_vars_uniform_substitution : core.

Lemma eassignables_subset_subterm :
  forall s a b,
    subterm a b
    -> eassignables_subset
         (free_vars_sub_restrict_term s a)
         (free_vars_sub_restrict_term s b)
       = true.
Proof.
  introv st.
  unfold free_vars_sub_restrict_term.
  apply implies_eassignables_subset_free_vars_uniform_substitution.
  induction s; simpl; auto.
  dest_cases w; dest_cases y; symmetry in Heqw, Heqy.
  { apply subset_cons_l; simpl; dands; tcsp. }
  { eapply uniform_substitution_entry_in_term_if_subterm in st;[|eauto].
    rewrite st in Heqy; ginv. }
Qed.
