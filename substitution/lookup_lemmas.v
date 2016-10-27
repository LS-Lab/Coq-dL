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



Lemma lookup_func_uniform_substitution_restriction_term_in :
  forall s (t :Term) f n,
    In (SymbolFunction f n) (term_signature t)
    -> lookup_func (uniform_substitution_restriction_term s t) f n
       = lookup_func s f n.
Proof.
  induction s; introv h; simpl in *; auto.
  rewrite uniform_substitution_entry_in_term_eq.
  destruct a; auto; try (complete (apply IHs; auto)).
  unfold in_signature.
  repeat (dest_cases w; GC);
    unfold lookup_func; simpl;
      repeat (dest_cases w; subst; GC);
      try (complete (pose proof (IHs t f0 n) as q;
                     unfold lookup_func in q; simpl in q;
                     rewrite <- Heqw0 in q;
                     try (rewrite <- Heqw in q; auto)));
      try (complete (pose proof (IHs t f n) as q;
                     unfold lookup_func in q; simpl in q;
                     rewrite <- Heqw0 in q;
                     try (rewrite <- Heqw in q; auto))).
Qed.

Lemma lookup_pred_uniform_substitution_restriction_term_in :
  forall s (t :Term) f n,
    In (SymbolPredicate f n) (term_signature t)
    -> lookup_pred (uniform_substitution_restriction_term s t) f n
       = lookup_pred s f n.
Proof.
  induction s; introv h; simpl in *; auto.
  unfold lookup_pred; simpl.
  repeat (dest_cases w; simpl); ginv;
    try (complete (pose proof (IHs t f n) as q;
                   unfold lookup_pred in q; simpl in q;
                   rewrite <- Heqw0 in q;
                   try (rewrite <- Heqw2 in q; auto);
                   try (rewrite <- Heqw1 in q; auto)));
    try (complete (destruct a; allsimpl; ginv; dest_cases w; subst;
                   dest_cases w; ginv; dest_cases w));
    try (complete (destruct a; allsimpl; unfold in_signature in *;
                   ginv; repeat (dest_cases w); ginv)).
Qed.

Lemma lookup_quant_uniform_substitution_restriction_term_in :
  forall s (t :Term) f,
    In (SymbolQuantifier f) (term_signature t)
    -> lookup_quant (uniform_substitution_restriction_term s t) f
       = lookup_quant s f.
Proof.
  induction s; introv h; simpl in *; auto.
  unfold lookup_quant; simpl.
  repeat (dest_cases w; simpl); ginv;
    try (complete (pose proof (IHs t f) as q;
                   unfold lookup_quant in q; simpl in q;
                   rewrite <- Heqw0 in q;
                   try (rewrite <- Heqw2 in q; auto);
                   try (rewrite <- Heqw1 in q; auto)));
    try (complete (destruct a; allsimpl; ginv; dest_cases w; ginv; dest_cases w));
    try (complete (destruct a; allsimpl; unfold in_signature in *;
                   ginv; repeat (dest_cases w); ginv)).
Qed.

Lemma lookup_const_uniform_substitution_restriction_term_in :
  forall s (t :Term) f,
    In (SymbolProgramConst f) (term_signature t)
    -> lookup_const (uniform_substitution_restriction_term s t) f
       = lookup_const s f.
Proof.
  induction s; introv h; simpl in *; auto.
  unfold lookup_const; simpl.
  repeat (dest_cases w; simpl); ginv;
    try (complete (pose proof (IHs t f) as q;
                   unfold lookup_const in q; simpl in q;
                   rewrite <- Heqw0 in q;
                   try (rewrite <- Heqw2 in q; auto);
                   try (rewrite <- Heqw1 in q; auto)));
    try (complete (destruct a; allsimpl; ginv; dest_cases w; ginv; dest_cases w));
    try (complete (destruct a; allsimpl; unfold in_signature in *;
                   ginv; repeat (dest_cases w); ginv)).
Qed.


Lemma lookup_func_uniform_substitution_restriction_formula_in :
  forall s t f n,
    In (SymbolFunction f n) (formula_signature t)
    -> lookup_func (uniform_substitution_restriction_formula s t) f n
       = lookup_func s f n.
Proof.
  induction s; introv h; simpl in *; auto.
  unfold lookup_func; simpl.
  repeat (dest_cases w; simpl); ginv;
    try (complete (pose proof (IHs t f n) as q;
                   unfold lookup_func in q; simpl in q;
                   rewrite <- Heqw0 in q;
                   try (rewrite <- Heqw2 in q; auto);
                   try (rewrite <- Heqw1 in q; auto)));
    try (complete (destruct a; allsimpl; ginv; dest_cases w; subst;
                   dest_cases w; ginv; dest_cases w));
    try (complete (destruct a; allsimpl; unfold in_signature in *;
                   ginv; repeat (dest_cases w); ginv)).
Qed.

Lemma lookup_pred_uniform_substitution_restriction_formula_in :
  forall s t f n,
    In (SymbolPredicate f n) (formula_signature t)
    -> lookup_pred (uniform_substitution_restriction_formula s t) f n
       = lookup_pred s f n.
Proof.
  induction s; introv h; simpl in *; auto.
  unfold lookup_pred; simpl.
  repeat (dest_cases w; simpl); ginv;
    try (complete (pose proof (IHs t f n) as q;
                   unfold lookup_pred in q; simpl in q;
                   rewrite <- Heqw0 in q;
                   try (rewrite <- Heqw2 in q; auto);
                   try (rewrite <- Heqw1 in q; auto)));
    try (complete (destruct a; allsimpl; ginv; dest_cases w; subst;
                   dest_cases w; ginv; dest_cases w));
    try (complete (destruct a; allsimpl; unfold in_signature in *;
                   ginv; repeat (dest_cases w); ginv)).
Qed.

Lemma lookup_quant_uniform_substitution_restriction_formula_in :
  forall s t f,
    In (SymbolQuantifier f) (formula_signature t)
    -> lookup_quant (uniform_substitution_restriction_formula s t) f
       = lookup_quant s f.
Proof.
  induction s; introv h; simpl in *; auto.
  unfold lookup_quant; simpl.
  repeat (dest_cases w; simpl); ginv;
    try (complete (pose proof (IHs t f) as q;
                   unfold lookup_quant in q; simpl in q;
                   rewrite <- Heqw0 in q;
                   try (rewrite <- Heqw2 in q; auto);
                   try (rewrite <- Heqw1 in q; auto)));
    try (complete (destruct a; allsimpl; ginv; dest_cases w; ginv; dest_cases w));
    try (complete (destruct a; allsimpl; unfold in_signature in *;
                   ginv; repeat (dest_cases w); ginv)).
Qed.

Lemma lookup_const_uniform_substitution_restriction_formula_in :
  forall s t f,
    In (SymbolProgramConst f) (formula_signature t)
    -> lookup_const (uniform_substitution_restriction_formula s t) f
       = lookup_const s f.
Proof.
  induction s; introv h; simpl in *; auto.
  unfold lookup_const; simpl.
  repeat (dest_cases w; simpl); ginv;
    try (complete (pose proof (IHs t f) as q;
                   unfold lookup_const in q; simpl in q;
                   rewrite <- Heqw0 in q;
                   try (rewrite <- Heqw2 in q; auto);
                   try (rewrite <- Heqw1 in q; auto)));
    try (complete (destruct a; allsimpl; ginv; dest_cases w; ginv; dest_cases w));
    try (complete (destruct a; allsimpl; unfold in_signature in *;
                   ginv; repeat (dest_cases w); ginv)).
Qed.


Lemma lookup_func_uniform_substitution_restriction_program_in :
  forall s t f n,
    In (SymbolFunction f n) (program_signature t)
    -> lookup_func (uniform_substitution_restriction_program s t) f n
       = lookup_func s f n.
Proof.
  induction s; introv h; simpl in *; auto.
  unfold lookup_func; simpl.
  repeat (dest_cases w; simpl); ginv;
    try (complete (pose proof (IHs t f n) as q;
                   unfold lookup_func in q; simpl in q;
                   rewrite <- Heqw0 in q;
                   try (rewrite <- Heqw2 in q; auto);
                   try (rewrite <- Heqw1 in q; auto)));
    try (complete (destruct a; allsimpl; ginv; dest_cases w; subst;
                   dest_cases w; ginv; dest_cases w));
    try (complete (destruct a; allsimpl; unfold in_signature in *;
                   ginv; repeat (dest_cases w); ginv)).
Qed.

Lemma lookup_pred_uniform_substitution_restriction_program_in :
  forall s t f n,
    In (SymbolPredicate f n) (program_signature t)
    -> lookup_pred (uniform_substitution_restriction_program s t) f n
       = lookup_pred s f n.
Proof.
  induction s; introv h; simpl in *; auto.
  unfold lookup_pred; simpl.
  repeat (dest_cases w; simpl); ginv;
    try (complete (pose proof (IHs t f n) as q;
                   unfold lookup_pred in q; simpl in q;
                   rewrite <- Heqw0 in q;
                   try (rewrite <- Heqw2 in q; auto);
                   try (rewrite <- Heqw1 in q; auto)));
    try (complete (destruct a; allsimpl; ginv; dest_cases w; subst;
                   dest_cases w; ginv; dest_cases w));
    try (complete (destruct a; allsimpl; unfold in_signature in *;
                   ginv; repeat (dest_cases w); ginv)).
Qed.

Lemma lookup_quant_uniform_substitution_restriction_program_in :
  forall s t f,
    In (SymbolQuantifier f) (program_signature t)
    -> lookup_quant (uniform_substitution_restriction_program s t) f
       = lookup_quant s f.
Proof.
  induction s; introv h; simpl in *; auto.
  unfold lookup_quant; simpl.
  repeat (dest_cases w; simpl); ginv;
    try (complete (pose proof (IHs t f) as q;
                   unfold lookup_quant in q; simpl in q;
                   rewrite <- Heqw0 in q;
                   try (rewrite <- Heqw2 in q; auto);
                   try (rewrite <- Heqw1 in q; auto)));
    try (complete (destruct a; allsimpl; ginv; dest_cases w; ginv; dest_cases w));
    try (complete (destruct a; allsimpl; unfold in_signature in *;
                   ginv; repeat (dest_cases w); ginv)).
Qed.

Lemma lookup_const_uniform_substitution_restriction_program_in :
  forall s t f,
    In (SymbolProgramConst f) (program_signature t)
    -> lookup_const (uniform_substitution_restriction_program s t) f
       = lookup_const s f.
Proof.
  induction s; introv h; simpl in *; auto.
  unfold lookup_const; simpl.
  repeat (dest_cases w; simpl); ginv;
    try (complete (pose proof (IHs t f) as q;
                   unfold lookup_const in q; simpl in q;
                   rewrite <- Heqw0 in q;
                   try (rewrite <- Heqw2 in q; auto);
                   try (rewrite <- Heqw1 in q; auto)));
    try (complete (destruct a; allsimpl; ginv; dest_cases w; ginv; dest_cases w));
    try (complete (destruct a; allsimpl; unfold in_signature in *;
                   ginv; repeat (dest_cases w); ginv)).
Qed.
