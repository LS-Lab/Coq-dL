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

Require Export terms_util2.

Lemma vec_eq_dec_in :
  forall (A : Type) (n : nat) (l l' : Vector.t A n),
    (forall x y : A, Vector.In x l -> {x = y} + {x <> y})
    -> {l = l'} + {l <> l'}.
Proof.
  induction n; introv ih.

  { apply Vector.case0 with (v := l).
    apply Vector.case0 with (v := l').
    prove_dec. }

  { revert dependent l; intro l.
    apply (Vector.caseS' l); clear l.
    apply (Vector.caseS' l'); clear l'.
    introv ih.
    pose proof (IHn t0 t) as q; autodimp q hyp.
    { introv i; apply ih; constructor; auto. }
    pose proof (ih h0 h) as z; autodimp z hyp; tcsp.
    destruct q as [q|q]; subst; destruct z as [z|z]; subst; prove_dec.
    right; intro z.
    apply Vector.cons_inj in z; repnd; tcsp. }
Defined.

(**

  In this file decidability of terms, formulas and programs is implemented.
  Decidability for symbols can be found in symbol_util.v.

*)


Lemma KTnum_dec : forall (t u : KTnum), {t = u} + {t <> u}.
Proof.
  destruct t as [n1|r1], u as [n2|r2]; prove_dec.
  { destruct (deq_nat n1 n2); subst; prove_dec. }
  { destruct (Req_EM_T r1 r2); subst; prove_dec. }
Defined.


(** decidability on Terms *)
Lemma term_dec : forall (t u : Term), {t = u} + {t <> u}.
Proof.
  term_rec t Case; destruct u; prove_dec;
    try (complete (destruct (IHt1 u1) as [d1|d1];
                   destruct (IHt2 u2) as [d2|d2];
                   subst; prove_dec));
    try (complete (destruct (IHt u) as [d3|d3]; subst; prove_dec)).

  { Case "KTdot".
    destruct (deq_nat n n0); prove_dec. }

  { Case "KTfuncOf".
    destruct (FunctionSymbol_dec f f0); subst; prove_dec.
    destruct (deq_nat n n0); subst; prove_dec.

    pose proof (vec_eq_dec_in _ _ args a) as h.
    autodimp h hyp.
    destruct h as [h|h]; subst; tcsp.
    right; intro xx.
    inversion xx; eqDepDec; subst; tcsp. }

  { Case "KTnumber".
    destruct (KTnum_dec r r0); subst; prove_dec. }

  { Case "KTread".
    destruct (KAssignable_dec var var0); subst; prove_dec. }
Defined.

(** decidability on Differential Programs *)
Lemma AtomicODE_dec :
  forall (t u : AtomicODE), {t = u} + {t <> u}.
Proof.
  destruct t, u; prove_dec.

  {
    destruct (ODEConst_dec name name0); subst; prove_dec.
  }

  {
    destruct (KAssignable_dec xp xp0); subst; prove_dec.
    destruct (term_dec e e0); subst; prove_dec.
  }
Defined.

Lemma ODE_dec :
  forall (t u : ODE), {t = u} + {t <> u}.
Proof.
  induction t; destruct u; prove_dec.

  { destruct (AtomicODE_dec child child0); subst; prove_dec. }

  {
    destruct (IHt1 u1); subst; prove_dec.
    destruct (IHt2 u2); subst; prove_dec.
  }
Defined.


(** decidability on Formulas and Programs *)
Lemma formula_program_dec :
  (forall (t u : Formula), {t = u} + {t <> u})
  * (forall (t u : Program), {t = u} + {t <> u}).
Proof.
  apply (Formula_Program_rec_2
           (fun t => forall (u : Formula), {t = u} + {t <> u})
           (fun t => forall (u : Program), {t = u} + {t <> u}));
    introv;
    try (intro imp1; introv);
    try (intro imp2; introv);
    destruct u;
    prove_dec;
    try (complete (destruct (IHt1 u1) as [d1|d1];
                   destruct (IHt2 u2) as [d2|d2];
                   subst; prove_dec));
    try (complete (destruct (IHt u) as [d3|d3]; subst; prove_dec));
    try (complete (destruct (term_dec left left0); subst; prove_dec;
                   destruct (term_dec right right0); subst; prove_dec));
    try (complete (destruct (imp1 u1); subst; prove_dec;
                   destruct (imp2 u2); subst; prove_dec));
    try (complete (destruct (imp1 u); subst; prove_dec)).

    {
      destruct (PredicateSymbol_dec f f0); subst; prove_dec.
      destruct (deq_nat n n0); subst; prove_dec.

      pose proof (vec_eq_dec_in _ _ args a) as h.
      autodimp h hyp;[introv i;apply term_dec|].
      destruct h as [h|h]; subst; tcsp.
      right; introv xx; inversion xx; eqDepDec; subst; tcsp.
    }

    {
      destruct (QuantifierSymbol_dec f f0); subst; prove_dec.
      destruct (imp1 u) as [d3|d3]; subst; prove_dec.
    }

    {
      destruct (list_eq_dec KVariable_dec vars vars0) as [d|d]; subst; prove_dec.
      destruct (imp1 u) as [d3|d3]; subst; prove_dec.
    }

    {
      destruct (list_eq_dec KVariable_dec vars vars0) as [d|d]; subst; prove_dec.
      destruct (imp1 u) as [d3|d3]; subst; prove_dec.
    }

    {
      destruct (imp1 prog0) as [d1|d1]; subst; prove_dec.
      destruct (imp2 u) as [d2|d2]; subst; prove_dec.
    }

    {
      destruct (imp1 prog0) as [d1|d1]; subst; prove_dec.
      destruct (imp2 u) as [d2|d2]; subst; prove_dec.
    }

    {
      destruct (ProgramConstName_dec name name0); subst; prove_dec.
    }

    {
      destruct (term_dec e e0); subst; prove_dec.
      destruct (KAssignable_dec x x0); subst; prove_dec.
    }

    {
      destruct (KAssignable_dec x x0); subst; prove_dec.
    }

    {
      destruct (imp1 cond0); subst; prove_dec.
    }

    {
      destruct (imp1 constraint0); subst; prove_dec.
      destruct (ODE_dec ode ode0); subst; prove_dec.
    }
Defined.


(** decidability on Formulas *)
Lemma formula_dec : forall (t u : Formula), {t = u} + {t <> u}.
Proof.
  pose proof formula_program_dec; sp.
Defined.


(** decidability on Programs *)
Lemma program_dec : forall (t u : Program), {t = u} + {t <> u}.
Proof.
  pose proof formula_program_dec; sp.
Defined.
