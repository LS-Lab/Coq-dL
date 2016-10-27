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
Require Export FunctionalExtensionality.


(**

  This files provides definitions and lemmas regarding the
  extensionality of interpretations.

*)


(** extensionally definition of interpretation of a Symbol *)
Definition ext_interpretations_at (I J : interpretation) (s : Symbol) : Prop :=
  match s with
  | SymbolFunction f n   =>
    forall r : Vector.t R n,
      interp_fun_f n (I (SymbolFunction f n)) r = interp_fun_f n (J (SymbolFunction f n)) r

  | SymbolDotTerm n      =>
    I (SymbolDotTerm n) = J (SymbolDotTerm n)

  | SymbolPredicate p n  =>
    forall r, I (SymbolPredicate p n) r <-> J (SymbolPredicate p n) r

  | SymbolQuantifier C   =>
    forall v w f g,
      (forall s, f s <-> g s)
      -> (forall a, v a = w a)
      -> interp_quant_f (I (SymbolQuantifier C)) f v
         <-> interp_quant_f (J (SymbolQuantifier C)) g w

  | SymbolDotForm        =>
    forall v w,
      (forall a, v a = w a)
      -> I SymbolDotForm v <-> J SymbolDotForm w

  | SymbolODE c =>
    eqset (interp_ode_bv (I (SymbolODE c))) (interp_ode_bv (J (SymbolODE c)))
    /\
    forall v w a,
      (forall a, v a = w a)
      -> interp_ode_dm (I (SymbolODE c)) v a
         = interp_ode_dm (J (SymbolODE c)) w a

  | SymbolProgramConst a =>
    forall v1 v2 w1 w2,
      (forall a, v1 a = v2 a)
      -> (forall a, w1 a = w2 a)
      -> I (SymbolProgramConst a) v1 w1 <-> J (SymbolProgramConst a) v2 w2
  end.

(** extensionally definition of interpretation *)
Definition ext_interpretations (I J : interpretation) : Prop :=
  forall s : Symbol, ext_interpretations_at I J s.

(** interpretations i1 and i2 are extensionally equal for variables in vars *)
Definition equal_interpretations_on_ext
           (i1 i2 : interpretation)
           (vs : list Symbol) :=
  forall x,
    List.In x vs
    -> ext_interpretations_at i1 i2 x.

(** interpretations i1 and i2 are  equal for all symbols in list vs *)
Definition equal_interpretations_on
           (i1 i2 : interpretation)
           (vs : list Symbol) :=
  forall x,
    List.In x vs
    -> i1 x = i2 x.

Lemma ext_interpretations_implies_equal_interpretations_on_ext :
  forall I J l,
    ext_interpretations I J
    -> equal_interpretations_on_ext I J l.
Proof.
  introv h i; tcsp.
Qed.
Hint Resolve ext_interpretations_implies_equal_interpretations_on_ext : core.

(** iff interpretations i2 and i2 are  equal on list of symbols,
they are equal for the symbol at the head of that list,
as well as for all symbols which are in the tale of that list *)
Lemma equal_interpretations_on_cons :
  forall i1 i2 v vs,
    equal_interpretations_on i1 i2 (v :: vs)
    <-> (i1 v = i2 v /\ equal_interpretations_on i1 i2 vs).
Proof.
  introv; split; intro h; repnd; dands; auto.
  { apply (h v); simpl; tcsp. }
  { introv i; apply (h x); simpl; tcsp. }
  { introv i; simpl in i; repndors; subst; auto. }
Qed.

(** iff interpretations i2 and i2 are extensionally equal on list of symbols,
they are extensionally equal for the symbol  at the head of that list,
as well as for all symbols which are in the tale of that list *)
Lemma equal_interpretations_on_ext_cons :
  forall i1 i2 v vs,
    equal_interpretations_on_ext i1 i2 (v :: vs)
    <-> (ext_interpretations_at i1 i2 v /\ equal_interpretations_on_ext i1 i2 vs).
Proof.
  introv; split; intro h; repnd; dands; auto.
  { apply (h v); simpl; tcsp. }
  { introv i; apply (h x); simpl; tcsp. }
  { introv i; simpl in i; repndors; subst; auto. }
Qed.

(** iff interpretations i2 and i2 are equal on append of two lists of symbols,
they are equal on all all symbols of both lists *)
Lemma equal_interpretations_on_app :
  forall i1 i2 vs1 vs2,
    equal_interpretations_on i1 i2 (vs1 ++ vs2)
    <-> (equal_interpretations_on i1 i2 vs1 /\ equal_interpretations_on i1 i2 vs2).
Proof.
  introv; split; intro h; repnd; dands; auto.
  { introv i.
    apply (h x).
    rewrite in_app_iff; auto. }
  { introv i.
    apply (h x).
    apply in_app_iff; auto. }
  { introv i.
    apply in_app_iff in i; repndors.
    - apply (h0 x); auto.
    - apply (h x); auto.
  }
Qed.

(** iff interpretations i2 and i2 are extensionally equal on append of two lists of symbols,
they are extensionally equal on all all symbols of both lists *)
Lemma equal_interpretations_on_ext_app :
  forall i1 i2 vs1 vs2,
    equal_interpretations_on_ext i1 i2 (vs1 ++ vs2)
    <-> (equal_interpretations_on_ext i1 i2 vs1 /\ equal_interpretations_on_ext i1 i2 vs2).
Proof.
  introv; split; intro h; repnd; dands; auto.
  { introv i.
    apply (h x).
    rewrite in_app_iff; auto. }
  { introv i.
    apply (h x).
    apply in_app_iff; auto. }
  { introv i.
    apply in_app_iff in i; repndors.
    - apply (h0 x); auto.
    - apply (h x); auto.
  }
Qed.

(** symmetry for equality of interpretations *)
Lemma equal_interpretations_on_sym :
  forall I J e,
    equal_interpretations_on I J e
    -> equal_interpretations_on J I e.
Proof.
  introv eqs i; symmetry; apply eqs; auto.
Qed.

(** symmetry for extensionall equality of interpretations *)
Lemma ext_interpretations_at_sym :
  forall I J x,
    ext_interpretations_at I J x
    -> ext_interpretations_at J I x.
Proof.
  introv h.
  destruct x; simpl in *; introv; tcsp;
    try (complete (rewrite h; tcsp)).

  { introv q z.
    symmetry.
    apply h; tcsp.
    introv; rewrite q; tcsp. }

  { introv q.
    symmetry; tcsp. }

  { dands.

    { introv; symmetry; apply h. }

    { introv q; symmetry; apply h; auto. }
  }

  { introv q z.
    symmetry; tcsp. }
Qed.

Lemma ext_interpretations_sym :
  forall I J, ext_interpretations I J -> ext_interpretations J I.
Proof.
  introv h.
  introv.
  apply ext_interpretations_at_sym; apply h.
Qed.

(** reflexivity of equality of interpretations *)
Lemma ext_interpretations_at_refl :
  forall I x,
    ext_interpretations_at I I x.
Proof.
  introv.
  destruct x; simpl in *; introv; tcsp;
    try (complete (rewrite h; tcsp)).

  { introv q z.
    remember (I (SymbolQuantifier f)) as iF.
    simpl in *.
    destruct iF as [F cond]; simpl.
    apply cond; tcsp. }

  { introv q; tcsp.
    (* make interpretations more extensional to get rid of functional_extensionality *)
    assert (v = w) as xx by (apply functional_extensionality; auto).
    subst; tcsp. }

  { dands; auto.
    introv q.
    remember (I (SymbolODE c)) as ic; simpl in ic.
    destruct ic as [bv sem cond]; simpl.
    unfold interpOdeExt in cond.
    apply cond; auto. }

  { introv q z.
    (* make interpretations more extensional to get rid of functional_extensionality *)
    assert (v1 = v2) as xx1 by (apply functional_extensionality; auto).
    assert (w1 = w2) as xx2 by (apply functional_extensionality; auto).
    rewrite xx1, xx2; tcsp. }
Qed.

Lemma ext_interpretations_refl :
  forall I, ext_interpretations I I.
Proof.
  repeat introv.
  apply ext_interpretations_at_refl.
Qed.

(** symmetry for extensionall equality of interpretations *)
Lemma equal_interpretations_on_ext_sym :
  forall I J e,
    equal_interpretations_on_ext I J e
    -> equal_interpretations_on_ext J I e.
Proof.
  introv eqs i; introv; apply ext_interpretations_at_sym; auto.
Qed.

(** reflexivity of extensionall equality of interpretations *)
Lemma equal_interpretations_on_ext_refl :
  forall I e,
    equal_interpretations_on_ext I I e.
Proof.
  introv i.
  apply ext_interpretations_at_refl.
Qed.
Hint Resolve equal_interpretations_on_ext_refl : core.

Lemma equal_interpretations_on_ext_vec_flatten_map :
  forall I J {n} (args : Vector.t Term n) a,
    equal_interpretations_on_ext I J (vec_flatten (Vector.map term_signature args))
    -> Vector.In a args
    -> equal_interpretations_on_ext I J (term_signature a).
Proof.
  introv equ i j.
  apply equ.
  apply in_vec_flatten.
  exists (term_signature a); dands; auto.
  apply in_vec_map.
  exists a; dands; auto.
Qed.
Hint Resolve equal_interpretations_on_ext_vec_flatten_map : core.

Lemma eqset_ode_footprint_if_equal_interpretations_on_ext :
  forall I J ode,
    equal_interpretations_on_ext I J (ode_signature ode)
    -> eqset (ode_footprint J ode) (ode_footprint I ode).
Proof.
  induction ode; introv eqi; simpl in *; tcsp.

  { destruct child; simpl in *.

    { unfold ode_footprint, ode_footprint_vars, ode_footprint_diff; simpl.
      introv; split; introv h; allrw in_app_iff; allrw in_map_iff;
        repndors; exrepnd; subst.

      { pose proof (eqi (SymbolODE name)) as z; simpl in z.
        autodimp z hyp; repnd.
        apply z0 in h.
        left; auto. }

      { pose proof (eqi (SymbolODE name)) as z; simpl in z.
        autodimp z hyp.
        apply z in h0.
        right.
        exists x0; dands; auto. }

      { pose proof (eqi (SymbolODE name)) as z; simpl in z.
        autodimp z hyp; repnd.
        apply z0 in h.
        left; auto. }

      { pose proof (eqi (SymbolODE name)) as z; simpl in z.
        autodimp z hyp.
        apply z in h0.
        right.
        exists x0; dands; auto. }
    }

    { unfold ode_footprint, ode_footprint_diff; simpl.
      apply eqset_refl. }
  }

  { apply equal_interpretations_on_ext_app in eqi; repnd.
    autodimp IHode1 hyp.
    autodimp IHode2 hyp.
    introv; split; intro h; apply eqset_ode_footprint_prod in h;
      apply eqset_ode_footprint_prod; allrw in_app_iff; repndors.

    { apply IHode1 in h; auto. }
    { apply IHode2 in h; auto. }
    { apply IHode1 in h; auto. }
    { apply IHode2 in h; auto. }
  }
Qed.

Lemma eqset_ode_footprint_diff_if_equal_interpretations_on_ext :
  forall I J ode,
    equal_interpretations_on_ext I J (ode_signature ode)
    -> eqset (ode_footprint_diff J ode) (ode_footprint_diff I ode).
Proof.
  induction ode; introv eqi; simpl in *; tcsp.

  { destruct child; simpl in *.

    { unfold ode_footprint_diff; simpl.
      introv; split; introv h; allrw in_app_iff; allrw in_map_iff;
        repndors; exrepnd; subst.

      { pose proof (eqi (SymbolODE name)) as z; simpl in z.
        autodimp z hyp.
        apply z in h0.
        exists x0; dands; auto. }

      { pose proof (eqi (SymbolODE name)) as z; simpl in z.
        autodimp z hyp.
        apply z in h0.
        exists x0; dands; auto. }
    }

    { unfold ode_footprint_diff; simpl.
      apply eqset_refl. }
  }

  { apply equal_interpretations_on_ext_app in eqi; repnd.
    autodimp IHode1 hyp.
    autodimp IHode2 hyp.
    introv; split; intro h; apply eqset_ode_footprint_diff_prod in h;
      apply eqset_ode_footprint_diff_prod; allrw in_app_iff; repndors.

    { apply IHode1 in h; auto. }
    { apply IHode2 in h; auto. }
    { apply IHode1 in h; auto. }
    { apply IHode2 in h; auto. }
  }
Qed.

Lemma equal_interpretations_on_ext_ode_signature_implies_eqset_ode_vars :
  forall I J ode,
    equal_interpretations_on_ext I J (ode_signature ode)
    -> eqset (ode_assign I ode) (ode_assign J ode).
Proof.
  induction ode; introv eqi; simpl in *; tcsp.

  { destruct child; simpl in *; auto.
    pose proof (eqi (SymbolODE name)) as q; clear eqi; simpl in q.
    autodimp q hyp.
    repnd; auto. }

  { apply equal_interpretations_on_ext_app in eqi; repnd.
    autodimp IHode1 hyp.
    autodimp IHode2 hyp.
    apply implies_eqset_app_lr; auto. }
Qed.
