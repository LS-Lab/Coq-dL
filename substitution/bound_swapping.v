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

Require Export swapping.


(**

   This file implements bound renaming of variables using swapping.

 *)


Lemma swap_left_eq_right :
  forall x y, swap (MkSwapping x y) x = y.
Proof.
  introv.
  unfold swap; repeat dest_cases w.
Qed.
Hint Rewrite swap_left_eq_right : core.

Lemma swap_idem :
  forall x v, swap (MkSwapping x x) v = v.
Proof.
  introv; unfold swap; simpl; dest_cases w.
Qed.
Hint Rewrite swap_idem : core.

Lemma swap_assgn_idem :
  forall x a, swap_assgn (MkSwapping x x) a = a.
Proof.
  induction a; simpl; autorewrite with core; auto.
  rewrite IHa; auto.
Qed.
Hint Rewrite swap_assgn_idem : core.

Lemma swap_assgns_idem :
  forall x l, swap_assgns (MkSwapping x x) l = l.
Proof.
  induction l; simpl; autorewrite with core; auto.
  rewrite IHl; auto.
Qed.
Hint Rewrite swap_assgns_idem : core.

Lemma swap_state_idem :
  forall x v, swap_state (MkSwapping x x) v = v.
Proof.
  introv; apply functional_extensionality; introv.
  unfold swap_state; simpl; autorewrite with core; auto.
Qed.

Lemma ext_interpretations_at_swap_interp_idem :
  forall x I s, ext_interpretations_at (swap_interp (MkSwapping x x) I) I s.
Proof.
  repeat introv.
  destruct s; simpl; tcsp.

  { introv h q.
    remember (I (SymbolQuantifier f)) as F.
    destruct F as [F cond]; clear HeqF; simpl in *.
    apply cond; clear cond; introv; rewrite swap_state_idem; auto. }

  { introv h.
    rewrite swap_state_idem.
    assert (v = w) as xx by (apply functional_extensionality; auto).
    subst; tcsp. }

  { autorewrite with core; dands; auto.
    introv h.
    rewrite swap_state_idem.
    remember (I (SymbolODE c)) as C.
    destruct C as [bv sem ext]; simpl in *; clear HeqC.
    apply ext; clear ext.
    introv.
    rewrite swap_state_idem; auto. }

  { introv h1 h2.
    repeat (rewrite swap_state_idem).
    assert (v1 = v2) as xx1 by (apply functional_extensionality; auto).
    assert (w1 = w2) as xx2 by (apply functional_extensionality; auto).
    subst; tcsp. }
Qed.
Hint Resolve ext_interpretations_at_swap_interp_idem : core.

Lemma ext_interpretations_swap_interp_idem :
  forall x I, ext_interpretations (swap_interp (MkSwapping x x) I) I.
Proof.
  repeat introv; eauto with core.
Qed.
Hint Resolve ext_interpretations_swap_interp_idem : core.

Lemma equal_interpretations_on_ext_swap_interp_idem :
  forall x I l, equal_interpretations_on_ext (swap_interp (MkSwapping x x) I) I l.
Proof.
  introv i; eauto 3 with core.
Qed.
Hint Resolve equal_interpretations_on_ext_swap_interp_idem : core.

Lemma swap_assgn_not_in :
  forall a x y,
    KAssignable2variable a <> x
    -> KAssignable2variable a <> y
    -> swap_assgn (MkSwapping x y) a = a.
Proof.
  induction a; introv d1 d2; simpl in *.
  { unfold swap; simpl; repeat (dest_cases w). }
  { rewrite IHa; auto. }
Qed.

Definition upd_state_v (s : state) (v : Var) (r : R) (x : KAssignable) :=
  if KVariable_dec (KAssignable2variable x) v
  then r else s x.

Lemma swap_term_dynamic_semantics_term_same_I :
  forall t I v sw,
    dynamic_semantics_term I v (swap_term sw t)
    = dynamic_semantics_term I (swap_state sw v) t.
Proof.
  term_ind t Case; introv; simpl; auto;
    try (complete (rewrite IHt; auto));
    try (complete (rewrite IHt1, IHt2; auto)).

  { Case "KTfuncOf".
    f_equal.
    rewrite vec_map_map; unfold compose; simpl.
    apply eq_vec_map; introv i; tcsp.
  }

  { Case "KTdifferential".
    unfold term_assignables_nodup.
    rewrite term_assignables_swap_term_eq.
    apply big_sum_map_ext; auto; try (apply eq_swap_assgn_implies_eq);[].

    introv i.
    rewrite swap_state_as_apply_diff_swap.
    rewrite swap_state_as_apply_swap_assgn.
    f_equal.
    apply Derive_ext; introv.

    rewrite IHt.
    rewrite swap_state_upd_state_swap_assgn; auto.
  }
Qed.

(* disallow constant ODEs *)
Definition no_const_ode_atomic_ode (o : AtomicODE) : bool :=
  match o with
  | ODEconst c   => false
  | ODEsing xp t => true
  end.

Fixpoint no_const_ode_ode (o : ODE) : bool :=
  match o with
  | ODEatomic c => no_const_ode_atomic_ode c
  | ODEprod l r => no_const_ode_ode l && no_const_ode_ode r
  end.

(* disallow quantifiers and therefore dot formulas too  *)
Fixpoint no_const_ode_formula (F : Formula) : bool :=
  match F with
  | KFdot                   => false
  | KFtrue                  => true
  | KFfalse                 => true

  | KFequal        l r      => true
  | KFnotequal     l r      => true
  | KFgreaterEqual l r      => true
  | KFgreater      l r      => true
  | KFlessEqual    l r      => true
  | KFless         l r      => true

  | KFpredOf p n args       => true

  | KFquantifier q t        => false

  | KFnot   f               => no_const_ode_formula f
  | KFand   l r             => no_const_ode_formula l && no_const_ode_formula r
  | KFor    l r             => no_const_ode_formula l && no_const_ode_formula r
  | KFimply l r             => no_const_ode_formula l && no_const_ode_formula r
  | KFequiv l r             => no_const_ode_formula l && no_const_ode_formula r

  | KFforallVars lv f       => no_const_ode_formula f
  | KFexistsVars lv f       => no_const_ode_formula f

  | KFbox     p f           => no_const_ode_program p && no_const_ode_formula f
  | KFdiamond p f           => no_const_ode_program p && no_const_ode_formula f

  | KFdifferentialFormula f => no_const_ode_formula f
  end

(* disallow program constants *)
  with no_const_ode_program (P : Program) : bool :=
         match P with
         | KPconstant c           => false
         | KPassign x t           => true
         | KPassignAny x          => true
         | KPtest f               => no_const_ode_formula f

         | KPchoice l r           => no_const_ode_program l && no_const_ode_program r

         | KPcompose l r          => no_const_ode_program l && no_const_ode_program r
         | KPparallel cl cr l r   => no_const_ode_program l && no_const_ode_program r

         | KPloop p               => no_const_ode_program p

         | KPsend c t            => true
         | KPreceive c lv        => true
         | KPbroadcast c t lv    => true

         | KPodeSystem ode f     => no_const_ode_ode ode && no_const_ode_formula f
         end.

Lemma dynamic_semantics_ode_fun_swap_ode_no_const :
  forall ode I sw s a,
    no_const_ode_ode ode = true
    -> dynamic_semantics_ode_fun I (swap_ode sw ode) s a
       = dynamic_semantics_ode_fun
           I ode
           (swap_state sw s) (swap_assgn sw a).
Proof.
  induction ode; introv noc; simpl in *.

  { destruct child; simpl; auto; ginv.

    repeat (dest_cases w; subst; simpl in *; GC); autorewrite with core in *; ginv.
    { apply swap_term_dynamic_semantics_term_same_I. }
    { unfold KD in n; tcsp. }
    { destruct a; simpl in *; ginv.
      fold KD in *; ginv.
      rewrite swap_assgn_twice in n; tcsp. }
  }

  { apply andb_true_iff in noc; repnd.
    rewrite IHode1, IHode2; auto. }
Qed.

Lemma ode_assign_as_map_if_no_const :
  forall sw I ode,
    no_const_ode_ode ode = true
    -> ode_assign I ode
       = map (swap_assgn sw) (ode_assign I (swap_ode sw ode)).
Proof.
  induction ode; simpl; introv noc.

  { destruct child; simpl in *; auto; ginv.
    autorewrite with core; auto. }

  { apply andb_true_iff in noc; repnd.
    allrw map_app.
    rewrite IHode1, IHode2; auto. }
Qed.

Lemma dynamic_semantics_ode_swap_ode_no_const :
  forall ode I sw r phi,
    no_const_ode_ode ode = true
    -> dynamic_semantics_ode I (swap_ode sw ode) r phi
       <-> dynamic_semantics_ode
             I ode r
             (fun x : R => swap_state sw (phi x)).
Proof.
  introv noc; split; introv h i; simpl in *; autorewrite with core.

  { rewrite (ode_assign_as_map_if_no_const sw) in i; auto.
    rewrite in_map_iff in i; exrepnd; subst.
    apply (h zeta) in i0; repnd.
    dands; auto.

    { eapply ex_derive_ext;[|exact i1]; introv; simpl; auto.
      unfold swap_state; simpl.
      rewrite swap_assgn_twice; auto. }

    { unfold swap_state; simpl.
      rewrite swap_assgn_twice.
      fold KD in *.
      rewrite i2; auto. }

    { unfold swap_state; simpl in *.
      rewrite swap_assgn_twice.
      fold KD in *.
      rewrite i0; auto.
      apply dynamic_semantics_ode_fun_swap_ode_no_const;auto. }
  }

  { pose proof (h zeta (swap_assgn sw v)) as q.
    rewrite (ode_assign_as_map_if_no_const sw) in q; auto.
    rewrite in_map_iff in q.
    autodimp q hyp.
    { eexists; dands; eauto. }
    simpl in *.
    repnd; dands; auto.

    { eapply ex_derive_ext;[|exact q0]; introv; simpl; auto.
      unfold swap_state; simpl.
      rewrite swap_assgn_twice; auto. }

    { unfold swap_state in q1; simpl in q1.
      rewrite swap_assgn_twice in q1; auto. }

    { unfold swap_state in q; simpl in q.
      rewrite swap_assgn_twice in q.
      fold KD in *.
      rewrite q.
      symmetry.
      apply dynamic_semantics_ode_fun_swap_ode_no_const; auto. }
  }
Qed.

Lemma ode_footprint_diff_swap_no_const :
  forall sw ode I,
    no_const_ode_ode ode = true
    -> ode_footprint_diff I ode
       = map (swap_assgn sw) (ode_footprint_diff I (swap_ode sw ode)).
Proof.
  introv noc.
  unfold ode_footprint_diff.
  allrw map_map; unfold compose.
  apply eq_maps3.

  { autorewrite with core; auto. }

  { introv i.
    simpl.
    unfold KD; f_equal.
    rewrite (ode_assign_as_map_if_no_const sw I ode) in i; auto.
    rewrite combine_map_l in i.
    apply in_map_iff in i; exrepnd; ginv; auto.
  }
Qed.

Lemma ode_footprint_vars_swap_no_const :
  forall sw ode I,
    no_const_ode_ode ode = true
    -> ode_footprint_vars I ode
       = map (swap_assgn sw) (ode_footprint_vars I (swap_ode sw ode)).
Proof.
  introv noc.
  unfold ode_footprint_vars.
  rewrite <- ode_assign_as_map_if_no_const; auto.
Qed.

Lemma ode_footprint_swap_no_const :
  forall sw ode I,
    no_const_ode_ode ode = true
    -> ode_footprint I ode
       = map (swap_assgn sw) (ode_footprint I (swap_ode sw ode)).
Proof.
  introv noc.
  unfold ode_footprint.
  rewrite (ode_footprint_diff_swap_no_const sw); auto.
  rewrite (ode_footprint_vars_swap_no_const sw); auto.
  rewrite map_app; auto.
Qed.

Lemma swap_dynamic_semantics_formula_program_no_const :
  (forall f sw I v,
      no_const_ode_formula f = true
      ->
      (
        dynamic_semantics_formula I (swap_formula sw f) v
        <->
        dynamic_semantics_formula I f (swap_state sw v)
      )
  )
  /\
  (forall p sw I v w,
      no_const_ode_program p = true
      ->
      (
        dynamic_semantics_program I (swap_program sw p) v w
        <->
        dynamic_semantics_program I p (swap_state sw v) (swap_state sw w)
      )
  ).
Proof.
  form_prog_ind Case;
    introv;
    simpl in *; tcsp; auto;
      try (complete (repeat (rewrite swap_term_dynamic_semantics_term_same_I); tcsp));
      try (complete (introv ih noc; introv; rewrite ih; tcsp));
      try (complete (introv ih1 ih2 noc;
                     apply andb_true_iff in noc; repnd;
                     split; introv h; repnd;
                     try (rewrite <- ih1, <- ih2; tcsp);
                     try (rewrite ih1, ih2; tcsp))).

  { Case "KFpredOf".
    introv noc; GC.
    rewrite vec_map_map; unfold compose.
    match goal with
    | [ |- _ _ ?x <-> _ _ ?y ] => assert (x = y) as xx;[|rewrite xx;tcsp];[]
    end.
    apply eq_vec_map; introv i.
    rewrite swap_term_dynamic_semantics_term_same_I; auto.
  }

  { Case "KFforallVars".
    introv ih; introv.
    split; intro h; introv len; autorewrite with core in *.

    { applydup h in len.
      rewrite ih in len0; auto.
      eapply ext_dynamic_semantics_formula;[| |exact len0].
      { introv; apply upd_list_state_swap_state. }
      { apply ext_interpretations_refl. }
    }

    { applydup h in len.
      rewrite ih; auto.
      eapply ext_dynamic_semantics_formula;[| |exact len0].
      { introv; symmetry; apply upd_list_state_swap_state. }
      { apply ext_interpretations_refl. }
    }
  }

  { Case "KFexistsVars".
    introv ih; introv.
    split; intro h; introv; exrepnd; exists rs; autorewrite with core in *; dands; auto.

    { apply ih in h0; auto.
      eapply ext_dynamic_semantics_formula;[| |exact h0].
      { introv; apply upd_list_state_swap_state. }
      { apply ext_interpretations_refl. }
    }

    { apply ih; auto.
      eapply ext_dynamic_semantics_formula;[| |exact h0].
      { introv; symmetry; apply upd_list_state_swap_state. }
      { apply ext_interpretations_refl. }
    }
  }

  { Case "KFbox".
    introv ihp ihf noc; introv.
    apply andb_true_iff in noc; repnd.
    split; introv h dsp.

    {
      pose proof (ihf sw I (swap_state sw w)) as q.
      rewrite swap_state_twice in q; apply q; clear q; auto.
      apply h; clear h.
      apply ihp; auto.
      rewrite swap_state_twice; auto.
    }

    {
      apply ihf; clear ihf; auto.
      apply h; clear h.
      apply ihp; auto.
    }
  }

  { Case "KFdiamond".
    introv ihp ihf noc; introv.
    apply andb_true_iff in noc; repnd.
    split; introv h; exrepnd.

    {
      exists (swap_state sw w); dands; auto.
      { apply ihf; auto. }
      { apply ihp; auto. }
    }

    {
      exists (swap_state sw w); dands.
      { apply ihf; auto; rewrite swap_state_twice; auto. }
      { apply ihp; auto; rewrite swap_state_twice; auto. }
    }
  }

  { Case "KPassign".
    intro noc; GC.
    rewrite swap_term_dynamic_semantics_term_same_I.
    split; introv h; unfold differ_state_except in *;
      repnd; dands; auto; introv i.

    { unfold swap_state.
      apply h0; intro xx.
      apply eq_swap_assgn_implies_eq in xx; tcsp. }

    { pose proof (h0 (swap_assgn sw y)) as q.
      autodimp q hyp.
      { intro xx; subst.
        autorewrite with core in *; tcsp. }
      repeat (rewrite swap_state_swap_assgn in q); auto. }
  }

  { Case "KPassignAny".
    intro noc; GC.
    split; intro h; exrepnd; exists r; unfold differ_state_except in *;
      repnd; dands; auto; introv i.

    { unfold swap_state.
      apply h1; intro xx.
      apply eq_swap_assgn_implies_eq in xx; tcsp. }

    { pose proof (h1 (swap_assgn sw y)) as q.
      autodimp q hyp.
      { intro xx; subst.
        autorewrite with core in *; tcsp. }
      repeat (rewrite swap_state_swap_assgn in q); auto. }
  }

  { Case "KPtest".
    introv ihf noc; introv.
    split; intro h; repnd; subst.

    { rewrite <- ihf; dands; auto. }

    { rewrite <- ihf in h; dands; auto.
      apply swap_state_inj in h0; auto. }
  }

  { Case "KPcompose".
    introv ih1 ih2 noc; introv.
    apply andb_true_iff in noc; repnd.
    split; intro h; exrepnd.
    { rewrite ih1 in h1; auto.
      rewrite ih2 in h0; auto.
      eexists; dands; eauto. }
    { pose proof (ih1 sw I v (swap_state sw s)) as q.
      rewrite swap_state_twice in q.
      apply q in h1; clear q; auto.

      pose proof (ih2 sw I (swap_state sw s) w) as q; auto.
      rewrite swap_state_twice in q.
      apply q in h0; clear q; auto.

      exists (swap_state sw s); dands; auto.
    }
  }

  { Case "KPloop".
    introv ih noc; introv; split; introv h;
      allrw program_close_implies_all; exrepnd; exists n.

    {
      revert w h0.
      induction n; introv dsp; simpl in *; repnd; subst; dands; auto.
      exrepnd.
      exists (swap_state sw s).
      apply IHn in dsp1; clear IHn.
      apply ih in dsp0; clear ih; auto.
    }

    {
      revert w h0.
      induction n; introv dsp; simpl in *; repnd; subst; dands; auto.

      { apply swap_state_inj in dsp0; auto. }

      exrepnd.
      pose proof (IHn (swap_state sw s)) as q; clear IHn.
      rewrite swap_state_twice in q; apply q in dsp1; clear q.
      pose proof (ih sw I (swap_state sw s) w) as q; clear ih.
      rewrite swap_state_twice in q; apply q in dsp0; clear q; auto.
      exists (swap_state sw s); dands; auto.
    }
  }

  { Case "KPodeSystem".
    introv ih noc; introv.
    apply andb_true_iff in noc; repnd.
    split; intro h; exrepnd; subst.

    { exists r (fun x => swap_state sw (phi x)).
      dands; auto.

      { introv i.
        unfold swap_state.
        apply h0.
        rewrite (ode_footprint_diff_swap_no_const sw) in i; auto.
        intro j; destruct i; rewrite in_map_iff.
        eexists; dands;[|eauto].
        rewrite swap_assgn_twice; auto. }

      { apply dynamic_semantics_ode_swap_ode_no_const; auto. }

      { introv; pose proof (h1 zeta) as q; clear h1; repnd.
        unfold swap_state; simpl.
        rewrite ih in q0; clear ih; auto.
        unfold swap_state in q0; dands; auto.

        introv i.
        apply q.
        rewrite (ode_footprint_swap_no_const sw) in i; auto.
        intro j; destruct i; rewrite in_map_iff.
        eexists; dands;[|eauto].
        rewrite swap_assgn_twice; auto. }
    }

    { exists r (fun x => swap_state sw (phi x)).
      unfold swap_state in *; simpl in *.
      dands; auto.

      { introv i.
        pose proof (h0 (swap_assgn sw x)) as q.
        rewrite (ode_footprint_diff_swap_no_const sw) in q; auto.
        autodimp q hyp.
        { rewrite in_map_iff.
          introv xx; destruct i; exrepnd.
          apply eq_swap_assgn_implies_eq in xx1; subst; auto. }
        rewrite swap_assgn_twice in q; auto. }

      { rewrite <- h2.
        apply functional_extensionality; introv.
        rewrite swap_assgn_twice; auto. }

      { apply dynamic_semantics_ode_swap_ode_no_const; auto.
        unfold swap_state; simpl.
        assert ((fun (x : R) (a : KAssignable) => phi x (swap_assgn sw (swap_assgn sw a)))
                = phi) as xx.
        { apply functional_extensionality; introv.
          apply functional_extensionality; introv.
          rewrite swap_assgn_twice; auto. }
        rewrite xx; clear xx; auto. }

      { introv; pose proof (h1 zeta) as q; clear h1; repnd.
        rewrite ih; clear ih; auto.
        assert ((fun (a : KAssignable) => phi zeta (swap_assgn sw (swap_assgn sw a)))
                = phi zeta) as xx.
        { apply functional_extensionality; introv.
          rewrite swap_assgn_twice; auto. }
        rewrite xx; clear xx; dands; auto.

        introv i.
        apply q.
        rewrite (ode_footprint_swap_no_const sw); auto.
        intro j; destruct i; rewrite in_map_iff in j; exrepnd.
        apply eq_swap_assgn_implies_eq in j1; subst; auto. }
    }
  }
Qed.

Lemma swap_dynamic_semantics_formula_no_const :
  forall f sw I v,
    no_const_ode_formula f = true
    ->
    (
      dynamic_semantics_formula I (swap_formula sw f) v
      <->
      dynamic_semantics_formula I f (swap_state sw v)
    ).
Proof.
  pose proof swap_dynamic_semantics_formula_program_no_const; tcsp.
Qed.

Lemma swap_bound_var_assign_box :
  forall F (x y : KVariable) t,
    no_const_ode_formula F = true
    -> Df_formula_valid (KFbox (KPassign x t) F)
    -> (forall a,
           in_eassignables a (free_vars_formula F) = true
           -> KAssignable2variable a <> y)
    -> (forall a,
           in_eassignables a (free_vars_formula F) = true
           -> KAssignable2variable a = x
           -> a = KAssignVar x)
    -> Df_formula_valid (KFbox (KPassign y t) (swap_formula (MkSwapping x y) F)).
Proof.
  introv noc valid niyF nixF dsp.
  simpl in *.

  unfold Df_formula_valid, Df_formula_valid_in_I in valid; simpl in valid.

  apply swap_dynamic_semantics_formula_no_const; auto.

  destruct (KVariable_dec x y) as [d|d]; subst.

  { rewrite swap_state_idem.
    apply (valid _ v); auto. }

  destruct dsp as [dsp1 dsp2].

  apply (coincidence_formula
           _ _ (upd_state (upd_state w y (v y)) x (dynamic_semantics_term I v t))
           _ I); eauto with core.

  {
    introv i; simpl.
    unfold swap_state, upd_state.
    repeat (dest_cases z; subst; simpl in *; autorewrite with core; auto).

    { apply niyF in i; simpl in *; tcsp. }

    applydup niyF in i.

    destruct (KVariable_dec (KAssignable2variable x0) x) as [d1|d1].

    { apply nixF in i; auto.
      destruct x0; ginv; subst; tcsp. }

    { rewrite swap_assgn_not_in; auto. }
  }

  apply (valid _ v); clear valid.

  split; auto;[|unfold upd_state; dest_cases w].
  introv dx.
  rewrite upd_state_diff; auto.

  unfold upd_state; dest_cases w.
Qed.
