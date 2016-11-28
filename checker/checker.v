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


Require Export soundness.
Require Export swapping.
Require Export DDLaxioms.
Require Export differential_axioms.
Require Export differential_invariant.
Require Export decidability.


Definition HName := String.string.
Definition HName_dec : Deq HName := String.string_dec.

Record hypothesis :=
  MkHyp
    {
      hyp_name : HName;
      hyp_form : Formula
    }.
Notation "a : b" := (MkHyp a b) (at level 70).

Definition hypotheses := list hypothesis.
Definition emHyps : hypotheses := [].
Notation "∅" := emHyps.
Definition addHyp (H : hypotheses) (h : hypothesis) : hypotheses :=
  snoc H h.
Notation "a • b" := (addHyp a b) (at level 70).

Record sequent :=
  MkSeq
    {
      seq_hyps : list hypothesis;
      seq_concl : Formula
    }.
Notation "a ⊢ b" := (MkSeq a b) (at level 70).

Definition DSF (F : Formula) (I : interpretation) (s : state) :=
  dynamic_semantics_formula I F s.

(**

  The semantics of a sequent of the form h1,..,hn |- C is the same as the semantics
  of the formula h1 -> ... -> hn -> C.

 *)

Definition sequent_true_I_v (s : sequent) (I : interpretation) (v : state) :=
  (forall h, List.In h (seq_hyps s) -> DSF (hyp_form h) I v)
  -> DSF (seq_concl s) I v.

Definition sequent_true_I (s : sequent) (I : interpretation) :=
  forall v, sequent_true_I_v s I v.

Definition sequent_true (s : sequent) :=
  forall I, sequent_true_I s I.

Record Rule :=
  MkRULE
    {
      RULE_premisses : list sequent;
      RULE_conclusion : sequent
    }.

Definition Rule_true_I (r : Rule) :=
  forall (I : interpretation),
    (forall s : sequent, List.In s (RULE_premisses r) -> sequent_true_I s I)
    -> sequent_true_I (RULE_conclusion r) I.

Definition Rule_true (r : Rule) :=
  (forall s : sequent, List.In s (RULE_premisses r) -> sequent_true s)
  -> sequent_true (RULE_conclusion r).

Lemma Rule_true_I_implies_Rule_true :
  forall r, Rule_true_I r -> Rule_true r.
Proof.
  introv rt sgs hyps; introv.
  apply rt; auto.
  introv p; apply sgs; auto.
Qed.


(**

  To move an hypothesis to the context:

  H , x : P |- Q
  --------------
   H |- P -> Q

 *)
Definition RULE_imply_right_const x H : Rule :=
    MkRULE
      [MkSeq (addHyp H (MkHyp x fpredp)) fpredq]
      (MkSeq H (KFimply fpredp fpredq)).

Lemma RULE_imply_right_const_true :
  forall x H, Rule_true (RULE_imply_right_const x H).
Proof.
  introv subgoals hyps i; simpl in *.
  pose proof (subgoals (MkSeq (snoc H (MkHyp x fpredp)) fpredq)) as h; clear subgoals.
  autodimp h hyp.
  pose proof (h I v) as q; clear h; simpl in q.
  unfold sequent_true_I_v in q.
  autodimp q hyp.
  introv j; apply in_snoc in j; repndors; subst; simpl in *; auto.
Qed.


(**

  To move an hypothesis to the context:

  H , x : P(v) |- Q(v)
  --------------------
   H |- P(v) -> Q(v)

 *)
Definition RULE_imply_right x H n : Rule :=
    MkRULE
      [MkSeq (addHyp H (MkHyp x (PofVN predp varx n))) (PofVN predq varx n)]
      (MkSeq H (KFimply (PofVN predp varx n) (PofVN predq varx n))).

Lemma RULE_imply_right_true_I :
  forall x H n, Rule_true_I (RULE_imply_right x H n).
Proof.
  introv subgoals hyps i; simpl in *.
  dLin_hyp h.
  pose proof (h v) as q; clear h; simpl in q.
  unfold sequent_true_I_v in q.
  autodimp q hyp.
  introv j; apply in_snoc in j; repndors; subst; simpl in *; auto.
Qed.

Lemma RULE_imply_right_true :
  forall x H n, Rule_true (RULE_imply_right x H n).
Proof.
  introv.
  apply Rule_true_I_implies_Rule_true.
  apply RULE_imply_right_true_I.
Qed.


(**

  To move an hypothesis to the context:

  H , x : P |- Q
  --------------------
   H |- P -> Q

 *)
Definition RULE_imply_right_quant x H : Rule :=
    MkRULE
      [MkSeq (addHyp H (MkHyp x quantP)) quantQ]
      (MkSeq H (KFimply quantP quantQ)).

Lemma RULE_imply_right_quant_true_I :
  forall x H, Rule_true_I (RULE_imply_right_quant x H).
Proof.
  introv subgoals hyps i; simpl in *.
  dLin_hyp h.
  pose proof (h v) as q; clear h; simpl in q.
  unfold sequent_true_I_v in q.
  autodimp q hyp.
  introv j; apply in_snoc in j; repndors; subst; simpl in *; auto.
Qed.

Lemma RULE_imply_right_quant_true :
  forall x H, Rule_true (RULE_imply_right_quant x H).
Proof.
  introv.
  apply Rule_true_I_implies_Rule_true.
  apply RULE_imply_right_quant_true_I.
Qed.


(**

  To move an hypothesis to the context:

  H , x : P |- Q
  --------------------
   H |- P -> Q

 *)
Definition RULE_imply_right_sch x H P Q : Rule :=
    MkRULE
      [MkSeq (addHyp H (MkHyp x P)) Q]
      (MkSeq H (KFimply P Q)).

Lemma RULE_imply_right_sch_true_I :
  forall x H P Q, Rule_true_I (RULE_imply_right_sch x H P Q).
Proof.
  introv subgoals hyps i; simpl in *.
  dLin_hyp h.
  pose proof (h v) as q; clear h; simpl in q.
  unfold sequent_true_I_v in q.
  autodimp q hyp.
  introv j; apply in_snoc in j; repndors; subst; simpl in *; auto.
Qed.

Lemma RULE_imply_right_sch_true :
  forall x H P Q, Rule_true (RULE_imply_right_sch x H P Q).
Proof.
  introv.
  apply Rule_true_I_implies_Rule_true.
  apply RULE_imply_right_sch_true_I.
Qed.


Definition addHyps (H J : hypotheses) : hypotheses := (H ++ J)%list.
Notation "a ⊕ b" := (addHyps a b) (at level 70).


(**

  H , x : P , y : Q , J |- R
  --------------------------
   H , x : P /\ Q , J |- R

 *)
Definition RULE_and_left_sch x y H J P Q R : Rule :=
    MkRULE
      [MkSeq (addHyps (addHyp (addHyp H (MkHyp x P)) (MkHyp y Q)) J) R]
      (MkSeq (addHyps (addHyp H (MkHyp x (KFand P Q))) J) R).

Lemma RULE_and_left_sch_true_I :
  forall x y H J P Q R, Rule_true_I (RULE_and_left_sch x y H J P Q R).
Proof.
  introv subgoals hyps; simpl in *.
  dLin_hyp h.
  pose proof (h v) as q; clear h; simpl in q.
  unfold sequent_true_I_v in q.
  autodimp q hyp.

  introv j; simpl in *.
  rewrite in_app_iff in j.
  rewrite in_snoc in j.
  rewrite in_snoc in j.
  repndors; subst; simpl in *.

  { apply hyps.
    rewrite in_app_iff.
    rewrite in_snoc; tcsp. }

  { pose proof (hyps ((x : KFand P Q))) as q; simpl in q.
    rewrite in_app_iff in q.
    rewrite in_snoc in q.
    autodimp q hyp; tcsp. }

  { simpl.
    pose proof (hyps ((x : KFand P Q))) as q; simpl in q.
    rewrite in_app_iff in q.
    rewrite in_snoc in q.
    autodimp q hyp; tcsp. }

  { apply hyps.
    rewrite in_app_iff.
    rewrite in_snoc; tcsp. }
Qed.

Lemma RULE_and_left_sch_true :
  forall x y H J P Q R, Rule_true (RULE_and_left_sch x y H J P Q R).
Proof.
  introv.
  apply Rule_true_I_implies_Rule_true.
  apply RULE_and_left_sch_true_I.
Qed.


(**

  H , x : P , J |- R     H , x : Q , J |- R
  -----------------------------------------
           H , x : P \/ Q , J |- R

 *)
Definition RULE_or_left_sch x H J P Q R : Rule :=
    MkRULE
      [MkSeq (addHyps (addHyp H (MkHyp x P)) J) R,
       MkSeq (addHyps (addHyp H (MkHyp x Q)) J) R]
      (MkSeq (addHyps (addHyp H (MkHyp x (KFor P Q))) J) R).

Lemma RULE_or_left_sch_true_I :
  forall x H J P Q R, Rule_true_I (RULE_or_left_sch x H J P Q R).
Proof.
  introv subgoals hyps; simpl in *.
  dLin_hyp h.

  pose proof (hyps (MkHyp x (KFor P Q))) as hor; simpl in hor.
  rewrite in_app_iff in hor; rewrite in_snoc in hor; simpl in hor.
  autodimp hor hyp.
  repndors.

  {
    pose proof (h v) as q; clear h; simpl in q.
    unfold sequent_true_I_v in q.
    autodimp q hyp.

    introv j; simpl in *.
    rewrite in_app_iff in j.
    rewrite in_snoc in j.
    repndors; subst; simpl in *.

    { apply hyps.
      rewrite in_app_iff.
      rewrite in_snoc; tcsp. }

    { pose proof (hyps ((x : KFor P Q))) as q; simpl in q.
      rewrite in_app_iff in q.
      rewrite in_snoc in q.
      autodimp q hyp; tcsp. }

    { apply hyps.
      rewrite in_app_iff.
      rewrite in_snoc; tcsp. }
  }

  {
    pose proof (h0 v) as q; clear h; simpl in q.
    unfold sequent_true_I_v in q.
    autodimp q hyp.

    introv j; simpl in *.
    rewrite in_app_iff in j.
    rewrite in_snoc in j.
    repndors; subst; simpl in *.

    { apply hyps.
      rewrite in_app_iff.
      rewrite in_snoc; tcsp. }

    { pose proof (hyps ((x : KFor P Q))) as q; simpl in q.
      rewrite in_app_iff in q.
      rewrite in_snoc in q.
      autodimp q hyp; tcsp. }

    { apply hyps.
      rewrite in_app_iff.
      rewrite in_snoc; tcsp. }
  }
Qed.

Lemma RULE_or_left_sch_true :
  forall x H J P Q R, Rule_true (RULE_or_left_sch x H J P Q R).
Proof.
  introv.
  apply Rule_true_I_implies_Rule_true.
  apply RULE_or_left_sch_true_I.
Qed.



(**

     H |- P
  -----------
  H |- P \/ Q

 *)
Definition RULE_or_right1_sch H P Q : Rule :=
    MkRULE
      [MkSeq H P]
      (MkSeq H (KFor P Q)).

Lemma RULE_or_right1_sch_true_I :
  forall H P Q, Rule_true_I (RULE_or_right1_sch H P Q).
Proof.
  introv subgoals hyps; simpl in *.
  dLin_hyp h.
  left.
  apply h; auto.
Qed.

Lemma RULE_or_right1_sch_true :
  forall H P Q, Rule_true (RULE_or_right1_sch H P Q).
Proof.
  introv.
  apply Rule_true_I_implies_Rule_true.
  apply RULE_or_right1_sch_true_I.
Qed.


(**

     H |- Q
  -----------
  H |- P \/ Q

 *)
Definition RULE_or_right2_sch H P Q : Rule :=
    MkRULE
      [MkSeq H Q]
      (MkSeq H (KFor P Q)).

Lemma RULE_or_right2_sch_true_I :
  forall H P Q, Rule_true_I (RULE_or_right2_sch H P Q).
Proof.
  introv subgoals hyps; simpl in *.
  dLin_hyp h.
  right.
  apply h; auto.
Qed.

Lemma RULE_or_right2_sch_true :
  forall H P Q, Rule_true (RULE_or_right2_sch H P Q).
Proof.
  introv.
  apply Rule_true_I_implies_Rule_true.
  apply RULE_or_right2_sch_true_I.
Qed.


(**

  H , J |- P    H , x : Q , J |- R
  ----------------------------
    H , x : P -> Q , J |- R

 *)
Definition RULE_imply_left_sch x H J P Q R : Rule :=
    MkRULE
      [MkSeq (addHyps H J) P, MkSeq (addHyps (addHyp H (MkHyp x Q)) J) R]
      (MkSeq (addHyps (addHyp H (MkHyp x (KFimply P Q))) J) R).

Lemma RULE_imply_left_sch_true_I :
  forall x H J P Q R, Rule_true_I (RULE_imply_left_sch x H J P Q R).
Proof.
  introv subgoals hyps; simpl in *.
  dLin_hyp h.
  pose proof (h0 v) as q; clear h0; simpl in q.
  unfold sequent_true_I_v in q.
  autodimp q hyp.

  introv j; simpl in *.
  rewrite in_app_iff in j.
  rewrite in_snoc in j.
  repndors; subst; simpl in *.

  { apply hyps.
    rewrite in_app_iff.
    rewrite in_snoc; tcsp. }

  { pose proof (hyps ((x : KFimply P Q))) as q; simpl in q.
    rewrite in_app_iff in q.
    rewrite in_snoc in q.
    repeat (autodimp q hyp); tcsp.
    apply h; simpl; introv i.
    apply in_app_iff in i.
    apply hyps.
    rewrite in_app_iff; rewrite in_snoc; simpl; tcsp. }

  { apply hyps.
    rewrite in_app_iff.
    rewrite in_snoc; tcsp. }
Qed.

Lemma RULE_imply_left_sch_true :
  forall x H J P Q R, Rule_true (RULE_imply_left_sch x H J P Q R).
Proof.
  introv.
  apply Rule_true_I_implies_Rule_true.
  apply RULE_imply_left_sch_true_I.
Qed.


(*
(* v≥0 → [{x'=v∧true}] v≥0 *)

Definition Example0 : Formula :=
  KFimply
    (KFgreaterEqual termv term0)
    (KFbox
       (KPodeSystem
          (ODEsing varxp termv)
          KFtrue
       )
       (KFgreaterEqual termv term0)
    ).

Definition Example0_rule : rule := MkRule [] Example0.

Lemma Example0_true : rule_true Example0_rule.
Proof.
  pose proof V_axiom_sound as v.
  unfold rule_true in v; simpl in v.
  autodimp v hyp; tcsp;[].

  (* use US_sound_rule? *)

Qed.
 *)


Definition swap_hyp (sw : swapping) (h : hypothesis) : hypothesis :=
  MkHyp
    (hyp_name h)
    (swap_formula sw (hyp_form h)).

Definition swap_hyps (sw : swapping) (H : hypotheses) : hypotheses :=
  map (swap_hyp sw) H.

Definition swap_sequent (sw : swapping) (s : sequent) : sequent :=
  MkSeq
    (swap_hyps sw (seq_hyps s))
    (swap_formula sw (seq_concl s)).

Definition swap_Rule (sw : swapping) (r : Rule) : Rule :=
  MkRULE
    (map (swap_sequent sw) (RULE_premisses r))
    (swap_sequent sw (RULE_conclusion r)).

Lemma swap_Rule_true :
  forall (sw : swapping) (r : Rule),
    Rule_true r
    -> Rule_true (swap_Rule sw r).
Proof.
  introv rt hhyps; simpl in *.
  destruct r as [Ps G]; simpl in *.
  introv hyps; simpl in *.

  apply swap_dynamic_semantics_formula.
  apply rt; simpl.

  { introv i.
    pose proof (hhyps (swap_sequent sw s)) as q; clear hhyps.
    autodimp q hyp.
    { apply in_map_iff; eexists; dands; eauto. }
    introv hs; simpl in *.
    pose proof (q (swap_interp sw I0) (swap_state sw v0)) as h; simpl in h; clear q.
    unfold sequent_true_I_v in h; simpl in *.
    autodimp h hyp.

    { introv j.
      unfold swap_hyps in j.
      apply in_map_iff in j; exrepnd; subst.
      applydup hs in j0.
      apply swap_dynamic_semantics_formula.
      rewrite swap_state_twice.
      eapply ext_dynamic_semantics_formula;
        [introv;reflexivity
        |apply swap_interp_twice
        |].
      auto. }

    { apply (swap_dynamic_semantics_formula _ _ (swap_interp sw I0)) in h.
      rewrite swap_state_twice in h.
      eapply ext_dynamic_semantics_formula in h;
        [|introv;reflexivity
         |apply ext_interpretations_sym;apply swap_interp_twice
        ].
      auto. }
  }

  { introv ih.
    pose proof (hyps (swap_hyp sw h)) as q; clear hyps.
    autodimp q hyp.
    { unfold swap_hyps; apply in_map_iff.
      eexists; dands; eauto. }
    simpl in *.
    apply swap_dynamic_semantics_formula in q; auto. }
Qed.

Lemma swap_Rule_true_I :
  forall (sw : swapping) (r : Rule),
    Rule_true_I r
    -> Rule_true_I (swap_Rule sw r).
Proof.
  introv rt hhyps; simpl in *.
  destruct r as [Ps G]; simpl in *.
  introv hyps; simpl in *.

  apply swap_dynamic_semantics_formula.
  apply rt; simpl.

  { introv i.
    pose proof (hhyps (swap_sequent sw s)) as q; clear hhyps.
    autodimp q hyp.
    { apply in_map_iff; eexists; dands; eauto. }
    introv hs; simpl in *.
    pose proof (q (swap_state sw v0)) as h; simpl in h; clear q.
    unfold sequent_true_I_v in h; simpl in *.
    autodimp h hyp.

    { introv j.
      unfold swap_hyps in j.
      apply in_map_iff in j; exrepnd; subst.
      applydup hs in j0.
      apply swap_dynamic_semantics_formula.
      rewrite swap_state_twice; auto. }

    { apply (swap_dynamic_semantics_formula _ _ I) in h.
      rewrite swap_state_twice in h; auto. }
  }

  { introv ih.
    pose proof (hyps (swap_hyp sw h)) as q; clear hyps.
    autodimp q hyp.
    { unfold swap_hyps; apply in_map_iff.
      eexists; dands; eauto. }
    simpl in *.
    apply swap_dynamic_semantics_formula in q; auto. }
Qed.

Definition US := UniformSubstitution.

Definition US_hyp_true (sub : US) (h : hypothesis) : hypothesis :=
  MkHyp
    (hyp_name h)
    (uniform_substitution_formula_opt_true (hyp_form h) sub).

Definition US_hyp_false (sub : US) (h : hypothesis) : hypothesis :=
  MkHyp
    (hyp_name h)
    (uniform_substitution_formula_opt_false (hyp_form h) sub).

Definition US_hyps_true (sub : US) (H : hypotheses) : hypotheses :=
  map (US_hyp_true sub) H.

Definition US_hyps_false (sub : US) (H : hypotheses) : hypotheses :=
  map (US_hyp_false sub) H.

Definition US_sequent_false (sub : US) (seq : sequent) : sequent :=
  MkSeq
    (US_hyps_true sub (seq_hyps seq))
    (uniform_substitution_formula_opt_false (seq_concl seq) sub).

Definition US_sequent_true (sub : US) (seq : sequent) : sequent :=
  MkSeq
    (US_hyps_false sub (seq_hyps seq))
    (uniform_substitution_formula_opt_true (seq_concl seq) sub).

Definition US_Rule (sub : US) (r : Rule) : Rule :=
  MkRULE
    (map (US_sequent_false sub) (RULE_premisses r))
    (US_sequent_true sub (RULE_conclusion r)).

Lemma US_Rule_true_I :
  forall (sub : UniformSubstitution) (r : Rule),
    free_vars_uniform_substitution sub = EA_assignables []
    -> Rule_true_I r
    -> Rule_true_I (US_Rule sub r).
Proof.
  introv fvars rt sgs hyps; simpl in *.
  destruct r as [Ps G]; simpl in *.
  unfold uniform_substitution_formula_opt_true.
  dest_sub w; simpl; tcsp; symmetry in Heqw;[].

  pose proof (us_lemma_formula (seq_concl G) sub I v) as h.
  unfold on_uniform_substitution_formula in h.
  rewrite Heqw in h.
  apply h; clear h.
  apply rt; clear rt; simpl in *.

  {
    introv i hs.
    pose proof (sgs (US_sequent_false sub s)) as q; clear sgs.
    rewrite in_map_iff in q.
    autodimp q hyp;[eexists; dands; eauto|].

    pose proof (q v0) as h; clear q.
    unfold sequent_true_I_v in h; simpl in *.
    autodimp h hyp.
    { introv j; simpl in *.
      unfold US_hyps_true in j.
      rewrite in_map_iff in j; exrepnd; subst; simpl in *.
      applydup hs in j0 as k.
      unfold uniform_substitution_formula_opt_true.
      dest_sub z; simpl; tcsp; symmetry in Heqz;[].

      pose proof (us_lemma_formula (hyp_form x) sub I v0) as h.
      unfold on_uniform_substitution_formula in h.
      rewrite Heqz in h.
      apply h; clear h.

      eapply substitution_adjoint_admissible_formula0;[|exact k].
      introv j.

      pose proof (free_vars_sub_restrict_formula_subset_free_vars_uniform_substitution sub (hyp_form x)) as ss.
      eapply eassignables_subset_prop in ss;[|exact j].
      rewrite fvars in ss; simpl in ss; ginv.
    }

    simpl in *.
    unfold uniform_substitution_formula_opt_false in h.
    dest_sub z;[|inversion h];[]; symmetry in Heqz.

    pose proof (us_lemma_formula (seq_concl s) sub I v0) as q.
    unfold on_uniform_substitution_formula in q.
    rewrite Heqz in q; apply q in h; clear q.

    eapply substitution_adjoint_admissible_formula0;[|exact h].
    introv j.

    pose proof (free_vars_sub_restrict_formula_subset_free_vars_uniform_substitution sub (seq_concl s)) as ss.
    eapply eassignables_subset_prop in ss;[|exact j].
    rewrite fvars in ss; simpl in ss; ginv.
  }

  {
    introv i.
    pose proof (hyps (US_hyp_false sub h)) as q.
    unfold US_hyps_false in q.
    rewrite in_map_iff in q.
    autodimp q hyp;[eexists; dands; eauto|].
    simpl in *.
    unfold uniform_substitution_formula_opt_false in q.
    dest_sub z;[|inversion q];[]; symmetry in Heqz.

    pose proof (us_lemma_formula (hyp_form h) sub I v) as w.
    unfold on_uniform_substitution_formula in w.
    rewrite Heqz in w; apply w in q; clear w.

    eapply substitution_adjoint_admissible_formula0;[|exact q].
    introv j.

    pose proof (free_vars_sub_restrict_formula_subset_free_vars_uniform_substitution sub (hyp_form h)) as ss.
    eapply eassignables_subset_prop in ss;[|exact j].
    rewrite fvars in ss; simpl in ss; ginv.
  }
Qed.

Definition rule_true_I_v (r : rule) :=
  forall I v,
    (forall f, List.In f (premisses r) -> DSF f I v)
    -> DSF (conclusion r) I v.

Lemma US_sound_rule_I_v :
  forall (r : rule) (s : UniformSubstitution),
    rule_true_I_v r
    -> rule_true_I_v
         (MkRule
            (map (fun f => uniform_substitution_formula_opt_false f s) (premisses r))
            (uniform_substitution_formula_opt_true (conclusion r) s)).
Proof.
  introv loc hyps; simpl in *.
  unfold uniform_substitution_formula_opt_true.
  dest_sub w; simpl; symmetry in Heqw; tcsp;[].

  pose proof (us_lemma_formula (conclusion r) s I v) as h.
  unfold on_uniform_substitution_formula in h.
  rewrite Heqw in h.
  apply h; clear h.
  apply loc; clear loc.
  introv i.

  pose proof (hyps (uniform_substitution_formula_opt_false f0 s)) as q; clear hyps.
  rewrite in_map_iff in q.
  autodimp q hyp.
  { exists f0; dands; auto. }
  introv.
  unfold uniform_substitution_formula_opt_false in q.
  dest_sub z;[|inversion q];[]; symmetry in Heqz.

  pose proof (us_lemma_formula f0 s I v) as h.
  unfold on_uniform_substitution_formula in h.
  rewrite Heqz in h; apply h in q; clear h; auto.
Qed.


Definition Rule_thin_all_hyps H F : Rule :=
  MkRULE [(∅ ⊢ F)]  (H ⊢ F).

Lemma Rule_thin_all_hyps_true :
  forall H F, Rule_true (Rule_thin_all_hyps H F).
Proof.
  introv hseq hhyps; simpl in *.
  dLin_hyp h.
  apply h; simpl; tcsp.
Qed.

Definition US_seq_Rule (sub : US) (F : Formula) : Rule :=
  MkRULE
    [(∅ ⊢ F)]
    (US_sequent_true sub (∅ ⊢ F)).

Lemma US_seq_Rule_true :
  forall (sub : UniformSubstitution) (F : Formula),
    Rule_true (US_seq_Rule sub F).
Proof.
  introv hseq hhyps; simpl in *.
  apply US_sound; simpl in *.
  introv i; repndors; subst; tcsp.
  dLin_hyp h.
  repeat introv.
  apply h; auto; simpl; tcsp.
Qed.

Lemma sequent_true_I_v_if_rule_true :
  forall (H : hypotheses) (r : rule) I v,
    rule_true_I_v r
    -> (forall f, List.In f (premisses r) -> sequent_true_I_v (MkSeq H f) I v)
    -> sequent_true_I_v (MkSeq H (conclusion r)) I v.
Proof.
  introv rt imp hyps; simpl in *.
  apply rt; auto; clear rt.
  introv i.
  apply imp in i; simpl in *; clear imp.
  apply i; simpl; auto.
Qed.

Lemma rule_locally_sound_sp_cut :
  forall F Fs C,
    Df_formula_valid F
    -> rule_locally_sound (MkRule (F :: Fs) C)
    -> rule_locally_sound (MkRule Fs C).
Proof.
  introv v l i; simpl in *.
  apply l; simpl; introv j; repndors; subst; tcsp.
Qed.

Lemma rule_true_sp_cut :
  forall F Fs C,
    Df_formula_valid F
    -> rule_true (MkRule (F :: Fs) C)
    -> rule_true (MkRule Fs C).
Proof.
  introv v l i; simpl in *.
  apply l; simpl; introv j; repndors; subst; tcsp.
Qed.

Definition swap_rule_inv (f : Formula) (sw : swapping) : rule :=
  MkRule [swap_formula sw f] f.

Lemma swap_rule_inv_true :
  forall f sw, rule_true (swap_rule_inv f sw).
Proof.
  introv h; simpl in *.
  dLin_hyp q.
  repeat introv.
  pose proof (swap_dynamic_semantics_formula f sw (swap_interp sw I) (swap_state sw v)) as h.
  rewrite swap_state_twice in h.
  destruct h as [h z]; clear z.
  autodimp h hyp;[apply q|].
  eapply ext_dynamic_semantics_formula;[| |exact h]; auto.
  apply ext_interpretations_sym;apply swap_interp_twice.
Qed.


Lemma rule_true_no_premisses :
  forall F,
    rule_true (MkRule [] F) -> Df_formula_valid F.
Proof.
  introv rt; apply rt; simpl; tcsp.
Qed.

Lemma rule_locally_sound_no_premisses :
  forall F,
    rule_locally_sound (MkRule [] F) -> Df_formula_valid F.
Proof.
  introv rt; introv; apply rt; simpl; tcsp.
Qed.

Lemma do_swap_left :
  forall a b, swap (MkSwapping a b) a = b.
Proof.
  introv.
  unfold swap; simpl; dest_cases w.
Qed.
Hint Rewrite do_swap_left : core.


Lemma swap_varx0_varx_on_varx :
  swap (MkSwapping (variable (strN "x" 0)) varx) varx = variable (strN "x" 0).
Proof.
  unfold swap; simpl; auto.
Qed.
Hint Rewrite swap_varx0_varx_on_varx : core.

Lemma swap_varv_varx_on_varx :
  swap (MkSwapping varv varx) varx = varv.
Proof.
  unfold swap; simpl; auto.
Qed.
Hint Rewrite swap_varv_varx_on_varx : core.

Lemma swap_idem :
  forall v w, swap (MkSwapping v v) w = w.
Proof.
  introv; unfold swap; simpl; repeat (dest_cases w; GC).
Qed.
Hint Rewrite swap_idem : core.




Definition proof_state := list sequent.

Definition sound_proof_state (ps : proof_state) : Prop :=
  forall s, List.In s ps -> sequent_true s.

Definition sound_proof_state_I (ps : proof_state) (I : interpretation) : Prop :=
  forall s, List.In s ps -> sequent_true_I s I.

Definition SW := list swapping.

(**

  H , x : P -> Q , y : Q -> P , J |- R
  --------------------------
   H , x : P <-> Q , J |- R

 *)
Definition RULE_equiv_left_sch x y H J P Q R : Rule :=
    MkRULE
      [MkSeq (addHyps (addHyp (addHyp H (MkHyp x (KFimply P Q))) (MkHyp y (KFimply Q P))) J) R]
      (MkSeq (addHyps (addHyp H (MkHyp x (KFequiv P Q))) J) R).

Lemma RULE_equiv_left_sch_true_I :
  forall x y H J P Q R, Rule_true_I (RULE_equiv_left_sch x y H J P Q R).
Proof.
  introv subgoals hyps; simpl in *.
  dLin_hyp h.
  pose proof (h v) as q; clear h; simpl in q.
  unfold sequent_true_I_v in q.
  autodimp q hyp.

  introv j; simpl in *.
  rewrite in_app_iff in j.
  rewrite in_snoc in j.
  rewrite in_snoc in j.
  repndors; subst; simpl in *.

  { apply hyps.
    rewrite in_app_iff.
    rewrite in_snoc; tcsp. }

  { pose proof (hyps ((x : KFequiv P Q))) as q; simpl in q.
    rewrite in_app_iff in q.
    rewrite in_snoc in q.
    autodimp q hyp; tcsp.
    rewrite q; auto. }

  { simpl.
    pose proof (hyps ((x : KFequiv P Q))) as q; simpl in q.
    rewrite in_app_iff in q.
    rewrite in_snoc in q.
    autodimp q hyp; tcsp.
    rewrite q; auto. }

  { apply hyps.
    rewrite in_app_iff.
    rewrite in_snoc; tcsp. }
Qed.

Lemma RULE_equiv_left_sch_true :
  forall x y H J P Q R, Rule_true (RULE_equiv_left_sch x y H J P Q R).
Proof.
  introv.
  apply Rule_true_I_implies_Rule_true.
  apply RULE_equiv_left_sch_true_I.
Qed.



(**

  H |- P -> Q     H |- Q -> P
  ---------------------------
       H |- P <-> Q

 *)
Definition RULE_equiv_right_sch H P Q : Rule :=
    MkRULE
      [MkSeq H (KFimply P Q),  MkSeq H (KFimply Q P)]
      (MkSeq H (KFequiv P Q)).

Lemma RULE_equiv_right_sch_true_I :
  forall H P Q, Rule_true_I (RULE_equiv_right_sch H P Q).
Proof.
  introv subgoals hyps; simpl in *.
  dLin_hyp h.

  pose proof (h v) as q1; clear h; simpl in q1.
  unfold sequent_true_I_v in q1.
  autodimp q1 hyp; simpl in q1.

  pose proof (h0 v) as q2; clear h0; simpl in q2.
  unfold sequent_true_I_v in q2.
  autodimp q2 hyp; simpl in q2.

  split; sp.
Qed.

Lemma RULE_equiv_right_sch_true :
  forall H P Q, Rule_true (RULE_equiv_right_sch H P Q).
Proof.
  introv.
  apply Rule_true_I_implies_Rule_true.
  apply RULE_equiv_right_sch_true_I.
Qed.


(**

  H |- P     H |- Q
  -----------------
     H |- P /\ Q

 *)
Definition RULE_and_right_sch H P Q : Rule :=
    MkRULE
      [MkSeq H P, MkSeq H Q]
      (MkSeq H (KFand P Q)).

Lemma RULE_and_right_sch_true_I :
  forall H P Q, Rule_true_I (RULE_and_right_sch H P Q).
Proof.
  introv subgoals hyps; simpl in *.
  dLin_hyp h.

  pose proof (h v) as q1; clear h; simpl in q1.
  unfold sequent_true_I_v in q1.
  autodimp q1 hyp; simpl in q1.

  pose proof (h0 v) as q2; clear h0; simpl in q2.
  unfold sequent_true_I_v in q2.
  autodimp q2 hyp; simpl in q2.
Qed.

Lemma RULE_and_right_sch_true :
  forall H P Q, Rule_true (RULE_and_right_sch H P Q).
Proof.
  introv.
  apply Rule_true_I_implies_Rule_true.
  apply RULE_and_right_sch_true_I.
Qed.


(**

  Differential ghosts (left to right only) --- see Figure 3, Section 5.1

      [x'=f(x) & q(x)]p(x,x')
      ->
      [x'=f(x),y'=a(x)*y+b(x) & q(x)]p(x,x')

 *)
Definition DG_LR_axiom : Formula :=
  KFimply
    (KFbox
       (KPodeSystem
          (ODEsing varx (Fof1 funcf tvarx))
          (Pof1 predq tvarx)
       )
       (Pof2 predp tvarx tvarxp)
    )
    (KFbox
       (KPodeSystem
          (ODEprod
             (ODEsing varx (Fof1 funcf tvarx))
             (ODEsing vary (KTplus
                              (KTtimes (Fof1 funcfa tvarx) tvary)
                              (Fof1 funcfb tvarx)
                           )
             )
          )
          (Pof1 predq tvarx)
       )
       (Pof2 predp tvarx tvarxp)
    ).

Definition DG_LR_rule : rule := MkRule [] DG_LR_axiom.

Lemma DG_LR_axiom_sound : rule_true DG_LR_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv; simpl.
  introv h q; exrepnd; subst.

  unfold ode_footprint_diff in q0; simpl in q0.
  unfold ode_footprint, ode_footprint_diff in q1; simpl in q1.

  pose proof (h (fun (a : KAssignable) =>
                   if KAssignable_dec a assignyp
                   then v a
                   else if KAssignable_dec a assigny
                        then v a
                        else phi r a)) as q; clear h.
  simpl in q.
  repeat (dest_cases w).
  apply q; clear q.

  fold assignyp in *.
  fold assignxp in *.
  fold assigny in *.
  fold assignx in *.

  exists r (fun r (a : KAssignable) =>
              if KAssignable_dec a assignyp
              then v a
              else if KAssignable_dec a assigny
                   then v a
                   else phi r a).
  repeat (dest_cases w); GC.
  dands; auto.

  { introv i; simpl in i; apply not_or in i; repnd; GC.
    dest_cases w.
    pose proof (q0 x) as h; clear q0; simpl in h.
    autodimp h hyp.
    { intro xx; repndors; tcsp. }
    unfold upd_state in h.
    dest_cases w. }

  { introv i.
    simpl in *; repndors; subst; tcsp.
    repeat (dest_cases w; GC).
    pose proof (q3 zeta assignx) as h; simpl in h.
    autodimp h hyp.
    repeat (dest_cases w; GC).
    autorewrite with core in *; tcsp. }

  { introv; simpl in *; repndors; subst; tcsp.
    fold assignx in *.
    repeat (dest_cases w; GC).
    pose proof (q1 zeta) as h; repnd.
    dands; auto.
    introv i; simpl in i; repeat (apply not_or in i; repnd); GC.
    repeat (dest_cases w).
    apply h; simpl.
    intro j; repndors; subst; tcsp. }
Qed.


(**

  Simpler version of differential ghosts (left to right only) --- see Figure 3, Section 5.1

      [x'=f(x) & q(x)]p(x,x')
      ->
      [x'=f(x),y'=a(x) & q(x)]p(x,x')

 *)
Definition sp_DG_LR_axiom : Formula :=
  KFimply
    (KFbox
       (KPodeSystem
          (ODEsing varx (Fof1 funcf tvarx))
          (Pof1 predq tvarx)
       )
       (Pof2 predp tvarx tvarxp)
    )
    (KFbox
       (KPodeSystem
          (ODEprod
             (ODEsing varx (Fof1 funcf tvarx))
             (ODEsing vary (Fof1 funcfa tvarx))
          )
          (Pof1 predq tvarx)
       )
       (Pof2 predp tvarx tvarxp)
    ).

Definition sp_DG_LR_rule : rule := MkRule [] sp_DG_LR_axiom.

Lemma sp_DG_LR_axiom_sound : rule_true sp_DG_LR_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv; simpl.
  introv h q; exrepnd; subst.

  unfold ode_footprint_diff in q0; simpl in q0.
  unfold ode_footprint, ode_footprint_diff in q1; simpl in q1.

  pose proof (h (fun (a : KAssignable) =>
                   if KAssignable_dec a assignyp
                   then v a
                   else if KAssignable_dec a assigny
                        then v a
                        else phi r a)) as q; clear h.
  simpl in q.
  repeat (dest_cases w).
  apply q; clear q.

  fold assignyp in *.
  fold assignxp in *.
  fold assigny in *.
  fold assignx in *.

  exists r (fun r (a : KAssignable) =>
              if KAssignable_dec a assignyp
              then v a
              else if KAssignable_dec a assigny
                   then v a
                   else phi r a).
  repeat (dest_cases w); GC.
  dands; auto.

  { introv i; simpl in i; apply not_or in i; repnd; GC.
    dest_cases w.
    pose proof (q0 x) as h; clear q0; simpl in h.
    autodimp h hyp.
    { intro xx; repndors; tcsp. }
    unfold upd_state in h.
    dest_cases w. }

  { introv i.
    simpl in *; repndors; subst; tcsp.
    repeat (dest_cases w; GC).
    pose proof (q3 zeta assignx) as h; simpl in h.
    autodimp h hyp.
    repeat (dest_cases w; GC).
    autorewrite with core in *; tcsp. }

  { introv; simpl in *; repndors; subst; tcsp.
    fold assignx in *.
    repeat (dest_cases w; GC).
    pose proof (q1 zeta) as h; repnd.
    dands; auto.
    introv i; simpl in i; repeat (apply not_or in i; repnd); GC.
    repeat (dest_cases w).
    apply h; simpl.
    intro j; repndors; subst; tcsp. }
Qed.


(**

   p((x)') <-> p(x')

 *)
Definition pred_XP_axiom : Formula :=
  KFequiv
    (Pof1 predp (KTdifferential tvarx))
    (Pof1 predp tvarxp).

Definition pred_XP_rule : rule := MkRule [] pred_XP_axiom.

Lemma pred_XP_sound : rule_true pred_XP_rule.
Proof.
  introv imp; repeat introv; simpl in *; clear imp.
  autorewrite with core.
  match goal with
  | [ |- _ _ ?x <-> _ _ ?y ] => assert (x = y) as xx;[|rewrite xx;tcsp]
  end.
  f_equal.
  erewrite Derive_ext;[|introv;autorewrite with core;reflexivity].
  rewrite Derive_id.
  autorewrite with core; auto.
Qed.

(**

   C(p((x)')) <-> C(p(x'))

 *)
Definition quant_pred_XP_axiom : Formula :=
  KFequiv
    (qC (Pof1 predp (KTdifferential tvarx)))
    (qC (Pof1 predp tvarxp)).

Definition quant_pred_XP_rule : rule := MkRule [] quant_pred_XP_axiom.

Lemma quant_pred_XP_sound : rule_true quant_pred_XP_rule.
Proof.
  introv imp; repeat introv; simpl in *; clear imp.
  autorewrite with core.
  remember (I (SymbolQuantifier qsC)) as C; simpl in C.
  destruct C as [C ext].
  clear HeqC.
  apply ext; auto; introv.
  match goal with
  | [ |- _ _ ?x <-> _ _ ?y ] => assert (x = y) as xx;[|rewrite xx;tcsp]
  end.
  f_equal.
  erewrite Derive_ext;[|introv;autorewrite with core;reflexivity].
  rewrite Derive_id.
  autorewrite with core; auto.
Qed.


(**

   p((n)') <-> p(0)

 *)
Definition diff_real_axiom (r : R) : Formula :=
  KFequiv
    (Pof1 predp (KTdifferential (KTnumber (KTNreal r))))
    (Pof1 predp 0).

Definition diff_real_rule (r : R) : rule := MkRule [] (diff_real_axiom r).

Lemma diff_real_sound : forall r, rule_true (diff_real_rule r).
Proof.
  introv imp; repeat introv; simpl in *; clear imp; tcsp.
Qed.


(**

   p((n)') <-> p(0)

 *)
Definition diff_realn_axiom (r : nat) : Formula :=
  KFequiv
    (Pof1 predp (KTdifferential r))
    (Pof1 predp 0).

Definition diff_realn_rule (r : nat) : rule := MkRule [] (diff_realn_axiom r).

Lemma diff_realn_sound : forall r, rule_true (diff_realn_rule r).
Proof.
  introv imp; repeat introv; simpl in *; clear imp; tcsp.
Qed.


(**

  [x':=f]p(x') <-> p(f)

 *)
Definition assignmentp_axiom : Formula :=
  KFequiv
    (KFbox (KPassign assignxp tfuncf) (Pof1 predp tvarxp))
    (Pof1 predp tfuncf).

Definition assignmentp_rule : rule := MkRule [] assignmentp_axiom.

Definition assignmentp_axiom_sound : rule_true assignmentp_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv; simpl.
  split; intro h; exrepnd.

  {
    pose proof (h (upd_state
                     v
                     assignxp
                     (interp_fun_f
                        0
                        (I (SymbolFunction funcf 0))
                        (Vector.nil R)))) as q; clear h.
    unfold upd_state in *.
    dest_cases w.
    apply q.
    unfold differ_state_except; autorewrite with core; dands; auto.
    introv d; dest_cases w.
  }

  {
    introv d.
    destruct d as [d1 d2].
    rewrite d2; auto.
  }
Qed.

Definition in_atomic_ode a (ode : AtomicODE) : bool :=
  match ode with
  | ODEconst c => true
  | ODEsing ds theta => if KAssignable_dec a ds then true else false
  end.

Fixpoint in_ode a (ode : ODE) : bool :=
  match ode with
  | ODEatomic c => in_atomic_ode a c
  | ODEprod l r => in_ode a l || in_ode a r
  end.

Lemma in_ode_false_implies_dynamic_semantics_ode_fun_0 :
  forall v ode I (phi : R -> state) r,
    in_ode v ode = false
    -> dynamic_semantics_ode_fun I ode (phi r) (KD v) = R0.
Proof.
  induction ode; introv i; simpl in *.

  { destruct child; simpl in *; ginv.
    repeat (dest_cases w). }

  { apply orb_false_iff in i; repnd.
    rewrite IHode1, IHode2; autorewrite with core; auto. }
Qed.


(**

  Differential effect --- see Figure 3, Section 5.1

  [x'=t,ODE & Q]P <-> [x'=t,ODE & Q][x':=t]P

 *)
Definition differential_effect_sch_axiom
           (x : KVariable)
           (t : Term)
           (ode : ODE)
           (Q P : Formula) : Formula :=
  KFequiv
    (KFbox (KPodeSystem (ODEprod (ODEsing x t) ode) Q) P)
    (KFbox
       (KPodeSystem (ODEprod (ODEsing x t) ode) Q)
       (KFbox (KPassign (KD x) t) P)
    ).

Definition differential_effect_sch_rule x t ode Q P : rule :=
  MkRule [] (differential_effect_sch_axiom x t ode Q P).

Lemma differential_effect_sch_axiom_sound :
  forall (x : KVariable) t ode Q P,
    in_ode x ode = false
    -> rule_true (differential_effect_sch_rule x t ode Q P).
Proof.
  introv niode imp; simpl in *; clear imp.
  repeat introv; simpl.

  split; intro h; introv cond; introv.

  {
    introv diff.
    exrepnd; subst.
    destruct diff as [diff1 diff2].

    pose proof (cond3 (mk_preal_upto r r (Rle_refl r)) x) as z; simpl in z.
    dest_cases w;[].
    autodimp z hyp; repnd.
    rewrite in_ode_false_implies_dynamic_semantics_ode_fun_0 in z; auto.
    autorewrite with core in *.

    assert (w0 = phi r) as xx.
    { apply functional_extensionality; introv.
      destruct (KAssignable_dec x0 (KD x)) as [d|d]; subst.
      { rewrite z; auto. }
      { symmetry; auto. }
    }
    subst; GC.

    apply h.
    exists r phi; simpl.
    dands; auto.
  }

  {
    exrepnd; subst.

    apply (h (phi r)).
    { exists r phi; dands; auto. }

    split; auto.
    pose proof (cond3 (mk_preal_upto r r (Rle_refl r)) x) as z; simpl in z.
    dest_cases w;[].
    rewrite in_ode_false_implies_dynamic_semantics_ode_fun_0 in z; auto.
    autorewrite with core in *.
    autodimp z hyp; tcsp.
  }
Qed.


(**

       H, J |- P
  --------------------
  H , x : ~ P , J |- Q

 *)
Definition RULE_not_left_sch x H J P Q : Rule :=
    MkRULE
      [MkSeq (addHyps H J) P]
      (MkSeq (addHyps (addHyp H (MkHyp x (KFnot P))) J) Q).

Lemma RULE_not_left_sch_true_I :
  forall x H J P Q, Rule_true_I (RULE_not_left_sch x H J P Q).
Proof.
  introv subgoals hyps; simpl in *.
  dLin_hyp h.

  pose proof (hyps (MkHyp x (KFnot P))) as hor; simpl in hor.
  rewrite in_app_iff in hor; rewrite in_snoc in hor; simpl in hor.
  autodimp hor hyp.
  destruct hor; apply h; introv i; simpl in i.
  apply in_app_iff in i; repndors.

  { apply hyps.
    rewrite in_app_iff.
    rewrite in_snoc; tcsp. }

  { apply hyps.
    rewrite in_app_iff.
    rewrite in_snoc; tcsp. }
Qed.

Lemma RULE_not_left_sch_true :
  forall x H J P Q, Rule_true (RULE_not_left_sch x H J P Q).
Proof.
  introv.
  apply Rule_true_I_implies_Rule_true.
  apply RULE_not_left_sch_true_I.
Qed.



(**

  H , x : P |- False
  ------------------
      H |- ~ P

 *)
Definition RULE_not_right_sch x H P : Rule :=
    MkRULE
      [MkSeq (addHyp H (MkHyp x P)) KFfalse]
      (MkSeq H (KFnot P)).

Lemma RULE_not_right_sch_true_I :
  forall x H P, Rule_true_I (RULE_not_right_sch x H P).
Proof.
  introv subgoals hyps; simpl in *.
  dLin_hyp h.
  intro d.
  pose proof (h v) as q; simpl in q.
  unfold sequent_true_I_v in q; autodimp q hyp; simpl.
  introv i; apply in_snoc in i; repndors; subst; tcsp.
Qed.

Lemma RULE_not_right_sch_true :
  forall x H P, Rule_true (RULE_not_right_sch x H P).
Proof.
  introv.
  apply Rule_true_I_implies_Rule_true.
  apply RULE_not_right_sch_true_I.
Qed.


Inductive step : Type :=
(*
           ∅
   ---------------- (assumption x)
   H, x : A, J |- A
 *)
| step_assumption  (x : HName)                                : step

(*
       H, J |- B
   ---------------- (clear x)
   H, x : A, J |- B
 *)
| step_clear       (x : HName)                                : step

(*
   H, x : A |- B
   ------------- (imply_right x)
    H |- A -> B
 *)
| step_imply_right (x : HName)                                : step

(*
   H, J |- A      H, x : B, J |- C
   ------------------------------- (imply_left x)
       H, x : A -> B, J |- C
 *)
| step_imply_left  (x : HName)                                : step

(*
   H, x : A, J |- C      H, x : B, J |- C
   -------------------------------------- (or_left x)
             H, x : A \/ B, J |- C
 *)
| step_or_left     (x : HName)                                : step

(*
   H, x : A, y : B, J |- C
   ----------------------- (and_left x y)
    H, x : A /\ B, J |- C
 *)
| step_and_left    (x y : HName)                              : step

(*
   H, x : A -> B, y : B -> A, J |- C
   ----------------------- (equiv_left x y)
    H, x : A <-> B, J |- C
 *)
| step_equiv_left  (x y : HName)                              : step

(*
   H |- A -> B      H |- B -> A
   ---------------------------- (equiv_right)
          H |- A <-> B
 *)
| step_equiv_right                                            : step

(*
   H |- A      H |- B
   ------------------ (and_right)
      H |- A /\ B
 *)
| step_and_right                                              : step

(*
     H |- A
   ----------- (or_right1)
   H |- A \/ B
 *)
| step_or_right1                                              : step

(*
     H |- B
   ----------- (or_right2)
   H |- A \/ B
 *)
| step_or_right2                                              : step

(*
          H, J |- A
   --------------------- (not_left x)
   H, x : not(A), J |- C
 *)
| step_not_left    (x : HName)                                : step

(*
   H, x : A |- False
   ----------------- (not_right x)
      H |- not(A)
 *)
| step_not_right   (x : HName)                                : step

(*
   H, J, x : A, y : B, K |- C
   -------------------------- (move_hyp)
   H, x : A, J, y : B, K |- C
 *)
| step_move_hyp    (x y : HName)                              : step

(*
   H |- f      H, x : f |- A
   ------------------------- (cut x f)
             H |- A
 *)
| step_cut         (x : HName) (f : Formula)                  : step

(*
   H, x : sw(sub(DI_ge_axiom)) |- A
   -------------------------------- (DIge x sub sw)
               H |- A
 *)
| step_DIge        (x : HName) (sub : US) (sw : SW)           : step

(*
   H, x : sw(sub(DI_ge_diff_axiom)) |- A
   ------------------------------------- (DIgeD x sub sw)
                H |- A
 *)
| step_DIgeD       (x : HName) (sub : US) (sw : SW)           : step

(*
   H, x : sw(sub(ode_comm)) |- A
   ----------------------------- (OC x sub sw)
            H |- A
 *)
| step_OC          (x : HName) (sub : US) (sw : SW)           : step

(*
   H, x : sw(sub(DG_LR_axiom)) |- A
   -------------------------------- (DGhostLR x sub sw)
              H |- A
 *)
| step_DGhostLR    (x : HName) (sub : US) (sw : SW)           : step

(*
   H, x : sw(sub(sp_DG_LR_axiom)) |- A
   ----------------------------------- (spDGhostLR x sub sw)
                H |- A
 *)
| step_spDGhostLR  (x : HName) (sub : US) (sw : SW)           : step

(*
   H, x : sw(differential_identity_axiom) |- A
   ------------------------------------------- (XP x sw)
                    H |- A
 *)
| step_XP          (x : HName) (sw : SW)                      : step

(*
   H, x : sw(sub(pred_XP_axiom)) |- A
   ---------------------------------- (PXP x sub sw)
               H |- A
 *)
| step_PXP         (x : HName) (sub : US) (sw : SW)           : step

(*
   H, x : sw(sub(quant_pred_XP_axiom)) |- A
   ---------------------------------------- (QPXP x sub sw)
                  H |- A
 *)
| step_QPXP        (x : HName) (sub : US) (sw : SW)           : step

(*
   H, x : sw(sub(differential_effect_axiom)) |- A
   ---------------------------------------------- (DE x sub sw)
                      H |- A
 *)
| step_DE          (x : HName) (sub : US) (sw : SW)           : step

(*
   H, x : sw(sub(differential_effect_sch_axiom v t ode Q P)) |- A
   -------------------------------------------------------------- (DEsch x v t ode Q P)
                              H |- A
 *)
| step_DEsch       (x : HName) (v : Var) (t : Term) (ode : ODE) (Q P : Formula) : step

(*
   H, x : sub(V_axiom) |- A
   ------------------------ (V x sub)
           H |- A
 *)
| step_V           (x : HName) (sub : US)                     : step

(*
   H, x : sub(diff_real_axiom r) |- A
   ---------------------------------- (DR x sub sw r)
              H |- A
 *)
| step_DR          (x : HName) (sub : US) (sw : SW) (r : R)   : step

(*
   H, x : sub(diff_realn_axiom r) |- A
   ----------------------------------- (DRN x sub sw r)
                H |- A
 *)
| step_DRN         (x : HName) (sub : US) (sw : SW) (r : nat) : step

(*
   ∅ |- sub(Q)      H, x : sub([a]Q) |- A
   --------------------------------------- (G x sub)
                    H |- A
 *)
| step_G           (x : HName) (sub : US)                     : step

(*
   H, x : sw(sub(assignment_axiom)) |- A
   ------------------------------------- (assign x sub sw)
                H |- A
 *)
| step_assign      (x : HName) (sub : US) (sw : SW)           : step

(*
   H, x : sw(sub(assignmentp_axiom)) |- A
   -------------------------------------- (assignp x sub sw)
                H |- A
 *)
| step_assignp     (x : HName) (sub : US) (sw : SW)           : step

(*
   H, x : sub(K_quant_axiom) |- A
   ------------------------------ (K x sub)
                H |- A
 *)
| step_K           (x : HName) (sub : US)                     : step

(*
   ∅ |- P <-> Q      H, x : [qsC -> C](qC P <> qC Q) |- A
   ------------------------------------------------------ (CE x P Q C)
                H |- A
 *)
| step_CE          (x : HName) (P Q C : Formula)              : step

(*
   H |- t > u
   ---------- (GE2GT)
   H |- t ≥ u
 *)
| step_GE2GT                                                  : step

(*
             ∅
   -------------------- (false_left x)
   H, x : False, J |- C
 *)
| step_false_left (x : HName)                                 : step

(*
(*
     H |- p(y)
   ------------- (all_right y)
   H |- ∀x.p(x)
 *)
| step_all_right (y : KVariable)                              : step
*)

(*
   sw(H |- A)
   ---------- (swap sw)
    H |- A
 *)
| step_swap        (sw : swapping)                            : step

| step_focus       (n : nat)                                  : step.
(*| step_US          (sub : US)                : step*)

Ltac dstep h c :=
  destruct h;
  [ Case_aux c "Assumption"
  | Case_aux c "Clear"
  | Case_aux c "ImplyRight"
  | Case_aux c "ImplyLeft"
  | Case_aux c "OrLeft"
  | Case_aux c "AndLeft"
  | Case_aux c "EquivLeft"
  | Case_aux c "EquivRight"
  | Case_aux c "AndRight"
  | Case_aux c "OrRight1"
  | Case_aux c "OrRight2"
  | Case_aux c "NotLeft"
  | Case_aux c "NotRight"
  | Case_aux c "MoveHyp"
  | Case_aux c "Cut"
  | Case_aux c "DIge"
  | Case_aux c "DIgeD"
  | Case_aux c "OdeComm"
  | Case_aux c "DGhostLR"
  | Case_aux c "spDGhostLR"
  | Case_aux c "XP"
  | Case_aux c "PXP"
  | Case_aux c "QPXP"
  | Case_aux c "DE"
  | Case_aux c "DEsch"
  | Case_aux c "V"
  | Case_aux c "DR"
  | Case_aux c "DRN"
  | Case_aux c "G"
  | Case_aux c "Assign"
  | Case_aux c "Assignp"
  | Case_aux c "K"
  | Case_aux c "CE"
(*  | Case_aux c "US"*)
  | Case_aux c "GE2GT"
  | Case_aux c "FalseLeft"
(*  | Case_aux c "AllRight"*)
  | Case_aux c "Swap"
  | Case_aux c "Focus"
  ].

Definition script := list step.

Record DecompH :=
  MkDecompH
    {
      decomph_pre : hypotheses;
      decomph_F   : Formula;
      decomph_suf : hypotheses
    }.

Definition preDecompH (h : hypothesis) (d : DecompH) : DecompH :=
  match d with
  | MkDecompH H f J => MkDecompH (h :: H) f J
  end.

Fixpoint find_hyp (H : hypotheses) (x : HName) : option DecompH :=
  match H with
  | [] => None
  | h :: H =>
    match h with
    | MkHyp n f =>
      if HName_dec n x
      then Some (MkDecompH [] f H)
      else
        match find_hyp H x with
        | Some d => Some (preDecompH h d)
        | None => None
        end
    end
  end.

Fixpoint focus_state (ps : proof_state) (n : nat) : option (sequent * list sequent)%type :=
  match n, ps with
  | _, [] => None
  | 0, seq :: seqs => Some (seq, seqs)
  | S n, seq :: seqs =>
    match focus_state seqs n with
    | Some (x, xs) => Some (x, seq :: xs)
    | None => None
    end
  end.

Fixpoint SW_formula (sw : SW) (f : Formula) : Formula :=
  match sw with
  | [] => f
  | x :: xs => swap_formula x (SW_formula xs f)
  end.

Definition G_quant_rule : rule :=
  MkRule [quantQ] (KFbox pconsta quantQ).

Definition G_quant_sound : rule_true G_quant_rule.
Proof.
  introv imp dsf; simpl in *.
  dLin_hyp q.
  apply q.
Qed.

Definition G_quant_locally_sound : rule_locally_sound G_quant_rule.
Proof.
  introv imp dsf; simpl in *.
  dLin_hyp q.
  apply q.
Qed.

Definition G_quant_sch_rule P F : rule :=
  MkRule [F] (KFbox P F).

Definition G_quant_sch_sound P Q : rule_true (G_quant_sch_rule P Q).
Proof.
  introv imp dsf; simpl in *.
  dLin_hyp q.
  apply q.
Qed.

Definition G_quant_sch_locally_sound P Q : rule_locally_sound (G_quant_sch_rule P Q).
Proof.
  introv imp dsf; simpl in *.
  dLin_hyp q.
  apply q.
Qed.

(**

  K axiom (using quantifiers) --- see Figure 2, Section 4

  [a](P -> Q) -> ([a]P -> [a]Q)

 *)
Definition K_quant_axiom : Formula :=
  KFimply
    (KFbox pconsta (KFimply quantP quantQ))
    (KFimply
       (KFbox pconsta quantP)
       (KFbox pconsta quantQ)).

Definition K_quant_rule : rule := MkRule [] K_quant_axiom.

Definition K_quant_axiom_sound : rule_true K_quant_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv; simpl.
  introv h1 h2 h3; tcsp.
Qed.


Fixpoint free_vars_hyp (h : hypothesis) : EAssignables :=
  free_vars_formula (hyp_form h).

Fixpoint free_vars_hyps (H : hypotheses) : EAssignables :=
  match H with
  | [] => FCS_finite []
  | h :: hs => EAssignables_app (free_vars_hyp h) (free_vars_hyps hs)
  end.


Definition apply_step (ps : proof_state) (s : step) : proof_state :=
  match s with
  | step_assumption x =>
    match ps with
    | MkSeq H C :: seqs =>
      match find_hyp H x with
      | Some (MkDecompH G F J) => if formula_dec F C then seqs else ps
      | _ => ps
      end
    | _ => ps
    end

  | step_clear x =>
    match ps with
    | MkSeq H C :: seqs =>
      match find_hyp H x with
      | Some (MkDecompH G F J) => MkSeq (addHyps G J) C :: seqs
      | _ => ps
      end
    | _ => ps
    end

  | step_imply_right x =>
    match ps with
    | MkSeq H C :: seqs =>
      match C with
      | KFimply P Q => (MkSeq (addHyp H (MkHyp x P)) Q) :: seqs
      | _ => ps
      end
    | _ => ps
    end

  | step_imply_left x =>
    match ps with
    | MkSeq H C :: seqs =>
      match find_hyp H x with
      | Some (MkDecompH G (KFimply P Q) J) =>
        MkSeq (addHyps G J) P
              :: MkSeq (addHyps (addHyp G (MkHyp x Q)) J) C
              :: seqs
      | _ => ps
      end
    | _ => ps
    end

  | step_or_left x =>
    match ps with
    | MkSeq H C :: seqs =>
      match find_hyp H x with
      | Some (MkDecompH G (KFor P Q) J) =>
        MkSeq (addHyps (addHyp G (MkHyp x P)) J) C
              :: MkSeq (addHyps (addHyp G (MkHyp x Q)) J) C
              :: seqs
      | _ => ps
      end
    | _ => ps
    end

  | step_and_left x y =>
    match ps with
    | MkSeq H C :: seqs =>
      match find_hyp H x with
      | Some (MkDecompH G (KFand P Q) J) =>
        MkSeq (addHyps (addHyp (addHyp G (MkHyp x P)) (MkHyp y Q)) J) C :: seqs
      | _ => ps
      end
    | _ => ps
    end

  | step_equiv_left x y =>
    match ps with
    | MkSeq H C :: seqs =>
      match find_hyp H x with
      | Some (MkDecompH G (KFequiv P Q) J) =>
        MkSeq (addHyps (addHyp (addHyp G (MkHyp x (KFimply P Q))) (MkHyp y (KFimply Q P))) J) C :: seqs
      | _ => ps
      end
    | _ => ps
    end

  | step_equiv_right =>
    match ps with
    | MkSeq H (KFequiv P Q) :: seqs =>
      MkSeq H (KFimply P Q) :: MkSeq H (KFimply Q P) :: seqs
    | _ => ps
    end

  | step_and_right =>
    match ps with
    | MkSeq H (KFand P Q) :: seqs => MkSeq H P :: MkSeq H Q :: seqs
    | _ => ps
    end

  | step_or_right1 =>
    match ps with
    | MkSeq H (KFor P Q) :: seqs => MkSeq H P :: seqs
    | _ => ps
    end

  | step_or_right2 =>
    match ps with
    | MkSeq H (KFor P Q) :: seqs => MkSeq H Q :: seqs
    | _ => ps
    end

  | step_not_left x =>
    match ps with
    | MkSeq H C :: seqs =>
      match find_hyp H x with
      | Some (MkDecompH G (KFnot P) J) => MkSeq (addHyps G J) P :: seqs
      | _ => ps
      end
    | _ => ps
    end

  | step_not_right x =>
    match ps with
    | MkSeq H (KFnot P) :: seqs => MkSeq (addHyp H (MkHyp x P)) KFfalse :: seqs
    | _ => ps
    end

  | step_move_hyp x y =>
    match ps with
    | MkSeq H C :: seqs =>
      match find_hyp H x with
      | Some (MkDecompH G Fx J) =>
        match find_hyp J y with
        | Some (MkDecompH W Fy X) =>
          MkSeq (addHyps G (addHyps (addHyp (addHyp W (MkHyp y Fy)) (MkHyp x Fx)) X)) C :: seqs
        | _ => ps
        end
      | _ => ps
      end
    | _ => ps
    end

  | step_cut x f =>
    match ps with
    | MkSeq H C :: seqs => MkSeq H f :: MkSeq (addHyp H (MkHyp x f)) C :: seqs
    | _ => ps
    end

  | step_DIge x sub sw =>
    match ps with
    | MkSeq H C :: seqs =>
      MkSeq (addHyp H (MkHyp x (SW_formula sw (US_formula_otrue DI_ge_axiom sub)))) C :: seqs
    | _ => ps
    end

  | step_DIgeD x sub sw =>
    match ps with
    | MkSeq H C :: seqs =>
      MkSeq (addHyp H (MkHyp x (SW_formula sw (US_formula_otrue DI_ge_diff_axiom sub)))) C :: seqs
    | _ => ps
    end

  | step_OC x sub sw =>
    match ps with
    | MkSeq H C :: seqs =>
      MkSeq (addHyp H (MkHyp x (SW_formula sw (US_formula_otrue ode_comm sub)))) C :: seqs
    | _ => ps
    end

  | step_DGhostLR x sub sw =>
    match ps with
    | MkSeq H C :: seqs =>
      MkSeq (addHyp H (MkHyp x (SW_formula sw (US_formula_otrue DG_LR_axiom sub)))) C :: seqs
    | _ => ps
    end

  | step_spDGhostLR x sub sw =>
    match ps with
    | MkSeq H C :: seqs =>
      MkSeq (addHyp H (MkHyp x (SW_formula sw (US_formula_otrue sp_DG_LR_axiom sub)))) C :: seqs
    | _ => ps
    end

  | step_XP x sw =>
    match ps with
    | MkSeq H C :: seqs =>
      MkSeq (addHyp H (MkHyp x (SW_formula sw differential_identity_axiom))) C :: seqs
    | _ => ps
    end

  | step_PXP x sub sw =>
    match ps with
    | MkSeq H C :: seqs =>
      MkSeq (addHyp H (MkHyp x (SW_formula sw (US_formula_otrue pred_XP_axiom sub)))) C :: seqs
    | _ => ps
    end

  | step_QPXP x sub sw =>
    match ps with
    | MkSeq H C :: seqs =>
      MkSeq (addHyp H (MkHyp x (SW_formula sw (US_formula_otrue quant_pred_XP_axiom sub)))) C :: seqs
    | _ => ps
    end

  | step_DE x sub sw =>
    match ps with
    | MkSeq H C :: seqs =>
      MkSeq (addHyp H (MkHyp x (SW_formula sw (US_formula_otrue differential_effect_axiom sub)))) C :: seqs
    | _ => ps
    end

  | step_DEsch x v f ode Q P =>
    if in_ode v ode
    then ps
    else
      match ps with
      | MkSeq H C :: seqs =>
        MkSeq (addHyp H (MkHyp x (differential_effect_sch_axiom v f ode Q P))) C :: seqs
      | _ => ps
      end

  | step_V x sub =>
    match ps with
    | MkSeq H C :: seqs =>
      MkSeq (addHyp H (MkHyp x (US_formula_otrue V_axiom sub))) C :: seqs
    | _ => ps
    end

  | step_DR x sub sw r =>
    match ps with
    | MkSeq H C :: seqs =>
      MkSeq (addHyp H (MkHyp x (SW_formula sw (US_formula_otrue (diff_real_axiom r) sub)))) C :: seqs
    | _ => ps
    end

  | step_DRN x sub sw r =>
    match ps with
    | MkSeq H C :: seqs =>
      MkSeq (addHyp H (MkHyp x (SW_formula sw (US_formula_otrue (diff_realn_axiom r) sub)))) C :: seqs
    | _ => ps
    end

  | step_G x sub =>
    match ps with
    | MkSeq H C :: seqs =>
      (MkSeq emHyps (US_formula_otrue quantQ sub))
        :: MkSeq (addHyp H (MkHyp x (US_formula_otrue (KFbox pconsta quantQ) sub))) C
        :: seqs
    | _ => ps
    end

  | step_assign x sub sw =>
    match ps with
    | MkSeq H C :: seqs =>
      MkSeq (addHyp H (MkHyp x (SW_formula sw (US_formula_otrue assignment_axiom sub)))) C :: seqs
    | _ => ps
    end

  | step_assignp x sub sw =>
    match ps with
    | MkSeq H C :: seqs =>
      MkSeq (addHyp H (MkHyp x (SW_formula sw (US_formula_otrue assignmentp_axiom sub)))) C :: seqs
    | _ => ps
    end

  | step_K x sub =>
    match ps with
    | MkSeq H C :: seqs =>
      MkSeq (addHyp H (MkHyp x (US_formula_otrue K_quant_axiom sub))) C :: seqs
    | _ => ps
    end

  | step_CE x P Q C =>
    match ps with
    | MkSeq H F :: seqs =>
      (MkSeq emHyps (KFequiv P Q))
        :: (MkSeq (addHyp H (MkHyp x (US_formula_otrue (KFequiv (qC P) (qC Q)) [USE_quant qsC C]))) F)
        :: seqs
    | _ => ps
    end

      (*
  | step_US sub =>
    match ps with
    | seq :: seqs => US_sequent_false sub seq :: seqs
    | _ => ps
    end
*)

  | step_GE2GT =>
    match ps with
    | MkSeq H C :: seqs =>
      match C with
      | KFgreaterEqual P Q => MkSeq H (KFgreater P Q) :: seqs
      | _ => ps
      end
    | _ => ps
    end

  | step_false_left x =>
    match ps with
    | MkSeq H C :: seqs =>
      match find_hyp H x with
      | Some (MkDecompH _ KFfalse _) => seqs
      | _ => ps
      end
    | _ => ps
    end

(*
  | step_all_right y =>
    match ps with
    | MkSeq H C :: seqs =>
      match C with
      | KFforallVars [x] P =>
        if in_eassignables y (free_vars_hyps H)
        then ps
        else (MkSeq H (swap_formula (MkSwapping x y) P)) :: seqs
      | _ => ps
      end
    | _ => ps
    end
*)

  | step_swap sw =>
    match ps with
    | seq :: seqs => swap_sequent sw seq :: seqs
    | _ => ps
    end

  | step_focus n =>
    match focus_state ps n with
    | Some (seq, seqs) => seq :: seqs
    | None => ps
    end
  end.

Fixpoint apply_script (ps : proof_state) (ss : script) : proof_state :=
  match ss with
  | [] => ps
  | step :: steps => apply_script (apply_step ps step) steps
  end.

Lemma find_hyp_some_implies :
  forall H x G f J,
    find_hyp H x = Some (MkDecompH G f J)
    -> H = addHyps (addHyp G (MkHyp x f)) J.
Proof.
  induction H; introv fh; simpl in *; ginv.
  destruct a as [n F].
  dest_cases w.
  remember (find_hyp H x) as fh2.
  destruct fh2; simpl in *; ginv; symmetry in Heqfh2; ginv.
  inversion fh as [e]; clear fh.
  destruct d; simpl in *.
  apply IHlist in Heqfh2; subst; ginv; clear IHlist; simpl; auto.
Qed.

Lemma in_focus_state_some :
  forall n ps seq seqs s,
    focus_state ps n = Some (seq, seqs)
    -> In s ps
    -> (s = seq \/ In s seqs).
Proof.
  induction n; introv fs i; destruct ps; simpl in *; tcsp; ginv; repndors; subst; tcsp.

  { remember (focus_state ps n) as fs2; symmetry in Heqfs2; destruct fs2; tcsp.
    destruct p as [seq2 seqs2]; ginv; simpl; tcsp. }

  { remember (focus_state ps n) as fs2; symmetry in Heqfs2; destruct fs2; tcsp.
    destruct p as [seq2 seqs2]; ginv; simpl; tcsp.
    apply (IHn _ seq seqs2 s) in Heqfs2; tcsp. }
Qed.

(*
Lemma sequent_true_US_sequent_false_implies :
  forall sub seq,
    sequent_true (US_sequent_false sub seq)
    -> sequent_true seq.
Proof.
  introv i j.
  destruct seq as [H C]; simpl in *.
  unfold US_sequent_false in i; simpl in i.
  pose proof (i (adjoint_interpretation sub I v) v) as q.
  unfold sequent_true_I_v in q; simpl in q; autodimp q hyp.

  { introv k.
    destruct h as [n F]; simpl in *.
    unfold US_hyps_true in k; apply in_map_iff in k; exrepnd; simpl in *.
    apply j in k0.
    destruct x as [n1 F1]; simpl in *.
    unfold US_hyp_true in k1; simpl in k1; ginv.
    unfold uniform_substitution_formula_opt_true.
    remember (uniform_substitution_formula F1 sub) as usf;
      symmetry in Hequsf; destruct usf; simpl; tcsp.

    pose proof (us_lemma_formula F1 sub I v) as q.
    unfold on_uniform_substitution_formula in q.
    rewrite Hequsf in q.

Qed.
*)

Lemma sequent_true_swap_sequent_implies :
  forall sw s,
    sequent_true (swap_sequent sw s)
    -> sequent_true s.
Proof.
  introv st i.
  destruct s as [H C]; simpl in *.
  pose proof (st (swap_interp sw I) (swap_state sw v)) as q; clear st; simpl in q.
  unfold sequent_true_I_v in q; autodimp q hyp.

  { introv j; simpl in *.
    unfold swap_hyps in j; apply in_map_iff in j; exrepnd; subst.
    apply i in j0.
    destruct x as [n F]; simpl in *.
    apply swap_dynamic_semantics_formula.
    rewrite swap_state_twice.
    apply (ext_dynamic_semantics_formula _ _ I _ v); auto. }

  { simpl in *.
    apply (swap_dynamic_semantics_formula _ _ (swap_interp sw I)) in q.
    rewrite swap_state_twice in q.
    apply (ext_dynamic_semantics_formula _ _ I _ v) in q; auto. }
Qed.

Lemma sequent_true_assumption :
  forall x G C J,
    sequent_true (((G • (x : C)) ⊕ J) ⊢ C).
Proof.
  introv i; simpl in *.
  apply (i (MkHyp x C)).
  apply in_app_iff; rewrite in_snoc; simpl; tcsp.
Qed.

Lemma sequent_true_weaken :
  forall x G A J C,
    sequent_true ((G ⊕ J) ⊢ C)
    -> sequent_true (((G • (x : A)) ⊕ J) ⊢ C).
Proof.
  introv st i; simpl in *.
  apply st; introv j.
  apply in_app_iff in j; apply i.
  apply in_app_iff; rewrite in_snoc; simpl; tcsp.
Qed.

Lemma SW_formula_KFtrue :
  forall sw, SW_formula sw KFtrue = KFtrue.
Proof.
  induction sw; simpl; auto.
  rewrite IHsw; simpl; auto.
Qed.
Hint Rewrite SW_formula_KFtrue : core.

Fixpoint SW_state (sw : SW) (s : state) : state :=
  match sw with
  | [] => s
  | x :: xs => swap_state x (SW_state xs s)
  end.

Fixpoint SW_interp (sw : SW) (i : interpretation) : interpretation :=
  match sw with
  | [] => i
  | x :: xs => swap_interp x (SW_interp xs i)
  end.

(*
Lemma swap_swap :
  forall (sw1 sw2 : swapping) (v : Var),
    swap sw1 (swap sw2 v)
    = swap sw2 (swap sw1 v).
Proof.
  introv.
  unfold swap.
  destruct sw1 as [a b].
  destruct sw2 as [c d].
  simpl.
  repeat (dest_cases w; try subst; GC; auto).

Qed.

Lemma swap_assgn_swap :
  forall (sw1 sw2 : swapping) (v : state),
    swap_state sw1 (swap_state sw2 v)
    = swap_state sw2 (swap_state sw1 v).
Proof.
  introv.
  apply functional_extensionality; introv.
  unfold swap_state.
Qed.

Lemma swap_state_swap :
  forall (sw1 sw2 : swapping) (v : state),
    swap_state sw1 (swap_state sw2 v)
    = swap_state sw2 (swap_state sw1 v).
Proof.
  introv.
  apply functional_extensionality; introv.
  unfold swap_state.
Qed.

Lemma swap_state_SW_state :
  forall sw a v,
    swap_state a (SW_state sw v)
    = SW_state sw (swap_state a v).
Proof.
  induction sw; simpl; introv; auto.
  rewrite IHsw.
  SearchAbout swap_state.
Qed.
 *)

Lemma swap_dynamic_semantics_formula2 :
  forall (f : Formula) (sw : swapping) (I : interpretation) (v : state),
    dynamic_semantics_formula I f v
    <->
    dynamic_semantics_formula (swap_interp sw I) (swap_formula sw f) (swap_state sw v).
Proof.
  introv.
  rewrite swap_dynamic_semantics_formula.
  apply ext_dynamic_semantics_formula; auto; introv.
  { rewrite swap_state_twice; auto. }
  { apply ext_interpretations_at_sym.
    apply swap_interp_twice. }
Qed.

Lemma implies_SW_dynamic_semantics_formula :
  forall (sw : SW) (f : Formula) (I : interpretation) (v : state),
    (forall I v, dynamic_semantics_formula I f v)
    -> dynamic_semantics_formula I (SW_formula sw f) v.
Proof.
  induction sw; simpl; introv imp; tcsp.
  rewrite swap_dynamic_semantics_formula.
  apply IHsw; auto.
Qed.

Lemma sound_proof_state_cons :
  forall p ps,
    sound_proof_state (p :: ps)
    <-> sequent_true p /\ sound_proof_state ps.
Proof.
  introv; split; intro h; repnd; dands; try (apply h; simpl; auto).
  { introv i; apply h; simpl; auto. }
  { introv i; simpl in i; repndors; subst; auto. }
Qed.

Lemma cut_valid_formula_in_sequent :
  forall H x F C,
    sequent_true ((H • (x : F)) ⊢ C)
    -> Df_formula_valid F
    -> sequent_true (H ⊢ C).
Proof.
  introv st fv i; simpl in *.
  apply st; clear st; introv j; simpl in *.
  apply in_snoc in j; repndors; subst; simpl; auto.
  apply fv.
Qed.

Lemma cut_formula_in_sequent :
  forall H x F C,
    sequent_true ((H • (x : F)) ⊢ C)
    -> sequent_true (H ⊢ F)
    -> sequent_true (H ⊢ C).
Proof.
  introv st fv i; simpl in *.
  apply st; clear st; introv j; simpl in *.
  apply in_snoc in j; repndors; subst; simpl; auto.
  apply fv; simpl; auto.
Qed.

Definition SW_rule (f : Formula) (sw : SW) : rule :=
  MkRule
    [f]
    (SW_formula sw f).

Lemma SW_rule_true :
  forall (sw : SW) (f : Formula), rule_true (SW_rule f sw).
Proof.
  induction sw; simpl; introv imp; tcsp; simpl in *.
  { apply imp; simpl; auto. }
  { apply swap_rule_true; auto.
    introv i; simpl in i; repndors; subst; tcsp.
    apply IHsw; simpl; auto. }
Qed.

Definition CE_rule_sch P Q : rule :=
  MkRule
    [KFequiv P Q]
    (KFequiv (qC P) (qC Q)).

Lemma CE_rule_sch_true P Q : rule_true (CE_rule_sch P Q).
Proof.
  introv imp; simpl in *.
  dLin_hyp h.
  repeat introv; simpl.
  remember (I (SymbolQuantifier qsC)) as IC; simpl in IC.
  destruct IC as [ic extic]; clear HeqIC; simpl.
  apply extic; auto; introv.
  apply (h I s).
Qed.

Definition CE_Rule_sch P Q : Rule :=
  MkRULE
    [MkSeq emHyps (KFequiv P Q)]
    (MkSeq emHyps (KFequiv (qC P) (qC Q))).

Lemma CE_Rule_sch_true P Q : Rule_true (CE_Rule_sch P Q).
Proof.
  introv imp; simpl in *.
  dLin_hyp h.
  introv imp; simpl in *.
  remember (I (SymbolQuantifier qsC)) as IC; simpl in IC.
  destruct IC as [ic extic]; clear HeqIC; simpl.
  apply extic; auto; introv.
  apply (h I s); simpl; tcsp.
Qed.

Lemma free_vars_sub_restrict_formula_quantQ :
  forall sub, free_vars_sub_restrict_formula sub quantQ = FCS_finite [].
Proof.
  induction sub; simpl; auto.
  unfold free_vars_sub_restrict_formula in *; simpl.
  destruct a; simpl; auto.
  unfold in_signature.
  dest_cases w; simpl; symmetry in Heqw.
  rewrite IHsub; clear IHsub; auto.
Qed.
Hint Rewrite free_vars_sub_restrict_formula_quantQ : core.

Lemma free_vars_sub_restrict_formula_KFtrue :
  forall sub, free_vars_sub_restrict_formula sub KFtrue = FCS_finite [].
Proof.
  induction sub; simpl; auto.
  unfold free_vars_sub_restrict_formula in *; simpl.
  destruct a; simpl; auto.
Qed.
Hint Rewrite free_vars_sub_restrict_formula_KFtrue : core.

Lemma disjoint_nil_r: forall {T} (l : list T), disjoint l [].
Proof.
  introv i j; simpl in *; tcsp.
Qed.

Lemma eassignables_disj_null_right :
  forall e, eassignables_disj e (FCS_finite []) = true.
Proof.
  destruct e; simpl; auto.
  unfold eassignables_disj; simpl; auto; apply disj_dec_prop.
  apply disjoint_nil_r.
Qed.
Hint Rewrite eassignables_disj_null_right : core.

Lemma sequent_true_G_swap_US :
  forall H sub,
    sequent_true (emHyps ⊢ US_formula_otrue quantQ sub)
    -> sequent_true (H ⊢ US_formula_otrue (KFbox pconsta quantQ) sub).
Proof.
  introv h.
  introv hhyps; simpl in *.

  unfold US_formula_otrue, uniform_substitution_formula_opt_true in *; simpl in *.
  unfold on_test in *; simpl in *.
  unfold U_admissible_formula in *; simpl in *; autorewrite with core in *; simpl.
  dest_cases w; clear Heqw; simpl.

  introv dsp.

  apply (h I w0); simpl; tcsp.
Qed.

Lemma sequent_true_move_hyp :
  forall C x y G W X Fx Fy,
    sequent_true ((G ⊕ (((W • (y : Fy)) • (x : Fx)) ⊕ X)) ⊢ C)
    -> sequent_true (((G • (x : Fx)) ⊕ ((W • (y : Fy)) ⊕ X)) ⊢ C).
Proof.
  introv st hhyps; simpl in *.
  apply st; introv i; simpl in *.
  allrw in_app_iff; allrw @in_snoc.
  repndors; subst; simpl in *;
    try (complete (apply hhyps; allrw in_app_iff; allrw @in_snoc; tcsp)).

  { apply (hhyps (MkHyp y Fy)); allrw in_app_iff; allrw @in_snoc; tcsp. }

  { apply (hhyps (MkHyp x Fx)); allrw in_app_iff; allrw @in_snoc; tcsp. }
Qed.

Lemma sequent_true_GE2GT :
  forall H A B,
    sequent_true (H ⊢ KFgreater A B)
    -> sequent_true (H ⊢ KFgreaterEqual A B).
Proof.
  introv st hhyps; simpl in *.
  apply Rgt_ge.
  apply st; auto.
Qed.

Lemma sequent_true_false_left :
  forall G x J F, sequent_true (((G • (x : KFfalse)) ⊕ J) ⊢ F).
Proof.
  introv hyps; simpl in *.
  pose proof (hyps (x : KFfalse)) as q; simpl in q.
  autodimp q hyp; try (complete (inversion q)).
  rewrite in_app_iff; rewrite in_snoc; tcsp.
Qed.

(*
Lemma sequent_true_all_right :
  forall H x y C,
    in_eassignables y (free_vars_hyps H) = false
    -> sequent_true (H ⊢ swap_formula (MkSwapping x y) C)
    -> sequent_true (H ⊢ KFforallVars [x] C).
Proof.
  introv ie st hyps ers; simpl in *.
  destruct rs; simpl in *; ginv.
  destruct rs; simpl in *; ginv.
  pose proof (st (swap_interp (MkSwapping x y) I) (swap_state (MkSwapping x y) (upd_state v x r))) as q; simpl in q.
  unfold sequent_true_I_v, DSF in q; simpl in q.
  rewrite <- swap_dynamic_semantics_formula2 in q.
  apply q; clear q.
  introv i.
  applydup hyps in i as j; unfold DSF in j.
Qed.
*)

Lemma apply_step_preserves_soundness :
  forall ps s,
    sound_proof_state (apply_step ps s)
    -> sound_proof_state ps.
Proof.
  dstep s Case; introv sound; simpl in *.

  { Case "Assumption".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *; auto.
    remember (find_hyp H x) as fh; destruct fh; symmetry in Heqfh; auto.
    destruct d as [G f J].
    dest_cases w; subst.
    apply find_hyp_some_implies in Heqfh; subst.
    apply sound_proof_state_cons; dands; auto.
    apply sequent_true_assumption. }

  { Case "Clear".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *; auto.
    remember (find_hyp H x) as fh; destruct fh; symmetry in Heqfh; auto.
    destruct d as [G f J].
    apply find_hyp_some_implies in Heqfh; subst.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply sequent_true_weaken; auto. }

  { Case "ImplyRight".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *; auto.
    destruct C; simpl in *; auto.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply (RULE_imply_right_sch_true x).
    introv i; simpl in i; repndors; subst; tcsp. }

  { Case "ImplyLeft".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *; auto.
    remember (find_hyp H x) as fh; destruct fh; symmetry in Heqfh; auto.
    destruct d as [G f J].
    destruct f; simpl in *; auto.
    apply find_hyp_some_implies in Heqfh; subst.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply (RULE_imply_left_sch_true x); introv i; simpl in *; repndors; subst; tcsp. }

  { Case "OrLeft".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *; auto.
    remember (find_hyp H x) as fh; destruct fh; symmetry in Heqfh; auto.
    destruct d as [G f J].
    destruct f; simpl in *; auto.
    apply find_hyp_some_implies in Heqfh; subst.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply (RULE_or_left_sch_true x); introv i; simpl in *; repndors; subst; tcsp. }

  { Case "AndLeft".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *; auto.
    remember (find_hyp H x) as fh; destruct fh; symmetry in Heqfh; auto.
    destruct d as [G f J].
    destruct f; simpl in *; auto.
    apply find_hyp_some_implies in Heqfh; subst.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply (RULE_and_left_sch_true x y); introv i; simpl in *; repndors; subst; tcsp. }

  { Case "EquivLeft".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *; auto.
    remember (find_hyp H x) as fh; destruct fh; symmetry in Heqfh; auto.
    destruct d as [G f J].
    destruct f; simpl in *; auto.
    apply find_hyp_some_implies in Heqfh; subst.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply (RULE_equiv_left_sch_true x y); introv i; simpl in *; repndors; subst; tcsp. }

  { Case "EquivRight".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *; auto.
    destruct C; simpl in *; auto.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply RULE_equiv_right_sch_true; simpl; introv i; repndors; subst; tcsp. }

  { Case "AndRight".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *; auto.
    destruct C; simpl in *; auto.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply RULE_and_right_sch_true; simpl; introv i; repndors; subst; tcsp. }

  { Case "OrRight1".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *; auto.
    destruct C; simpl in *; auto.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply RULE_or_right1_sch_true; simpl; introv i; repndors; subst; tcsp. }

  { Case "OrRight2".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *; auto.
    destruct C; simpl in *; auto.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply RULE_or_right2_sch_true; simpl; introv i; repndors; subst; tcsp. }

  { Case "NotLeft".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *; auto.
    remember (find_hyp H x) as fh; destruct fh; symmetry in Heqfh; auto.
    destruct d as [G f J].
    destruct f; simpl in *; auto.
    apply find_hyp_some_implies in Heqfh; subst.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply (RULE_not_left_sch_true x); introv i; simpl in *; repndors; subst; tcsp. }

  { Case "NotRight".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *; auto.
    destruct C; simpl in *; auto.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply (RULE_not_right_sch_true x H C); simpl; introv i; repndors; subst; tcsp. }

  { Case "MoveHyp".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    remember (find_hyp H x) as fxh; destruct fxh; symmetry in Heqfxh; auto.
    destruct d as [G Fx J].
    remember (find_hyp J y) as fyh; destruct fyh; symmetry in Heqfyh; auto.
    destruct d as [W Fy X].
    apply find_hyp_some_implies in Heqfxh; subst.
    apply find_hyp_some_implies in Heqfyh; subst.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply sequent_true_move_hyp; auto. }

  { Case "Cut".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    eapply cut_formula_in_sequent; eauto. }

  { Case "DIge".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply cut_valid_formula_in_sequent in sound0; auto.
    apply SW_rule_true; simpl; introv i; repndors; subst; tcsp.
    apply US_sound; simpl; introv i; repndors; subst; tcsp.
    apply DI_ge_sound; simpl; tcsp. }

  { Case "DIgeD".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply cut_valid_formula_in_sequent in sound0; auto.
    apply SW_rule_true; simpl; introv i; repndors; subst; tcsp.
    apply US_sound; simpl; introv i; repndors; subst; tcsp.
    apply DI_ge_diff_sound; simpl; tcsp. }

  { Case "OdeComm".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply cut_valid_formula_in_sequent in sound0; auto.
    apply SW_rule_true; simpl; introv i; repndors; subst; tcsp.
    apply US_sound; simpl; introv i; repndors; subst; tcsp.
    apply ode_comm_sound; simpl; tcsp. }

  { Case "DGhostLR".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply cut_valid_formula_in_sequent in sound0; auto.
    apply SW_rule_true; simpl; introv i; repndors; subst; tcsp.
    apply US_sound; simpl; introv i; repndors; subst; tcsp.
    apply DG_LR_axiom_sound; simpl; tcsp. }

  { Case "spDGhostLR".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply cut_valid_formula_in_sequent in sound0; auto.
    apply SW_rule_true; simpl; introv i; repndors; subst; tcsp.
    apply US_sound; simpl; introv i; repndors; subst; tcsp.
    apply sp_DG_LR_axiom_sound; simpl; tcsp. }

  { Case "XP".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply cut_valid_formula_in_sequent in sound0; auto.
    apply SW_rule_true; simpl; introv i; repndors; subst; tcsp.
    apply differential_identity_sound; simpl; tcsp. }

  { Case "PXP".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply cut_valid_formula_in_sequent in sound0; auto.
    apply SW_rule_true; simpl; introv i; repndors; subst; tcsp.
    apply US_sound; simpl; introv i; repndors; subst; tcsp.
    apply pred_XP_sound; simpl; tcsp. }

  { Case "QPXP".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply cut_valid_formula_in_sequent in sound0; auto.
    apply SW_rule_true; simpl; introv i; repndors; subst; tcsp.
    apply US_sound; simpl; introv i; repndors; subst; tcsp.
    apply quant_pred_XP_sound; simpl; tcsp. }

  { Case "DE".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply cut_valid_formula_in_sequent in sound0; auto.
    apply SW_rule_true; simpl; introv i; repndors; subst; tcsp.
    apply US_sound; simpl; introv i; repndors; subst; tcsp.
    apply differential_effect_axiom_sound; simpl; tcsp. }

  { Case "DEsch".

    destruct ps; simpl in *; auto; dest_cases w;[].
    destruct s as [H C]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply cut_valid_formula_in_sequent in sound0; auto.
    apply differential_effect_sch_axiom_sound; simpl; tcsp. }

  { Case "V".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply cut_valid_formula_in_sequent in sound0; auto.
    apply US_sound; simpl; introv i; repndors; subst; tcsp.
    apply V_axiom_sound; simpl; tcsp. }

  { Case "DR".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply cut_valid_formula_in_sequent in sound0; auto.
    apply SW_rule_true; simpl; introv i; repndors; subst; tcsp.
    apply US_sound; simpl; introv i; repndors; subst; tcsp.
    apply diff_real_sound; simpl; tcsp. }

  { Case "DRN".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply cut_valid_formula_in_sequent in sound0; auto.
    apply SW_rule_true; simpl; introv i; repndors; subst; tcsp.
    apply US_sound; simpl; introv i; repndors; subst; tcsp.
    apply diff_realn_sound; simpl; tcsp. }

  { Case "G".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *; auto.
    allrw sound_proof_state_cons; repnd; dands; auto.
    eapply cut_formula_in_sequent;[exact sound1|]; clear sound1 sound.
    apply sequent_true_G_swap_US; auto. }

  (*
  { Case "US".

    destruct ps as [|seq seqs]; simpl in *; auto.
    introv i; simpl in i; repndors; subst;[|apply sound; simpl; tcsp].
    pose proof (sound (US_sequent_false sub s)) as q; clear sound; simpl in q; autodimp q hyp.

  }
   *)

  { Case "Assign".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply cut_valid_formula_in_sequent in sound0; auto.
    apply SW_rule_true; simpl; introv i; repndors; subst; tcsp.
    apply US_sound; simpl; introv i; repndors; subst; tcsp.
    apply assignment_axiom_sound; simpl; tcsp. }

  { Case "Assignp".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply cut_valid_formula_in_sequent in sound0; auto.
    apply SW_rule_true; simpl; introv i; repndors; subst; tcsp.
    apply US_sound; simpl; introv i; repndors; subst; tcsp.
    apply assignmentp_axiom_sound; simpl; tcsp. }

  { Case "K".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply cut_valid_formula_in_sequent in sound0; auto.
    apply US_sound; simpl; introv i; repndors; subst; tcsp.
    apply K_quant_axiom_sound; simpl; tcsp. }

  { Case "CE".

    destruct ps; simpl in *; auto.
    destruct s as [H F]; simpl in *.
    allrw sound_proof_state_cons; repnd; dands; auto.
    eapply cut_formula_in_sequent;[exact sound1|]; clear sound1.
    apply Rule_thin_all_hyps_true; introv i; simpl in i; repndors; subst; tcsp.
    apply US_seq_Rule_true; introv i; simpl in i; repndors; subst; tcsp.
    apply CE_Rule_sch_true; introv i; simpl in i; repndors; subst; tcsp. }

  { Case "GE2GT".

    destruct ps; simpl in *; auto.
    destruct s as [H F]; simpl in *.
    destruct F; simpl in *; auto.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply sequent_true_GE2GT; auto. }

  { Case "FalseLeft".

    destruct ps; simpl in *; auto.
    destruct s as [H F]; simpl in *.
    remember (find_hyp H x) as fxh; destruct fxh; symmetry in Heqfxh; auto.
    destruct d as [G Fx J].
    destruct Fx; simpl in *; auto.
    apply find_hyp_some_implies in Heqfxh; subst.
    allrw sound_proof_state_cons; repnd; dands; auto.
    apply sequent_true_false_left. }

  (*
  { Case "AllRight".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *; auto.
    destruct C; simpl in *; auto.
    destruct vars; simpl in *; auto.
    destruct vars; simpl in *; auto.
    dest_cases w.
    symmetry in Heqw.
    allrw sound_proof_state_cons; repnd; dands; auto.
    clear sound.
  }*)

  { Case "Swap".

    destruct ps as [|seq seqs]; simpl in *; auto.
    allrw sound_proof_state_cons; repnd; dands; auto.
    eapply sequent_true_swap_sequent_implies; eauto. }

  { Case "Focus".

    remember (focus_state ps n) as fs; symmetry in Heqfs; destruct fs; auto.
    destruct p as [seq seqs]; simpl in *.
    introv i.
    eapply in_focus_state_some in Heqfs;[|exact i].
    repndors; subst; auto; apply sound; simpl; tcsp. }
Qed.


(*
Lemma apply_step_preserves_soundness_I :
  forall ps s (I : interpretation),
    sound_proof_state_I (apply_step ps s) I
    -> sound_proof_state_I ps I.
Proof.
  dstep s Case; introv sound; simpl in *.

  { Case "ImplyRight".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *; auto.
    destruct C; simpl in *; auto.
    introv i; simpl in i; repndors; subst; tcsp;[|apply sound;simpl;tcsp].
    apply (RULE_imply_right_sch_true_I x).
    introv i; simpl in i; repndors; subst; tcsp.
    apply sound; simpl; tcsp. }

  { Case "AndLeft".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *; auto.
    remember (find_hyp H x) as fh; destruct fh; symmetry in Heqfh; auto.
    destruct d as [G f J].
    destruct f; simpl in *; auto.
    introv i; simpl in i; repndors; subst;[|apply sound;simpl;tcsp].
    apply find_hyp_some_implies in Heqfh; subst.
    apply (RULE_and_left_sch_true_I x y); introv i; simpl in *; repndors; subst; tcsp.
    apply sound; simpl; tcsp. }

  { Case "Cut".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    introv i; simpl in i; repndors; subst;[|apply sound; simpl; tcsp].
    introv i; simpl in *.
    apply (sound ((H • (x : f)) ⊢ C)); simpl; tcsp.
    introv q.
    apply in_snoc in q; repndors; subst; tcsp; simpl.
    apply (sound (H ⊢ f)); simpl; tcsp. }

  { Case "DIge".

    destruct ps; simpl in *; auto.
    destruct s as [H C]; simpl in *.
    introv i; simpl in i; repndors; subst;[|apply sound; simpl; tcsp].
    introv i; simpl in *.
    apply (sound ((H • (x : US_formula_otrue DI_ge_axiom sub)) ⊢ C)); simpl; tcsp.
    introv q.
    apply in_snoc in q; repndors; subst; tcsp; simpl.
    unfold US_formula_otrue.
    unfold uniform_substitution_formula_opt_true.
    remember (uniform_substitution_formula DI_ge_axiom sub) as usf;
      symmetry in Hequsf; destruct usf; simpl; tcsp.
    pose proof (us_lemma_formula DI_ge_axiom sub I v) as q.
    unfold on_uniform_substitution_formula in q.
    rewrite Hequsf in q.
    apply q.
    apply DI_ge_sound; simpl; tcsp. }

  (*
  { Case "US".

    destruct ps as [|seq seqs]; simpl in *; auto.
    introv i; simpl in i; repndors; subst;[|apply sound; simpl; tcsp].
    pose proof (sound (US_sequent_false sub s)) as q; clear sound; simpl in q; autodimp q hyp.

  }
*)

  { Case "Focus".

    remember (focus_state ps n) as fs; symmetry in Heqfs; destruct fs; auto.
    destruct p as [seq seqs]; simpl in *.
    introv i.
    eapply in_focus_state_some in Heqfs;[|exact i].
    repndors; subst; auto; apply sound; simpl; tcsp. }
Qed.
*)

Lemma apply_script_preserves_soundness :
  forall s ps,
    sound_proof_state (apply_script ps s)
    -> sound_proof_state ps.
Proof.
  induction s; introv sound; simpl in *; auto.
  apply IHs in sound.
  apply apply_step_preserves_soundness in sound; auto.
Qed.

(*
Lemma apply_script_preserves_soundness_I :
  forall s ps (I : interpretation),
    sound_proof_state_I (apply_script ps s) I
    -> sound_proof_state_I ps I.
Proof.
  induction s; introv sound; simpl in *; auto.
  apply IHs in sound.
  apply apply_step_preserves_soundness_I in sound; auto.
Qed.
*)

Lemma sequent_true_I_as_sound_proof_state_I :
  forall seq I,
    sound_proof_state_I [seq] I
    -> sequent_true_I seq I.
Proof.
  introv i; apply i; simpl; tcsp.
Qed.

Lemma sequent_true_as_sound_proof_state :
  forall seq,
    sound_proof_state [seq]
    -> sequent_true seq.
Proof.
  introv i; apply i; simpl; tcsp.
Qed.

Lemma swap_varv_varx_on_vary :
  swap (MkSwapping varv varx) vary = vary.
Proof.
  unfold swap; simpl; auto.
Qed.
Hint Rewrite swap_varv_varx_on_vary : core.

Lemma swap_vary_varx_on_varv :
  swap (MkSwapping vary varx) varv = varv.
Proof.
  unfold swap; simpl; auto.
Qed.
Hint Rewrite swap_vary_varx_on_varv : core.

Lemma swap_vary_varx_on_varx :
  swap (MkSwapping vary varx) varx = vary.
Proof.
  unfold swap; simpl; auto.
Qed.
Hint Rewrite swap_vary_varx_on_varx : core.

Lemma sound_proof_state_nil : sound_proof_state [].
Proof.
  introv; simpl; tcsp.
Qed.
Hint Resolve sound_proof_state_nil : core.


Definition DI_box_sch (A B : Formula) : Formula :=
  KFimply
    A
    (KFimply
       (KFbox (KPodeSystem (ODEconst odec) quantH) B)
       (KFbox (KPodeSystem (ODEconst odec) quantH) A)).

Definition DI_box_seq H (A B : Formula) : sequent :=
  MkSeq H (DI_box_sch A B).
