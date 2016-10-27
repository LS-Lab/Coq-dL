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
(* Some rules needs classical reasoning in the metatheory,
   such as the diamond rule. *)
Require Export Classical_Prop.



(**

  Diamond axiom --- see Figure 2, Section 4

  <a>P <-> ¬[a]¬P

 *)
Definition diamond_axiom : Formula :=
  KFequiv
    (KFdiamond pconsta quantP)
    (KFnot (KFbox pconsta (KFnot quantP))).

Definition diamond_rule : rule := MkRule [] diamond_axiom.

Definition diamond_axiom_sound : rule_true diamond_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv; simpl.
  split; intro h; exrepnd.

  {
    intro q.
    pose proof (q w) as z; clear q.
    autodimp z hyp.
  }

  {
    (* needs classical logic *)
    match goal with
    | [ |- ?t ] => pose proof (classic t) as q
    end.
    repndors; auto;[].
    destruct h; introv; introv h1 h2.
    destruct q.
    exists w; auto.
  }
Qed.


(**

  Assignment axiom --- see Figure 2, Section 4

  [x:=f]p(x) <-> p(f)

 *)
Definition assignment_axiom : Formula :=
  KFequiv
    (KFbox (KPassign assignx tfuncf) (Pof1 predp tvarx))
    (Pof1 predp tfuncf).

Definition assignment_rule : rule := MkRule [] assignment_axiom.

Definition assignment_axiom_sound : rule_true assignment_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv; simpl.
  split; intro h; exrepnd.

  {
    pose proof (h (upd_state_var
                     v
                     varx
                     (interp_fun_f
                        0
                        (I (SymbolFunction funcf 0))
                        (Vector.nil R)))) as q; clear h.
    autorewrite with core in *.
    apply q.
    unfold differ_state_except; autorewrite with core; dands; auto.
    introv d.
    rewrite upd_state_var_diff; auto.
  }

  {
    introv d.
    destruct d as [d1 d2].
    rewrite d2; auto.
  }
Qed.


(**

  Test axiom --- see Figure 2, Section 4

  [?q]p <-> (q -> p)

 *)
Definition test_axiom : Formula :=
  KFequiv
    (KFbox (KPtest fpredq) fpredp)
    (KFimply fpredq fpredp).

Definition test_rule : rule := MkRule [] test_axiom.

Definition test_axiom_sound : rule_true test_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv; simpl.
  split; intro h; exrepnd.

  { intro q; apply (h v); auto. }

  { introv q; repnd; subst; tcsp. }
Qed.


(**

  Choice axiom --- see Figure 2, Section 4

  [a∪b]P <-> [a]P /\ [b]P

 *)
Definition choice_axiom : Formula :=
  KFequiv
    (KFbox (KPchoice pconsta pconstb) quantP)
    (KFand
       (KFbox pconsta quantP)
       (KFbox pconstb quantP)).

Definition choice_rule : rule := MkRule [] choice_axiom.

Definition choice_axiom_sound : rule_true choice_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv; simpl.
  split; intro h; exrepnd.

  { dands; introv q; apply h; tcsp. }

  { introv q; repndors; tcsp. }
Qed.


(**

  Sequential composition axiom --- see Figure 2, Section 4

  [a;b]P <-> [a][b]P

 *)
Definition sequential_composition_axiom : Formula :=
  KFequiv
    (KFbox (KPcompose pconsta pconstb) quantP)
    (KFbox pconsta (KFbox pconstb quantP)).

Definition sequential_composition_rule : rule := MkRule [] sequential_composition_axiom.

Definition sequential_composition_axiom_sound : rule_true sequential_composition_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv; simpl.
  split; intro h; exrepnd.

  { introv h1 h2.
    apply h; eexists; dands; eauto. }

  { introv q; exrepnd; eapply h; eauto. }
Qed.


(**

  Iteration axiom --- see Figure 2, Section 4

  [a*]P <-> P /\ [a][a*]P

 *)
Definition iteration_axiom : Formula :=
  KFequiv
    (KFbox (KPloop pconsta) quantP)
    (KFand
       quantP
       (KFbox pconsta (KFbox (KPloop pconsta) quantP))).

Definition iteration_rule : rule := MkRule [] iteration_axiom.

Definition iteration_axiom_sound : rule_true iteration_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv; simpl.
  split; intro h; exrepnd.

  { dands; auto.
    introv q z.
    apply h.
    eapply program_close_trans_rev; eauto. }

  { introv q.
    apply program_close_trans_imply_rev in q; repndors; exrepnd; subst; auto.
    eapply h; eauto. }
Qed.


(**

  K axiom --- see Figure 2, Section 4

  [a](P -> Q) -> ([a]P -> [a]Q)

 *)
Definition K_axiom : Formula :=
  KFimply
    (KFbox pconsta (KFimply quantP quantQ))
    (KFimply
       (KFbox pconsta quantP)
       (KFbox pconsta quantQ)).

Definition K_rule : rule := MkRule [] K_axiom.

Definition K_axiom_sound : rule_true K_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv; simpl.
  introv h1 h2 h3; tcsp.
Qed.


(**

  I axiom --- see Figure 2, Section 4

  [a*](P -> [a]P) -> (P -> [a*]P)

 *)
Definition I_axiom : Formula :=
  KFimply
    (KFbox
       (KPloop pconsta)
       (KFimply
          quantP
          (KFbox pconsta quantP)))
    (KFimply
       quantP
       (KFbox (KPloop pconsta) quantP)).

Definition I_rule : rule := MkRule [] I_axiom.

Definition I_axiom_sound : rule_true I_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv; simpl.
  introv h1 h2 h3.
  induction h3; auto.
  repeat (autodimp IHh3 hyp).
  eapply h1; eauto.
Qed.


(**

  V axiom --- see Figure 2, Section 4

  p -> [a]p

 *)
Definition V_axiom : Formula :=
  KFimply fpredp (KFbox pconsta fpredp).

Definition V_rule : rule := MkRule [] V_axiom.

Definition V_axiom_sound : rule_true V_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv; simpl.
  introv h1 h2; auto.
Qed.


(**

  G rule --- see Figure 2, Section 4

    p(x)
  -------
  [a]p(x)

 *)
Definition G_rule : rule :=
  MkRule
    [quantP]
    (KFbox pconsta quantP).

Definition G_rule_sound : rule_true G_rule.
Proof.
  introv imp; simpl in *.
  pose proof (imp quantP) as h; clear imp; autodimp h hyp;[].
  repeat introv; simpl.
  introv q.
  pose proof (h I w) as z; simpl in z; auto.
Qed.


(**

  Forall rule --- see Figure 2, Section 4

    p(x)
  --------
  ∀x.p(x)

 *)
Definition forall_rule : rule :=
  MkRule
    [Pof1 predp tvarx]
    (KFforallVars [varx] (Pof1 predp tvarx)).

Definition forall_rule_sound : rule_true forall_rule.
Proof.
  introv imp; simpl in *.
  pose proof (imp (Pof1 predp tvarx)) as h; clear imp; autodimp h hyp;[].
  repeat introv; simpl.
  introv len.
  repeat (destruct rs; simpl in *; ginv).
  autorewrite with core.
  pose proof (h I (upd_state_var v varx r)) as z; simpl in z; auto.
Qed.


(**

  Modus-Ponens rule --- see Figure 2, Section 4

  p -> q    p
  -----------
       q

 *)
Definition MP_rule : rule :=
  MkRule
    [KFimply fpredp fpredq, fpredp]
    fpredq.

Definition MP_rule_sound : rule_true MP_rule.
Proof.
  introv imp; simpl in *.
  pose proof (imp (KFimply fpredp fpredq)) as h1; autodimp h1 hyp;[].
  pose proof (imp fpredp) as h2; autodimp h2 hyp;[].
  clear imp.
  repeat introv; simpl.
  pose proof (h1 I v) as z1; simpl in z1; auto.
  pose proof (h2 I v) as z2; simpl in z2; auto.
Qed.


(**

  Modus-Ponens rule with quantifiers

  P -> Q    P
  -----------
       Q

 *)
Definition MP_rule_quant : rule :=
  MkRule
    [KFimply quantP quantQ, quantP]
    quantQ.

Definition MP_rule_quant_locally_sound : rule_locally_sound MP_rule_quant.
Proof.
  introv imp; simpl in *.
  dLin_hyp h.
  repeat introv; simpl.
  pose proof (h v) as z1; simpl in z1; auto.
  pose proof (h0 v) as z2; simpl in z2; auto.
Qed.



(**

  CE rule --- see Figure 2, Section 4

     P <-> Q
  -------------------
  C(P) <-> C(Q)

 *)
Definition CE_rule : rule :=
  MkRule
    [KFequiv quantP quantQ]
    (KFequiv (qC quantP) (qC quantQ)).

Lemma CE_rule_locally_sound : rule_locally_sound CE_rule.
Proof.
  introv imp; simpl in *.
  dLin_hyp h.
  introv; simpl.
  remember (I (SymbolQuantifier qsC)) as IC; simpl in IC.
  destruct IC as [ic extic]; clear HeqIC; auto.
Qed.


(**

  p <-> q    p
  -----------
       q

 *)
Definition IFF_rule : rule :=
  MkRule
    [KFequiv quantP quantQ, quantP]
    quantQ.

Definition IFF_rule_locally_sound : rule_locally_sound IFF_rule.
Proof.
  introv imp; simpl in *.
  dLin_hyp h.
  repeat introv; simpl.
  pose proof (h v) as z1; simpl in z1; auto.
  pose proof (h0 v) as z2; simpl in z2; auto.
  apply z1; auto.
Qed.
