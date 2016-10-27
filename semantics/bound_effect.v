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



(** Bound effect --- see Lemma 1, Section 2.4 *)
Lemma bound_effect_lemma :
  forall alpha I v w,
    dynamic_semantics_program I alpha v w
    -> equal_states_on_complement v w (bound_vars_program alpha).
Proof.
  unfold equal_states_on_complement;
    prog_ind alpha Case; simpl; introv ds i;
      ginv; try (complete (inversion i)).

  { Case "KPassign".
    repeat (dest_cases x; GC).
    eapply differ_state_except_prop1; eauto.
  }

  { Case "KPassignAny".
    introv h.
    repeat (dest_cases x; GC).
    exrepnd.
    eapply differ_state_except_prop1; eauto. }

  { Case "KPtest".
    repnd; subst; auto.
  }

  { Case "KPchoice".
    apply in_eassignables_app_false_implies in i; repnd.
    repndors;[|].
    - apply (IHalpha1 I); auto.
    - apply (IHalpha2 I); auto.
  }

  { Case "KPcompose".
    apply in_eassignables_app_false_implies in i; repnd.
    exrepnd.
    pose proof (IHalpha1 I v s ds1 a i0) as h1.
    pose proof (IHalpha2 I s w ds0 a i) as h2.
    congruence.
  }

  { Case "KPloop".
    induction ds; auto.
    rewrite IHds; clear IHds.
    apply (IHalpha I); auto.
  }

  { Case "KPodeSystem".
    pose proof (equal_states_upto_prop1 a v w (ode_footprint I ode)) as q.
    repeat (autodimp q hyp);
      [|intro j;
        apply in_ode_footprint_implies_in_bound_vars in j;
        rewrite i in j; ginv];[].

    exrepnd; subst.
    pose proof (ds1 (mk_preal_upto r r (Rle_refl r))) as h; clear ds1; simpl in h; repnd.
    introv j.
    rewrite <- h; auto.
    apply ds0; intro xx.
    apply ode_footprint_diff_subset_ode_footprint in xx; auto. }
Qed.

