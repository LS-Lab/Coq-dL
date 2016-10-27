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
Require Import integral.



(**

  Differential weakening --- see Figure 3, Section 5.1

  [x'=f(x) & q(x)]q(x)

 *)
Definition differential_weakening_axiom : Formula :=
  KFbox
    (KPodeSystem
       (ODEsing varx (Fof1 funcf tvarx))
       (Pof1 predq tvarx)
    )
    (Pof1 predq tvarx).

Definition differential_weakening_rule : rule := MkRule [] differential_weakening_axiom.

Lemma differential_weakening_axiom_sound : rule_true differential_weakening_rule.
Proof.
  introv imp; simpl in *; clear imp.
  introv h; simpl in *; exrepnd; subst.
  pose proof (h1 (mk_preal_upto r r (Rle_refl r))) as q; simpl in *; repnd; auto.
Qed.


(**

  Differential cut --- see Figure 3, Section 5.1

      [x'=f(x) & q(x)]r(x)
      ->
      ([x'=f(x) & q(x)]p(x) <-> [x'=f(x) & (q(x) /\ r(x))]p(x))

 *)
Definition differential_cut_axiom : Formula :=
  KFimply
    (KFbox
       (KPodeSystem
          (ODEsing varx (Fof1 funcf tvarx))
          (Pof1 predq tvarx)
       )
       (Pof1 predr tvarx)
    )
    (KFequiv
       (KFbox
          (KPodeSystem
             (ODEsing varx (Fof1 funcf tvarx))
             (Pof1 predq tvarx)
          )
          (Pof1 predp tvarx)
       )
       (KFbox
          (KPodeSystem
             (ODEsing varx (Fof1 funcf tvarx))
             (KFand
                (Pof1 predq tvarx)
                (Pof1 predr tvarx)
             )
          )
          (Pof1 predp tvarx)
       )
    ).

Definition differential_cut_rule : rule := MkRule [] differential_cut_axiom.

Lemma differential_cut_axiom_sound : rule_true differential_cut_rule.
Proof.
  introv imp; simpl in *; clear imp.
  introv IHqr; simpl in *.
  split.

  {
    introv IHqp; introv.
    pose proof (IHqr w) as qr. clear IHqr.
    pose proof (IHqp w) as qp. clear IHqp.
    introv h; exrepnd; subst.
    apply qp; clear qp.

    exists r phi; dands; auto.
    introv.
    pose proof (h1 zeta) as q; clear h1; tcsp.
  }

  {
    introv IHqrp cond.
    exrepnd; subst.

    apply (IHqrp (phi r)); clear IHqrp.

    exists r phi; dands; auto.
    introv.

    dands; auto; try (complete (pose proof (cond1 zeta) as q; repnd; auto)).

    apply (IHqr (phi zeta)).
    exists zeta phi; dands; auto; introv.

    {
      pose proof (cond3 (ex_preal_upto_trans r zeta zeta0)).
      simpl in *.
      auto.
    }

    {
      pose proof (cond1 (ex_preal_upto_trans r zeta zeta0)).
      simpl in *.
      auto.
    }
  }
Qed.


(**

  Differential effect --- see Figure 3, Section 5.1

  [x'=f(x) & q(x)]p(x,x') <-> [x'=f(x) & q(x)][x':=f(x)]p(x,x')

 *)
Definition differential_effect_axiom : Formula :=
  KFequiv
    (KFbox
       (KPodeSystem
          (ODEsing varx (Fof1 funcf tvarx))
          (Pof1 predq tvarx)
       )
       (Pof2 predp tvarx tvarxp)
    )
    (KFbox
          (KPodeSystem
             (ODEsing varx (Fof1 funcf tvarx))
             (Pof1 predq tvarx)
          )
          (KFbox
            (KPassign assignxp (Fof1 funcf tvarx))
              (Pof2 predp tvarx tvarxp)
          )
    ).

Definition differential_effect_rule : rule := MkRule [] differential_effect_axiom.

Lemma differential_effect_axiom_sound : rule_true differential_effect_rule.
Proof.
  introv imp. simpl in *. clear imp.
  repeat introv; simpl.

  split; intro h; introv cond; introv.

  {
    introv diff.
    exrepnd; subst.

    destruct diff as [diff1 diff2].
    rewrite <- diff1;[|intro xx; inversion xx].
    rewrite diff2.

    assert (phi r assignxp
            = interp_fun_f
                1
                (I (SymbolFunction funcf 1))
                (Vector.cons R (phi r assignx) 0 (Vector.nil R))) as e.
    { pose proof (cond3 (mk_preal_upto r r (Rle_refl r)) varx) as z; simpl in z.
      autodimp z hyp; tcsp. }

    pose proof (h (phi r)) as q; clear h; autodimp q hyp.
    { exists r phi; dands; auto. }

    rewrite <- e; auto.
  }

  {
    exrepnd; subst.

    apply (h (phi r)).
    { exists r phi; dands; auto. }

    split; auto.
    pose proof (cond3 (mk_preal_upto r r (Rle_refl r)) varx) as z; simpl in z.
    autodimp z hyp; tcsp.
  }
Qed.


(**

  Differential effect with constant

  [x'=f(x),c & q(x)]p(x,x') <-> [x'=f(x),c & q(x)][x':=f(x)]p(x,x')

 *)
Definition differential_effect_const_axiom : Formula :=
  KFequiv
    (KFbox
       (KPodeSystem
          (ODEprod
             (ODEsing varx (Fof1 funcf tvarx))
             (ODEconst odec))
          (Pof1 predq tvarx)
       )
       (Pof2 predp tvarx tvarxp)
    )
    (KFbox
          (KPodeSystem
             (ODEprod
                (ODEsing varx (Fof1 funcf tvarx))
                (ODEconst odec))
             (Pof1 predq tvarx)
          )
          (KFbox
            (KPassign assignxp (Fof1 funcf tvarx))
              (Pof2 predp tvarx tvarxp)
          )
    ).

Definition differential_effect_const_rule : rule :=
  MkRule [] differential_effect_const_axiom.

Lemma differential_effect_const_axiom_sound : rule_true differential_effect_const_rule.
Proof.
  introv imp. simpl in *. clear imp.
  repeat introv; simpl.

  split; intro h; introv cond; introv.

  {
    introv diff.
    exrepnd; subst.

    destruct diff as [diff1 diff2].
    rewrite <- diff1;[|intro xx; inversion xx].
    rewrite diff2.

    assert (phi r assignxp
            = (interp_fun_f
                 1
                 (I (SymbolFunction funcf 1))
                 (Vector.cons R (phi r assignx) 0 (Vector.nil R))
               + interp_ode_dm (I (SymbolODE odec)) (phi r) (KD varx))%R) as e.
    { pose proof (cond3 (mk_preal_upto r r (Rle_refl r)) varx) as z; simpl in z.
      autodimp z hyp; tcsp. }

    pose proof (h (phi r)) as q; clear h; autodimp q hyp.
    { exists r phi; dands; auto. }
    (*
    rewrite <- e; auto.
  }

  {
    exrepnd; subst.

    apply (h (phi r)).
    { exists r phi; dands; auto. }

    split; auto.
    pose proof (cond3 (mk_preal_upto r r (Rle_refl r)) varx) as z; simpl in z.
    autodimp z hyp; tcsp.
  }
*)
Abort.


(**

  Differential constant --- see Figure 3, Section 5.1

  f' = 0

 *)
Definition differential_constant_axiom : Formula :=
  KFequal (KTdifferential tfuncf) 0.

Definition differential_constant_rule : rule := MkRule [] differential_constant_axiom.

Lemma differential_constant_sound : rule_true differential_constant_rule.
Proof.
  introv imp; repeat introv; tcsp.
Qed.

Definition differential_constant_R_axiom : Formula :=
  KFequal (KTdifferential tfuncf) (KTnumber (KTNreal 0)).

Definition differential_constant_R_rule : rule := MkRule [] differential_constant_R_axiom.

Lemma differential_constant_R_sound : rule_true differential_constant_R_rule.
Proof.
  introv imp; repeat introv; tcsp.
Qed.


(**

   Differential identity --- see Figure 3, Section 5.1

   (x)' = x'

 *)
Definition differential_identity_axiom : Formula :=
  KFequal
    (KTdifferential tvarx)
    tvarxp.

Definition differential_identity_rule : rule := MkRule [] differential_identity_axiom.

Lemma differential_identity_sound : rule_true differential_identity_rule.
Proof.
  introv imp; repeat introv; simpl in *; clear imp.
  autorewrite with core.
  fold assignx.
  erewrite Derive_ext;[|introv;autorewrite with core;reflexivity].
  rewrite Derive_id.
  autorewrite with core; auto.
Qed.

(*
Lemma diff_diff :
  forall t I v,
    dynamic_semantics_term I v (KTdifferential (KTdifferential t)) = R0.
Proof.
  introv; simpl.
  erewrite big_sum_ext;
    [|introv i;apply Rmult_eq_compat_l;
      apply Derive_ext;introv;
      apply big_sum_ext;introv j;
      rewrite upd_state_diff;[|intro xx; inversion xx];
      reflexivity
    ].
  Focus 2.
  SearchAbout (_ * _ = _ * _)%R.
Qed.
 *)


(*
(**

   ((x)')' = 0

 *)
Definition prime_prime_axiom : Formula :=
  KFequal
    (KTdifferential (KTdifferential tvarx))
    (KTnumber 0).

Definition prime_prime_rule : rule := MkRule [] prime_prime_axiom.

Lemma prime_prime_sound : rule_true prime_prime_rule.
Proof.
  introv imp; repeat introv; simpl in *; clear imp.
  autorewrite with core.
  fold assignx.
  erewrite Derive_ext;
    [|introv;
      rewrite upd_state_diff;[|intro xx; inversion xx];
      autorewrite with core;
      erewrite Derive_ext;
      [|introv;autorewrite with core;reflexivity];
      rewrite Derive_id;
      autorewrite with core;
      reflexivity
    ].
  rewrite Derive_const.
  autorewrite with core.
  auto.
Qed.


(**

   (x')' = 0

 *)
Definition prime_diff_axiom : Formula :=
  KFequal
    (KTdifferential tvarxp)
    (KTnumber 0).

Definition prime_diff_rule : rule := MkRule [] prime_diff_axiom.

Definition prime_diff_sound : rule_true prime_diff_rule.
Proof.
  introv imp; repeat introv; simpl in *; clear imp; auto.
Qed.
*)




(**

  Differential plus --- see Figure 3, Section 5.1

      (f(x)+g(x))'=f(x)'+g(x)'

 *)
Definition differential_plus_axiom : Formula :=
  KFequal
    (KTdifferential
       (KTplus
          (Fof1 funcf tvarx)
          (Fof1 funcg tvarx)
       )
    )
    (KTplus
       (KTdifferential (Fof1 funcf tvarx))
       (KTdifferential (Fof1 funcg tvarx))
    ).
Definition differential_plus_rule : rule := MkRule [] differential_plus_axiom.

Lemma differential_plus_sound : rule_true differential_plus_rule.
Proof.
  introv imp. simpl in *. clear imp.
  repeat introv; simpl.
  autorewrite with core.
  rewrite <- Rmult_plus_distr_l.

  unfold term_assignables_nodup; simpl.
  f_equal.

  apply Derive_plus.

  { remember (I (SymbolFunction funcf 1)) as F; simpl in *.
    destruct F as [f cond]; simpl in *; clear HeqF.

    eapply ex_derive_ext.
    {
      introv.
      autorewrite with core.
      reflexivity.
    }
    simpl; eauto 2 with core.
  }

  { remember (I (SymbolFunction funcg 1)) as F; simpl in *.
    destruct F as [f cond]; simpl in *; clear HeqF.

    eapply ex_derive_ext.
    {
      introv.
      autorewrite with core.
      reflexivity.
    }
    simpl; eauto 2 with core.
  }
Qed.


(**

  Differential times --- see Figure 3, Section 5.1

      (f(x)*g(x))'=f(x)'*g(x)'

 *)
Definition differential_times_axiom : Formula :=
  KFequal
    (KTdifferential
       (KTtimes
          (Fof1 funcf tvarx)
          (Fof1 funcg tvarx)
       )
    )
    (KTplus
       (KTtimes
          (KTdifferential (Fof1 funcf tvarx))
          (Fof1 funcg tvarx)
       )
       (KTtimes
          (Fof1 funcf tvarx)
          (KTdifferential (Fof1 funcg tvarx))
       )
    ).

Definition differential_times_rule : rule := MkRule [] differential_times_axiom.

Lemma differential_times_sound : rule_true differential_times_rule.
Proof.
  introv imp. simpl in *. clear imp.
  repeat introv; simpl.
  autorewrite with core.
  rewrite <- Rmult_assoc.
  rewrite (Rmult_comm _ (v (KD assignx))).
  rewrite Rmult_assoc.
  rewrite (Rmult_comm _ (interp_fun_f 1 (I (SymbolFunction funcg 1))
                                      (Vector.cons R (v assignx) 0 (Vector.nil R)))).
  rewrite Rmult_assoc.
  rewrite <- Rmult_plus_distr_l.

  unfold term_assignables_nodup; simpl.
  f_equal.
  rewrite Derive_mult.

  {
    autorewrite with core.
    rewrite <- (Rmult_comm (interp_fun_f 1 (I (SymbolFunction funcg 1)) (VR1 (v assignx)))).
    auto.
  }

  {
    remember (I (SymbolFunction funcf 1)) as F; simpl in *.
    destruct F as [f cond]; simpl in *; clear HeqF.

    eapply ex_derive_ext.
    {
      introv.
      autorewrite with core; reflexivity.
    }
    simpl; eauto 2 with core.
  }

  { remember (I (SymbolFunction funcg 1)) as F; simpl in *.
    destruct F as [f cond]; simpl in *; clear HeqF.

    eapply ex_derive_ext.
    {
      introv.
      autorewrite with core; reflexivity.
    }
    simpl; eauto 2 with core.
  }
Qed.


(**

  Differential compose --- see Figure 3, Section 5.1

  [y:=g(x)][y':=1]((f(g(x)))' = (f(y))' o (g(x))')

 *)
Definition differential_compose_axiom : Formula :=
  KFbox
    (KPassign assigny (Fof1 funcg tvarx))
    (KFbox
       (KPassign assignyp 1)
       (KFequal
          (KTdifferential (Fof1 funcf (Fof1 funcg tvarx)))
          (KTtimes
          (KTdifferential (Fof1 funcf tvary))
          (KTdifferential (Fof1 funcg tvarx))
          )
       )
    ).

Definition differential_compose_rule : rule := MkRule [] differential_compose_axiom.

Lemma differential_compose_sound : rule_true differential_compose_rule.
Proof.
  introv imp. simpl in *. clear imp.
  repeat introv; simpl.

  introv dse1 dse2.
  autorewrite with core. simpl in *.

  unfold differ_state_except in *.
  simpl; autorewrite with core.
  destruct dse1 as [H1 H2].
  destruct dse2 as [H3 H4].

  assert (w0 (KD assigny) = R1) as q1 by tcsp.
  rewrite q1; clear q1.
  autorewrite with core.

  symmetry; rewrite Rmult_comm; symmetry.
  rewrite Rmult_assoc.
  f_equal.

  remember (I (SymbolFunction funcf 1)) as F; simpl in *;
    destruct F as [f condf]; simpl in *; clear HeqF.

  remember (I (SymbolFunction funcg 1)) as G; simpl in *;
    destruct G as [g condg]; simpl in *.

  (* some cleaning up *)
  fold assignx in *.
  fold assigny in *.
  erewrite Derive_ext;
    [|introv;autorewrite with core;reflexivity].
  symmetry.
  erewrite Derive_ext;
    [|introv;autorewrite with core;reflexivity].
  erewrite (Derive_ext _ _ (w0 assigny));
    [|introv;autorewrite with core;reflexivity].
  symmetry.
  (* done with cleaning up *)

  pose proof (Derive_comp
                (fun r => f (Vector.cons R r 0 (Vector.nil R)))
                (fun r => g (Vector.cons R r 0 (Vector.nil R))))
    as q; simpl in q.
  rewrite q; clear q; eauto 2 with core.

  f_equal.
  rewrite <- H3;[|intro xx;inversion xx].
  rewrite <- H1;[|intro xx;inversion xx].
  try fold assignx; rewrite <- H2.
  rewrite <- H3;[|intro xx;inversion xx].
  auto.
Qed.



(* I can't find what DS stands for *)
(**

  DS--- see Figure 3, Section 5.1

  [x'=f & q(x)]p(x) <-> ∀t≥0.((∀0≤s≤t.q(x+fs)) -> [x:=x+ft]p(x))

 *)
Definition DS_axiom : Formula :=
  KFequiv
    (KFbox
       (KPodeSystem
          (ODEsing varx tfuncf)
          (Pof1 predq tvarx)
       )
       (Pof1 predp tvarx)
    )
    (KFforallVars
       [vart]
       (KFimply
          (KFgreaterEqual tvart term0)
          (KFimply
             (KFforallVars
                [vars]
                (KFimply
                   (KFand (KFgreaterEqual tvars term0) (KFlessEqual tvars tvart))
                   (Pof1 predq (KTplus tvarx (KTtimes tfuncf tvars)))
                )
             )
             (KFbox
                (KPassign
                   assignx
                   (KTplus tvarx (KTtimes tfuncf tvart))
                )
                (Pof1 predp tvarx)
             )
          )
       )
    ).

Definition DS_rule : rule := MkRule [] DS_axiom.

Lemma DS_axiom_sound : rule_true DS_rule.
Proof.
  introv imp. simpl in *. clear imp.
  repeat introv; simpl.

  remember (interp_fun_f 0 (I (SymbolFunction funcf 0)) (Vector.nil R)) as F.
  hide_hyp HeqF.

  split.

  {
    introv h len upd cond diff.

    repeat (destruct rs; simpl in *; ginv).
    autorewrite with core in *.

    (* anything that's greater or equal to 0 works *)
    pose proof (cond [r]) as q; simpl in q.
    hide_hyp cond.
    (* we keep cond---it might be useful *)
    autorewrite with core in q.
    rewrite upd_state_diff in q;[|intro xx; inversion xx];[].
    autorewrite with core in q.
    repeat (autodimp q hyp); dands; auto; try (complete (apply Rle_refl)).
    repeat (rewrite upd_state_diff in q;[|intro xx; inversion xx];[]).
    destruct diff as [diff1 diff2].
    repeat (rewrite upd_state_diff in diff2;[|intro xx; inversion xx];[]).
    fold assignx in *.
    fold assignxp in *.
    fold assignt in *.

    apply Rge_le in upd.

    pose proof (h (fun x : KAssignable =>
                     if KAssignable_dec assignt x
                     then v assignt
                     else if KAssignable_dec assignxp x
                          then F
                          else w x)) as z; clear h.
    Opaque KAssignable_dec. (* otherwise things get unfolded too much here *)
    simpl in z.
    repeat (dest_cases w;[]).
    apply z; clear z.

    exists (mk_preal r upd).
    exists(fun r (x : KAssignable) =>
             if KAssignable_dec assignx x
             then (v assignx + F * r)%R
             else if KAssignable_dec assignxp x
                  then F
                  else v x).
    simpl.
    autorewrite with core.
    repeat (dest_cases w;[]); GC.

    dands;[| |introv j;dands|introv;dands]; auto; simpl in *;
      repndors; try (subst v0); tcsp;
        fold assignx in *; repeat (dest_cases w; GC);
          try (complete (destruct n2; auto)).

    { introv ni; dest_cases w.
      simpl in *; apply not_or in ni; repnd; GC.
      dest_cases w. }

    { apply functional_extensionality; introv.
      repeat (dest_cases w); subst; ginv.
      rewrite <- diff1; auto.
      rewrite upd_state_diff; auto. }

    { apply @ex_derive_plus;[apply ex_derive_const|].
      apply ex_derive_mult;[apply @ex_derive_const|].
      apply @ex_derive_id. }

    { rewrite Derive_plus;
        [|apply @ex_derive_const
         |apply ex_derive_mult;[apply @ex_derive_const|];
          apply @ex_derive_id
        ].
      rewrite Derive_const; autorewrite with core.
      rewrite Derive_mult;[|apply @ex_derive_const|apply @ex_derive_id].
      rewrite Derive_const; autorewrite with core.
      rewrite Derive_id; autorewrite with core.
      auto. }

    { show_hyp cond.
      pose proof (cond [preal_r (preal_upto_preal _ zeta)]) as z.
      simpl in z.
      autorewrite with core in z.
      rewrite upd_state_diff in z;[|intro xx; inversion xx];[].
      autorewrite with core in z.
      repeat (autodimp z hyp); dands; auto;
        try (complete (apply Rle_refl));
        try (complete (apply preal_upto_cond; auto));
        try (complete (apply Rle_ge; apply preal_upto_are_pos)). }

    { introv ni; simpl in ni; repeat (apply not_or in ni; repnd); GC.
      dest_cases w. }
  }

  (******************************************************************************)
  {
    introv interp ode; exrepnd; subst.
    pose proof (interp [preal_r r] eq_refl) as itrp.
    hide_hyp interp.
    simpl in *.
    autorewrite with core in itrp.
    autodimp itrp hyp.
    { destruct r; simpl; apply Rle_ge; auto. }
    rewrite upd_state_diff in itrp;[|intro xx; inversion xx].
    autodimp itrp hyp.

    { introv len updle.
      repeat (destruct rs; simpl in *; ginv).
      autorewrite with core in *.
      repnd.
      rewrite upd_state_diff in updle;[|intro xx;inversion xx].
      autorewrite with core in updle.
      rewrite upd_state_diff;[|intro xx;inversion xx].
      rewrite upd_state_diff;[|intro xx;inversion xx].

      fold assignx in *.
      unfold equal_states_except in *.
      pose proof (ode0 assignx) as phi0.
      autodimp phi0 hyp. unfold not. unfold In. introv HH. destruct HH. inversion H. auto.
      apply Rge_le in updle0.

      pose proof (ode1 (mk_preal_upto r (mk_preal r0 updle0) updle)) as kk. simpl in kk. repnd.

      rewrite phi0.

      match goal with
      | [ H : I _ ?x |- I _ ?y ] => assert (x = y) as xx;[|rewrite <- xx;auto]
      end.
      f_equal.
      apply (evolve_from_initial F r0 (fun t => phi t assignx)); auto.
      introv.

      pose proof (ode3 (ex_preal_upto_trans
                          r
                          (mk_preal_upto r (mk_preal r0 updle0) updle)
                          x) assignx) as q; simpl in q.
      autodimp q hyp.
      dest_cases w; ginv; GC.
      repnd; dands; auto.
      fold assignx in *.
      rewrite <- q1; auto.
      rewrite q; auto.
    }

    {
      fold assignx in *.
      pose proof (itrp (fun x =>
                          if KAssignable_dec assignx x
                          then phi r x
                          else upd_state v (KAssignVar vart) r x)) as q;
        simpl in q.
      dest_cases w; GC.
      apply q.
      unfold differ_state_except.
      dest_cases w; GC.

      dands.

      { introv d; dest_cases w. }

      unfold equal_states_except in ode0.
      pose proof (ode0 assignx) as phi0.
      autodimp phi0 hyp; simpl;[intro xx; repndors; tcsp; inversion xx|].
      rewrite phi0.

      apply (evolve_from_initial F r (fun t => phi t assignx)); auto;
        try (complete (destruct r; simpl; auto)).
      introv.

      pose proof (ode3 x assignx) as z; simpl in z.
      autodimp z hyp.
      dest_cases w; GC.
      repnd; dands; auto.
      fold assignx in *.
      rewrite <- z1; auto.
      rewrite z; auto.
    }
  }
Qed.


(**

  Differential ghosts (left to right direction only) --- see Figure 3, Section 5.1

      [x'=f(x) & q(x)]p(x)
      ->
      ∃y.[x'=f(x),y'=a(x)*y+b(x) & q(x)]p(x)

 *)
Definition differential_ghosts_lr_axiom : Formula :=
  KFimply
    (KFbox
       (KPodeSystem
          (ODEsing varx (Fof1 funcf tvarx))
          (Pof1 predq tvarx)
       )
       (Pof1 predp tvarx)
    )
    (KFexistsVars
       [vary]
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
         (Pof1 predp tvarx)
       )
    ).

Definition differential_ghosts_lr_rule : rule := MkRule [] differential_ghosts_lr_axiom.

Lemma differential_ghosts_lr_axiom_sound :
  rule_true differential_ghosts_lr_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv; simpl.
  intro h.

  exists [v assigny]; simpl; dands; auto.
  introv q; exrepnd; subst.
  autorewrite with core in *.

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


(* Admitted for now.  Is that what we want? *)
Definition PicardLindelof :=
  forall (r : R) (Fa Fb : R (* preal_upto r *) -> R) (d : R),
    (forall z : preal_upto r, ex_derive Fa z /\ ex_derive Fb z)
    ->
    exists Y,
      Y 0%R = d
      /\
      forall t : preal_upto r,
        ex_derive_R Y t
        /\
        Derive Y t
        = ((Fa t * Y t) + Fb t)%R.


(**

  Differential ghosts --- see Figure 3, Section 5.1

      [x'=f(x) & q(x)]p(x)
      <->
      ∃y.[x'=f(x),y'=a(x)*y+b(x) & q(x)]p(x)

 *)
Definition differential_ghosts_axiom : Formula :=
  KFequiv
    (KFbox
       (KPodeSystem
          (ODEsing varx (Fof1 funcf tvarx))
          (Pof1 predq tvarx)
       )
       (Pof1 predp tvarx)
    )
    (KFexistsVars
       [vary]
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
         (Pof1 predp tvarx)
       )
    ).

Definition differential_ghosts_rule : rule := MkRule [] differential_ghosts_axiom.

Lemma differential_ghosts_axiom_sound :
  PicardLindelof
  -> rule_true differential_ghosts_rule.
Proof.
  introv pl imp. simpl in *. clear imp.
  repeat introv; simpl.
  split; intro h.

  { apply differential_ghosts_lr_axiom_sound; simpl; tcsp. }

  {
    introv q.
    exrepnd; subst.
    repeat (destruct rs; simpl in *; ginv).
    autorewrite with core in *.

    fold assignyp in *.
    fold assignxp in *.
    fold assigny  in *.
    fold assignx  in *.

    remember (interp_fun_f 1 (I (SymbolFunction funcfa 1))) as Fa.
    remember (interp_fun_f 1 (I (SymbolFunction funcfb 1))) as Fb.

    rename r0 into d.

    pose proof (pl
                  r
                  (fun t => Fa (VR1 (phi t assignx)))
                  (fun t => Fb (VR1 (phi t assignx)))
                  d) as sol.
    repeat (autodimp sol hyp).

    { introv; dands.

      { subst Fa.
        remember (I (SymbolFunction funcfa 1)) as Fa; simpl in Fa.
        destruct Fa as [Fa cond]; simpl in *; clear HeqFa.

        apply (ex_derive_comp
                 (fun t => Fa (VR1 t))
                 (fun t => phi t assignx)
                 z); simpl; eauto 2 with core.
        pose proof (q3 z varx) as q; simpl in *.
        autodimp q hyp; dest_cases w.
      }

      { subst Fb.
        remember (I (SymbolFunction funcfb 1)) as Fb; simpl in Fb.
        destruct Fb as [Fb cond]; simpl in *; clear HeqFb.

        apply (ex_derive_comp
                 (fun t => Fb (VR1 t))
                 (fun t => phi t assignx)
                 z); simpl; eauto 2 with core.
        pose proof (q3 z varx) as q; simpl in *.
        autodimp q hyp; dest_cases w.
      }
    }

    exrepnd.

    pose proof (h0 (fun a =>
                      if KAssignable_dec a assigny
                      then Y r
                      else
                        if KAssignable_dec a assignyp
                        then (Fa (VR1 (phi r assignx)) * Y r + Fb (VR1 (phi r assignx)))%R
                        else phi r a)) as z; clear h0; simpl in z.
    repeat (dest_cases w; GC;[]).
    autodimp z hyp.

    exists r (fun r a =>
                if KAssignable_dec a assigny
                then Y r
                else
                  if KAssignable_dec a assignyp
                  then (Fa (VR1 (phi r assignx)) * Y r + Fb (VR1 (phi r assignx)))%R
                  else phi r a).
    repeat (dest_cases w; GC;[]).
    dands; auto.

    { unfold ode_footprint_diff; simpl.
      introv i; simpl in i.
      repeat (apply not_or in i; repnd); GC.
      unfold upd_state.
      repeat (dest_cases w; subst; tcsp).
      apply q0; simpl; tcsp. }

    { introv i; simpl in *.
      repndors; subst; tcsp; repeat (dest_cases w; GC);
        try (complete (match goal with | [ H : _ <> _ |- _ ] => destruct H; auto;fail end));
        autorewrite with core in *;
        dands; auto;
          try (complete (pose proof (sol0 zeta) as q; repnd; auto));
          try (complete (pose proof (q3 zeta assignx) as xx; simpl in xx;
                         autodimp xx hyp; dest_cases w)).
    }

    { introv.
      pose proof (q1 zeta) as h; repnd.
      dands; auto.

      unfold ode_footprint, ode_footprint_diff; simpl.
      introv i.
      repeat (apply not_or in i; repnd); GC.
      repeat (dest_cases w; GC).
      apply h; simpl; tcsp. }
  }
Qed.




(**

  This rule is not mentioned in the paper:

  [c,d & P]Q <-> [d,c & P]Q

 *)
Definition ode_comm : Formula :=
  KFequiv
    (KFbox
       (KPodeSystem (ODEprod (ODEconst odec) (ODEconst oded)) quantP)
       quantQ)
    (KFbox
       (KPodeSystem (ODEprod (ODEconst oded) (ODEconst odec)) quantP)
       quantQ).

Definition ode_comm_rule : rule := MkRule [] ode_comm.

Lemma ode_comm_locally_sound : rule_locally_sound ode_comm_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv; simpl.
  split; intro h; introv z; exrepnd; subst; apply h; exists r phi; dands; auto.

  { introv i; apply z0; intro j; destruct i; apply eqset_ode_footprint_diff_prod;
      apply eqset_ode_footprint_diff_prod in j; allrw in_app_iff; tcsp. }

  { eapply dynamic_semantics_ode_comm; eauto. }

  { introv.
    pose proof (z1 zeta) as q.
    repnd; dands; auto.
    introv i; apply q; intro j; destruct i; apply eqset_ode_footprint_prod;
      apply eqset_ode_footprint_prod in j; allrw in_app_iff; tcsp. }

  { introv i; apply z0; intro j; destruct i; apply eqset_ode_footprint_diff_prod;
      apply eqset_ode_footprint_diff_prod in j; allrw in_app_iff; tcsp. }

  { eapply dynamic_semantics_ode_comm; eauto. }

  { introv.
    pose proof (z1 zeta) as q.
    repnd; dands; auto.
    introv i; apply q; intro j; destruct i; apply eqset_ode_footprint_prod;
      apply eqset_ode_footprint_prod in j; allrw in_app_iff; tcsp. }
Qed.

Lemma ode_comm_sound : rule_true ode_comm_rule.
Proof.
  apply rule_locally_sound_implies_true.
  apply ode_comm_locally_sound.
Qed.
