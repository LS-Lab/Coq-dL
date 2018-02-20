(*

  Copyright 2016 University of Luxembourg
  Copyright 2017 University of Luxembourg
  Copyright 2018 University of Luxembourg

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
Require Import differential.
Require Import integral.



(* !!MOVE *)
Lemma var_not_in_ode_footprint_diff :
  forall I v ode, ~ In (KAssignVar v) (ode_footprint_diff I ode).
Proof.
  unfold ode_footprint_diff.
  introv i.
  apply in_map_iff in i; exrepnd; ginv.
Qed.


(**

  DI for KFgreaterEqual

  (p(x) -> g(x)≥h(x))
  -> [x'=f(x), c & p(x)](g(x)'≥h(x)')
  -> [x'=f(x), c & p(x)]g(x)≥h(x)

 *)
Definition DI_ge_axiom : Formula :=
  KFimply
    (KFimply (Pof1 predp tvarx) (KFgreaterEqual (Fof1 funcg tvarx) (Fof1 funch tvarx)))
    (KFimply
       (KFbox
          (KPodeSystem
             (ODEprod
                (ODEsing varx (Fof1 funcf tvarx))
                (ODEconst odec))
             (Pof1 predp tvarx))
          (KFgreaterEqual
             (KTdifferential (Fof1 funcg tvarx))
             (KTdifferential (Fof1 funch tvarx)))
       )
       (KFbox
          (KPodeSystem
             (ODEprod
                (ODEsing varx (Fof1 funcf tvarx))
                (ODEconst odec))
             (Pof1 predp tvarx))
          (KFgreaterEqual
             (Fof1 funcg tvarx)
             (Fof1 funch tvarx)))).

Definition DI_ge_rule : rule := MkRule [] DI_ge_axiom.

Lemma DI_ge_sound : rule_true DI_ge_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv ; simpl.
  introv h1 h2 q.
  exrepnd; subst.
  allrw fold_VR1.

  assert (v assignx = phi 0%R assignx) as xx.
  { apply (q0 assignx); introv xx.
    apply var_not_in_ode_footprint_diff in xx; auto. }

  remember (I (SymbolFunction funcg 1)) as Fg; simpl in Fg.
  remember (I (SymbolFunction funch 1)) as Fh; simpl in Fh.
  destruct Fg as [Fg condg].
  destruct Fh as [Fh condh].
  simpl in *.
  hide_hyp HeqFh.
  hide_hyp HeqFg.

  fold assignx in *.
  apply Rle_ge.

  pose proof (q1 (mk_preal_upto r (mk_preal 0 (Rle_refl 0)) (preal_cond r))) as cz.
  simpl in cz; repnd.
  rewrite <- xx in cz0.

  apply Rge_le in h1; auto.

  assert (forall z,
             (0 <= z)%R
             -> (z <= r)%R
             -> (Derive (fun t : R => Fh (VR1 (phi t assignx))) z
                 <=
                 Derive (fun t : R => Fg (VR1 (phi t assignx))) z)%R) as gtd.

  {
    introv le0z lezr.
    pose proof (h2 (phi (mk_preal_upto r (mk_preal z le0z) lezr))) as zz; clear h2.
    autodimp zz hyp; simpl in *.

    {
      exists (mk_preal z le0z) phi; simpl; dands; auto.

      {
        Opaque KAssignable_dec. (* otherwise things get unfolded too much here *)
        introv i; simpl in *.
        pose proof (q3 (ex_preal_upto_trans
                          r
                          (mk_preal_upto r (mk_preal z le0z) lezr)
                          zeta) v0) as q; simpl in q; tcsp.
      }

      {
        introv.
        pose proof (q1 (ex_preal_upto_trans
                          r
                          (mk_preal_upto r (mk_preal z le0z) lezr)
                          zeta)) as q; simpl in q; tcsp.
      }
    }

    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    apply Rge_le in zz.
    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].

    autorewrite with core in zz.

    pose proof (differential_space_time
                  varx I r phi z
                  (Fof1 funcg tvarx)) as e1.
    repeat (autodimp e1 hyp); eauto with core;
      try (complete (destruct r; simpl; auto));
      try (complete (apply Rle_refl)).

    {
      introv; simpl.
      pose proof (q3 zeta varx) as h; simpl in h.
      autodimp h hyp; dest_cases w.
    }

    simpl in e1.
    autorewrite with core in e1.
    rewrite <- HeqFg in e1; simpl in *.
    erewrite Derive_ext in e1;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    fold assignx in *.
    rewrite e1 in zz; clear e1.

    pose proof (differential_space_time
                  varx I r phi z
                  (Fof1 funch tvarx)) as e2.
    repeat (autodimp e2 hyp); eauto with core; simpl in *;
      try (complete (destruct r; simpl; auto));
      try (complete (apply Rle_refl)).

    {
      introv; simpl.
      pose proof (q3 zeta varx) as h.
      simpl in h; autodimp h hyp; dest_cases w.
    }

    simpl in e2.
    autorewrite with core in e2.
    rewrite <- HeqFh in e2; simpl in *.
    erewrite Derive_ext in e2;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    fold assignx in *.
    rewrite e2 in zz; clear e2.

    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    apply Rle_ge in zz.
    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    apply Rge_le in zz.
    auto.
  }
  clear h2.

  apply Rminus_le_0 in h1.
  apply Rminus_le_0.

  assert (forall z : R,
             (0 <= z)%R ->
             (z <= r)%R ->
             (0 <=
              Derive (fun t : R => Fg (VR1 (phi t assignx))) z * r
              - Derive (fun t : R => Fh (VR1 (phi t assignx))) z * r)%R) as gtd'.
  { introv le0z lezr.
    rewrite <- Rmult_minus_distr_r.
    apply Rmult_le_pos; auto.
    rewrite <- Rminus_le_0.
    apply gtd; auto. }
  clear gtd.

  pose proof (MVT_gen
                (fun r => (Fg (VR1 (phi r assignx)) - Fh (VR1 (phi r assignx)))%R)
                0 r
                (fun r =>
                   (Derive (fun t : R => Fg (VR1 (phi t assignx))) r
                    - Derive (fun t : R => Fh (VR1 (phi t assignx))) r)%R)) as mvt.
  rewrite Rmin_left in mvt; auto.
  rewrite Rmax_right in mvt; auto.
  simpl in mvt.
  repeat (autodimp mvt hyp).

  {
    introv ltx.
    destruct ltx as [lt0x ltxr].
    apply @is_derive_minus; apply Derive_correct.

    {
      apply (ex_derive_comp
               (fun t => Fg (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      apply Rlt_le in lt0x.
      apply Rlt_le in ltxr.
      pose proof (q3 (mk_preal_upto r (mk_preal x lt0x) ltxr) varx) as q; simpl in q.
      autodimp q hyp; dest_cases w.
    }

    {
      apply (ex_derive_comp
               (fun t => Fh (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      apply Rlt_le in lt0x.
      apply Rlt_le in ltxr.
      pose proof (q3 (mk_preal_upto r (mk_preal x lt0x) ltxr) varx) as q; simpl in q.
      autodimp q hyp; dest_cases w.
    }
  }

  {
    introv lex.
    destruct lex as [le0x lexr].

    unfold continuity_pt.
    apply (cont_deriv
             _
             (fun r =>
                (Derive (fun t : R => Fg (VR1 (phi t assignx))) r
                 - Derive (fun t : R => Fh (VR1 (phi t assignx))) r)%R)).
    apply derivable_pt_lim_D_in.
    apply is_derive_Reals.
    apply @is_derive_minus; apply Derive_correct.

    {
      apply (ex_derive_comp
               (fun t => Fg (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      pose proof (q3 (mk_preal_upto r (mk_preal x le0x) lexr) varx) as q; simpl in q.
      autodimp q hyp; dest_cases w.
    }

    {
      apply (ex_derive_comp
               (fun t => Fh (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      pose proof (q3 (mk_preal_upto r (mk_preal x le0x) lexr) varx) as q; simpl in q.
      autodimp q hyp; dest_cases w.
    }
  }

  {
    exrepnd.
    autorewrite with core in mvt0.
    repeat (rewrite <- xx in mvt0).
    apply subtract_both_side_equ in mvt0.
    rewrite mvt0; clear mvt0.

    pose proof (gtd' c) as q; clear gtd'; repeat (autodimp q hyp).
    rewrite Rmult_minus_distr_r.
    apply Rplus_le_le_0_compat; auto.
  }
Qed.


(**

  DI for KFgreaterEqual (version with c only)

  (p(x) -> g(x)≥h(x))
  -> [c & p(x)](g(x)'≥h(x)')
  -> [c & p(x)]g(x)≥h(x)

 *)
Definition DI_ge_c_axiom : Formula :=
  KFimply
    (KFimply (Pof1 predp tvarx) (KFgreaterEqual (Fof1 funcg tvarx) (Fof1 funch tvarx)))
    (KFimply
       (KFbox
          (KPodeSystem
             (ODEconst odec)
             (Pof1 predp tvarx))
          (KFgreaterEqual
             (KTdifferential (Fof1 funcg tvarx))
             (KTdifferential (Fof1 funch tvarx)))
       )
       (KFbox
          (KPodeSystem
             (ODEconst odec)
             (Pof1 predp tvarx))
          (KFgreaterEqual
             (Fof1 funcg tvarx)
             (Fof1 funch tvarx)))).

Definition DI_ge_c_rule : rule := MkRule [] DI_ge_c_axiom.

Lemma DI_ge_c_sound : rule_true DI_ge_c_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv ; simpl.
  introv h1 h2 q.
  exrepnd; subst.
  allrw fold_VR1.

  assert (v assignx = phi 0%R assignx) as xx.
  { apply (q0 assignx); introv xx.
    apply var_not_in_ode_footprint_diff in xx; auto. }

  remember (I (SymbolFunction funcg 1)) as Fg; simpl in Fg.
  remember (I (SymbolFunction funch 1)) as Fh; simpl in Fh.
  destruct Fg as [Fg condg].
  destruct Fh as [Fh condh].
  simpl in *.
  hide_hyp HeqFh.
  hide_hyp HeqFg.

  fold assignx in *.
  apply Rle_ge.

  pose proof (q1 (mk_preal_upto r (mk_preal 0 (Rle_refl 0)) (preal_cond r))) as cz.
  simpl in cz; repnd.
  rewrite <- xx in cz0.

  pose proof (q1 (mk_preal_upto r r (Rle_refl r))) as cr.
  simpl in cr; repnd.

  apply Rge_le in h1; auto;[].

  destruct (in_dec KAssignable_dec varx (interp_ode_bv (I (SymbolODE odec)))) as [d|d];
    [|assert (~ In assignx (ode_footprint I (ODEconst odec))) as ni;
      [introv ix;
       unfold ode_footprint in ix; apply in_app_iff in ix; repndors; simpl in ix; tcsp;
       apply var_not_in_ode_footprint_diff in ix; auto|];
      pose proof (cr assignx ni) as ex;
      rewrite <- ex; clear ex;
      assert (R0 = 0%R) as zz by auto; rewrite zz; clear zz;
      rewrite <- xx; auto];[].

  assert (forall z,
             (0 <= z)%R
             -> (z <= r)%R
             -> (Derive (fun t : R => Fh (VR1 (phi t assignx))) z
                 <=
                 Derive (fun t : R => Fg (VR1 (phi t assignx))) z)%R) as gtd.

  {
    introv le0z lezr.
    pose proof (h2 (phi (mk_preal_upto r (mk_preal z le0z) lezr))) as zz; clear h2.
    autodimp zz hyp; simpl in *.

    {
      exists (mk_preal z le0z) phi; simpl; dands; auto.

      {
        Opaque KAssignable_dec. (* otherwise things get unfolded too much here *)
        introv i; simpl in *.
        pose proof (q3 (ex_preal_upto_trans
                          r
                          (mk_preal_upto r (mk_preal z le0z) lezr)
                          zeta) v0) as q; simpl in q; tcsp.
      }

      {
        introv.
        pose proof (q1 (ex_preal_upto_trans
                          r
                          (mk_preal_upto r (mk_preal z le0z) lezr)
                          zeta)) as q; simpl in q; tcsp.
      }
    }

    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    apply Rge_le in zz.
    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].

    autorewrite with core in zz.

    pose proof (differential_space_time
                  varx I r phi z
                  (Fof1 funcg tvarx)) as e1.
    repeat (autodimp e1 hyp); eauto with core;
      try (complete (destruct r; simpl; auto));
      try (complete (apply Rle_refl)).

    {
      introv; simpl.
      pose proof (q3 zeta varx) as h; simpl in h.
      autodimp h hyp; tcsp.
    }

    simpl in e1.
    autorewrite with core in e1.
    rewrite <- HeqFg in e1; simpl in *.
    erewrite Derive_ext in e1;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    fold assignx in *.
    rewrite e1 in zz; clear e1.

    pose proof (differential_space_time
                  varx I r phi z
                  (Fof1 funch tvarx)) as e2.
    repeat (autodimp e2 hyp); eauto with core; simpl in *;
      try (complete (destruct r; simpl; auto));
      try (complete (apply Rle_refl)).

    {
      introv; simpl.
      pose proof (q3 zeta varx) as h.
      simpl in h; autodimp h hyp; tcsp.
    }

    simpl in e2.
    autorewrite with core in e2.
    rewrite <- HeqFh in e2; simpl in *.
    erewrite Derive_ext in e2;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    fold assignx in *.
    rewrite e2 in zz; clear e2.

    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    apply Rle_ge in zz.
    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    apply Rge_le in zz.
    auto.
  }
  clear h2.

  apply Rminus_le_0 in h1.
  apply Rminus_le_0.

  assert (forall z : R,
             (0 <= z)%R ->
             (z <= r)%R ->
             (0 <=
              Derive (fun t : R => Fg (VR1 (phi t assignx))) z * r
              - Derive (fun t : R => Fh (VR1 (phi t assignx))) z * r)%R) as gtd'.
  { introv le0z lezr.
    rewrite <- Rmult_minus_distr_r.
    apply Rmult_le_pos; auto.
    rewrite <- Rminus_le_0.
    apply gtd; auto. }
  clear gtd.

  pose proof (MVT_gen
                (fun r => (Fg (VR1 (phi r assignx)) - Fh (VR1 (phi r assignx)))%R)
                0 r
                (fun r =>
                   (Derive (fun t : R => Fg (VR1 (phi t assignx))) r
                    - Derive (fun t : R => Fh (VR1 (phi t assignx))) r)%R)) as mvt.
  rewrite Rmin_left in mvt; auto.
  rewrite Rmax_right in mvt; auto.
  simpl in mvt.
  repeat (autodimp mvt hyp).

  {
    introv ltx.
    destruct ltx as [lt0x ltxr].
    apply @is_derive_minus; apply Derive_correct.

    {
      apply (ex_derive_comp
               (fun t => Fg (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      apply Rlt_le in lt0x.
      apply Rlt_le in ltxr.
      pose proof (q3 (mk_preal_upto r (mk_preal x lt0x) ltxr) varx) as q; simpl in q.
      autodimp q hyp; tcsp.
    }

    {
      apply (ex_derive_comp
               (fun t => Fh (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      apply Rlt_le in lt0x.
      apply Rlt_le in ltxr.
      pose proof (q3 (mk_preal_upto r (mk_preal x lt0x) ltxr) varx) as q; simpl in q.
      autodimp q hyp; tcsp.
    }
  }

  {
    introv lex.
    destruct lex as [le0x lexr].

    unfold continuity_pt.
    apply (cont_deriv
             _
             (fun r =>
                (Derive (fun t : R => Fg (VR1 (phi t assignx))) r
                 - Derive (fun t : R => Fh (VR1 (phi t assignx))) r)%R)).
    apply derivable_pt_lim_D_in.
    apply is_derive_Reals.
    apply @is_derive_minus; apply Derive_correct.

    {
      apply (ex_derive_comp
               (fun t => Fg (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      pose proof (q3 (mk_preal_upto r (mk_preal x le0x) lexr) varx) as q; simpl in q.
      autodimp q hyp; tcsp.
    }

    {
      apply (ex_derive_comp
               (fun t => Fh (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      pose proof (q3 (mk_preal_upto r (mk_preal x le0x) lexr) varx) as q; simpl in q.
      autodimp q hyp; tcsp.
    }
  }

  {
    exrepnd.
    autorewrite with core in mvt0.
    repeat (rewrite <- xx in mvt0).
    apply subtract_both_side_equ in mvt0.
    rewrite mvt0; clear mvt0.

    pose proof (gtd' c) as q; clear gtd'; repeat (autodimp q hyp).
    rewrite Rmult_minus_distr_r.
    apply Rplus_le_le_0_compat; auto.
  }
Qed.



(**

  DI for KFgreaterEqual (instance for g(x) = (x)'

  (p(x) -> x≥h(x))
  -> [x'=f(x), c & p(x)]x'≥h(x)')
  -> [x'=f(x), c & p(x)]x≥h(x)

 *)
Definition DI_ge_diff_axiom : Formula :=
  KFimply
    (KFimply (Pof1 predp tvarx) (KFgreaterEqual tvarx (Fof1 funch tvarx)))
    (KFimply
       (KFbox
          (KPodeSystem
             (ODEprod
                (ODEsing varx (Fof1 funcf tvarx))
                (ODEconst odec))
             (Pof1 predp tvarx))
          (KFgreaterEqual
             tvarxp
             (KTdifferential (Fof1 funch tvarx)))
       )
       (KFbox
          (KPodeSystem
             (ODEprod
                (ODEsing varx (Fof1 funcf tvarx))
                (ODEconst odec))
             (Pof1 predp tvarx))
          (KFgreaterEqual
             tvarx
             (Fof1 funch tvarx)))).

Definition DI_ge_diff_rule : rule := MkRule [] DI_ge_diff_axiom.

Lemma DI_ge_diff_sound : rule_true DI_ge_diff_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv ; simpl.
  introv h1 h2 q.
  exrepnd; subst.
  allrw fold_VR1.

  assert (v assignx = phi 0%R assignx) as xx.
  { apply (q0 assignx); introv xx.
    unfold ode_footprint_diff in xx; simpl in xx;
      repndors; tcsp; [inversion xx|].
    apply in_map_iff in xx; exrepnd; ginv. }

  remember (I (SymbolFunction funch 1)) as Fh; simpl in Fh.
  destruct Fh as [Fh condh].
  simpl in *.
  hide_hyp HeqFh.

  fold assignx in *.
  apply Rle_ge.

  pose proof (q1 (mk_preal_upto r (mk_preal 0 (Rle_refl 0)) (preal_cond r))) as cz.
  simpl in cz; repnd.
  rewrite <- xx in cz0.

  apply Rge_le in h1; auto.

  assert (forall z,
             (0 <= z)%R
             -> (z <= r)%R
             -> (Derive (fun t : R => Fh (VR1 (phi t assignx))) z
                 <=
                 Derive (fun t : R => phi t assignx) z)%R) as gtd.

  {
    introv le0z lezr.
    pose proof (h2 (phi (mk_preal_upto r (mk_preal z le0z) lezr))) as zz; clear h2.
    autodimp zz hyp; simpl in *.

    {
      exists (mk_preal z le0z) phi; simpl; dands; auto.

      {
        Opaque KAssignable_dec. (* otherwise things get unfolded too much here *)
        introv i; simpl in *.
        pose proof (q3 (ex_preal_upto_trans
                          r
                          (mk_preal_upto r (mk_preal z le0z) lezr)
                          zeta) v0) as q; simpl in q; tcsp.
      }

      {
        introv.
        pose proof (q1 (ex_preal_upto_trans
                          r
                          (mk_preal_upto r (mk_preal z le0z) lezr)
                          zeta)) as q; simpl in q; tcsp.
      }
    }

    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    apply Rge_le in zz.

    autorewrite with core in zz.

    pose proof (differential_space_time
                  varx I r phi z
                  (Fof1 funch tvarx)) as e2.
    repeat (autodimp e2 hyp); eauto with core; simpl in *;
      try (complete (destruct r; simpl; auto));
      try (complete (apply Rle_refl)).

    {
      introv; simpl.
      pose proof (q3 zeta varx) as h.
      simpl in h; autodimp h hyp; dest_cases w.
    }

    simpl in e2.
    autorewrite with core in e2.
    rewrite <- HeqFh in e2; simpl in *.
    erewrite Derive_ext in e2;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    fold assignx in *.
    rewrite e2 in zz; clear e2.

    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].

    pose proof (q3 (mk_preal_upto r (mk_preal z le0z) lezr) varx) as q; simpl in q.
    autodimp q hyp; repnd.

    fold assignx in *.
    rewrite <- q4; auto.
  }
  clear h2.

  apply Rminus_le_0 in h1.
  apply Rminus_le_0.

  assert (forall z : R,
             (0 <= z)%R ->
             (z <= r)%R ->
             (0 <=
              Derive (fun t : R => phi t assignx) z * r
              - Derive (fun t : R => Fh (VR1 (phi t assignx))) z * r)%R) as gtd'.
  { introv le0z lezr.
    rewrite <- Rmult_minus_distr_r.
    apply Rmult_le_pos; auto.
    rewrite <- Rminus_le_0.
    apply gtd; auto. }
  clear gtd.

  pose proof (MVT_gen
                (fun r => (phi r assignx - Fh (VR1 (phi r assignx)))%R)
                0 r
                (fun r =>
                   (Derive (fun t : R => phi t assignx) r
                    - Derive (fun t : R => Fh (VR1 (phi t assignx))) r)%R)) as mvt.
  rewrite Rmin_left in mvt; auto.
  rewrite Rmax_right in mvt; auto.
  simpl in mvt.
  repeat (autodimp mvt hyp).

  {
    introv ltx.
    destruct ltx as [lt0x ltxr].
    apply @is_derive_minus; apply Derive_correct.

    {
      apply (ex_derive_comp
               (fun t => t)
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      { apply ex_derive_id. }
      apply Rlt_le in lt0x.
      apply Rlt_le in ltxr.
      pose proof (q3 (mk_preal_upto r (mk_preal x lt0x) ltxr) varx) as q; simpl in q.
      autodimp q hyp; dest_cases w.
    }

    {
      apply (ex_derive_comp
               (fun t => Fh (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      apply Rlt_le in lt0x.
      apply Rlt_le in ltxr.
      pose proof (q3 (mk_preal_upto r (mk_preal x lt0x) ltxr) varx) as q; simpl in q.
      autodimp q hyp; dest_cases w.
    }
  }

  {
    introv lex.
    destruct lex as [le0x lexr].

    unfold continuity_pt.
    apply (cont_deriv
             _
             (fun r =>
                (Derive (fun t : R => phi t assignx) r
                 - Derive (fun t : R => Fh (VR1 (phi t assignx))) r)%R)).
    apply derivable_pt_lim_D_in.
    apply is_derive_Reals.
    apply @is_derive_minus; apply Derive_correct.

    {
      apply (ex_derive_comp
               (fun t => t)
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      { apply ex_derive_id. }
      pose proof (q3 (mk_preal_upto r (mk_preal x le0x) lexr) varx) as q; simpl in q.
      autodimp q hyp; dest_cases w.
    }

    {
      apply (ex_derive_comp
               (fun t => Fh (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      pose proof (q3 (mk_preal_upto r (mk_preal x le0x) lexr) varx) as q; simpl in q.
      autodimp q hyp; dest_cases w.
    }
  }

  {
    exrepnd.
    autorewrite with core in mvt0.
    repeat (rewrite <- xx in mvt0).
    apply subtract_both_side_equ in mvt0.
    rewrite mvt0; clear mvt0.

    pose proof (gtd' c) as q; clear gtd'; repeat (autodimp q hyp).
    rewrite Rmult_minus_distr_r.
    apply Rplus_le_le_0_compat; auto.
  }
Qed.



(**

  DI for KFgreater

  (p(x)->g(x)>h(x))
  -> [x'=f(x), c & p(x)](g(x)'≥h(x)')
  -> [x'=f(x), c & p(x)]g(x)>h(x)

 *)

Definition DI_gt_axiom : Formula :=
  KFimply
    (KFimply
       (Pof1 predp tvarx)
       (KFgreater (Fof1 funcg tvarx) (Fof1 funch tvarx)))
    (KFimply
       (KFbox
          (KPodeSystem
             (ODEprod
                (ODEsing varx (Fof1 funcf tvarx))
                (ODEconst odec))
             (Pof1 predp tvarx))
          (KFgreaterEqual
             (KTdifferential (Fof1 funcg tvarx))
             (KTdifferential (Fof1 funch tvarx)))
       )
       (KFbox
          (KPodeSystem
             (ODEprod
                (ODEsing varx (Fof1 funcf tvarx))
                (ODEconst odec))
             (Pof1 predp tvarx))
          (KFgreater
             (Fof1 funcg tvarx)
             (Fof1 funch tvarx)))).

Definition DI_gt_rule : rule := MkRule [] DI_gt_axiom.

Lemma DI_gt_sound : rule_true DI_gt_rule.
  Proof.
  introv imp; simpl in *; clear imp.
  repeat introv ; simpl.
  introv h1 h2 q.
  exrepnd; subst.
  allrw fold_VR1.

  assert (v assignx = phi 0%R assignx) as xx.
  { apply (q0 assignx); introv xx.
    unfold ode_footprint_diff in xx; simpl in xx;
      repndors; tcsp; [inversion xx|].
    apply in_map_iff in xx; exrepnd; ginv. }

  remember (I (SymbolFunction funcg 1)) as Fg; simpl in Fg.
  remember (I (SymbolFunction funch 1)) as Fh; simpl in Fh.
  destruct Fg as [Fg condg].
  destruct Fh as [Fh condh].
  simpl in *.
  hide_hyp HeqFh.
  hide_hyp HeqFg.

  fold assignx in *.
  apply Rlt_gt.

  pose proof (q1 (mk_preal_upto r (mk_preal 0 (Rle_refl 0)) (preal_cond r))) as cz.
  simpl in cz; repnd.
  rewrite <- xx in cz0.
  autodimp h1 hyp.

  apply Rgt_lt in h1.

  assert (forall z,
             (0 <= z)%R
             -> (z <= r)%R
             -> (Derive (fun t : R => Fh (VR1 (phi t assignx))) z
                 <=
                 Derive (fun t : R => Fg (VR1 (phi t assignx))) z)%R) as gtd.

  {
    introv le0z lezr.
    pose proof (h2 (phi (mk_preal_upto r (mk_preal z le0z) lezr))) as zz; clear h2.
    autodimp zz hyp; simpl in *.

    {
      exists (mk_preal z le0z) phi; simpl; dands; auto.

      {
        introv i; simpl in *.
        pose proof (q3 (ex_preal_upto_trans
                          r
                          (mk_preal_upto r (mk_preal z le0z) lezr)
                          zeta) v0) as q; simpl in q; tcsp.
      }

      {
        introv.
        pose proof (q1 (ex_preal_upto_trans
                          r
                          (mk_preal_upto r (mk_preal z le0z) lezr)
                          zeta)) as q; simpl in q; tcsp.
      }
    }

    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    apply Rge_le in zz.
    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].

    autorewrite with core in zz.

    pose proof (differential_space_time
                  varx I r phi z
                  (Fof1 funcg tvarx)) as e1.
    repeat (autodimp e1 hyp); eauto with core;
      try (complete (destruct r; simpl; auto));
      try (complete (apply Rle_refl)).

    {
      introv; simpl.
      pose proof (q3 zeta varx) as h; simpl in h.
      autodimp h hyp; dest_cases w.
    }


    simpl in e1.
    autorewrite with core in e1.
    rewrite <- HeqFg in e1; simpl in *.
    erewrite Derive_ext in e1;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    fold assignx in *.
    rewrite e1 in zz; clear e1.

    pose proof (differential_space_time
                  varx I r phi z
                  (Fof1 funch tvarx)) as e2.
    repeat (autodimp e2 hyp); eauto with core; simpl in *;
      try (complete (destruct r; simpl; auto));
      try (complete (apply Rle_refl)).

    {
      introv; simpl.
      pose proof (q3 zeta varx) as h.
      simpl in h; autodimp h hyp; dest_cases w.
    }

    simpl in e2.
    autorewrite with core in e2.
    rewrite <- HeqFh in e2; simpl in *.
    erewrite Derive_ext in e2;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    fold assignx in *.
    rewrite e2 in zz; clear e2.

    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    apply Rle_ge in zz.
    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    apply Rge_le in zz. (* This is not possible :( *)
    auto.
  }
  clear h2.

  apply Rminus_lt_0 in h1.
  apply Rminus_lt_0.

  assert (0 <= r)%R as le0r by auto.

  apply Rle_lt_or_eq_dec in le0r.
  destruct le0r as [lt0r|e];
    [|rewrite <- e;rewrite <- xx; auto].

  assert (forall z : R,
             (0 <= z)%R ->
             (z <= r)%R ->
             (0 <=
              Derive (fun t : R => Fg (VR1 (phi t assignx))) z * r
              - Derive (fun t : R => Fh (VR1 (phi t assignx))) z * r)%R) as gtd'.
  { introv le0z lezr.
    rewrite <- Rmult_minus_distr_r.
    apply Rmult_le_pos; auto.
    rewrite <- Rminus_le_0.
    apply gtd; auto. }
  clear gtd.

  pose proof (MVT_gen
                (fun r => (Fg (VR1 (phi r assignx)) - Fh (VR1 (phi r assignx)))%R)
                0 r
                (fun r =>
                   (Derive (fun t : R => Fg (VR1 (phi t assignx))) r
                    - Derive (fun t : R => Fh (VR1 (phi t assignx))) r)%R)) as mvt.
  rewrite Rmin_left in mvt; auto.
  rewrite Rmax_right in mvt; auto.
  simpl in mvt.
  repeat (autodimp mvt hyp).

  {
    introv ltx.
    destruct ltx as [lt0x ltxr].
    apply @is_derive_minus; apply Derive_correct.

    {
      apply (ex_derive_comp
               (fun t => Fg (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      apply Rlt_le in lt0x.
      apply Rlt_le in ltxr.
      pose proof (q3 (mk_preal_upto r (mk_preal x lt0x) ltxr) varx) as q; simpl in q.
      autodimp q hyp; dest_cases w.
    }

    {
      apply (ex_derive_comp
               (fun t => Fh (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      apply Rlt_le in lt0x.
      apply Rlt_le in ltxr.
      pose proof (q3 (mk_preal_upto r (mk_preal x lt0x) ltxr) varx) as q; simpl in q.
      autodimp q hyp; dest_cases w.
    }
  }

  {
    introv lex.
    destruct lex as [le0x lexr].

    unfold continuity_pt.
    apply (cont_deriv
             _
             (fun r =>
                (Derive (fun t : R => Fg (VR1 (phi t assignx))) r
                 - Derive (fun t : R => Fh (VR1 (phi t assignx))) r)%R)).
    apply derivable_pt_lim_D_in.
    apply is_derive_Reals.
    apply @is_derive_minus; apply Derive_correct.

    {
      apply (ex_derive_comp
               (fun t => Fg (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      pose proof (q3 (mk_preal_upto r (mk_preal x le0x) lexr) varx) as q; simpl in q.
      autodimp q hyp; dest_cases w.
    }

    {
      apply (ex_derive_comp
               (fun t => Fh (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      pose proof (q3 (mk_preal_upto r (mk_preal x le0x) lexr) varx) as q; simpl in q.
      autodimp q hyp; dest_cases w.
    }
  }

  {
    exrepnd.
    autorewrite with core in mvt0.
    repeat (rewrite <- xx in mvt0).
    apply subtract_both_side_equ in mvt0.
    rewrite mvt0; clear mvt0.

    pose proof (gtd' c) as q; clear gtd'; repeat (autodimp q hyp).
    rewrite Rmult_minus_distr_r.
    apply Rplus_lt_le_0_compat; auto.
  }
Qed.


Lemma fold_Fof1 : forall fs t, KTfuncOf fs 1 (VT1 t) = Fof1 fs t.
Proof. auto. Qed.

Lemma fold_Pof1 : forall ps t, KFpredOf ps 1 (VT1 t) = Pof1 ps t.
Proof. auto. Qed.

Lemma Df_formula_valid_iff :
  forall a b,
    (forall I v, dynamic_semantics_formula I a v -> dynamic_semantics_formula I b v)
    -> Df_formula_valid a
    -> Df_formula_valid b.
Proof.
  introv imp df; repeat introv.
  apply imp; apply df; auto.
Qed.

Lemma dynamic_semantics_formula_KFimply_equiv :
  forall I v a b c d,
    (forall I v, dynamic_semantics_formula I a v <-> dynamic_semantics_formula I c v)
    -> (forall I v, dynamic_semantics_formula I b v <-> dynamic_semantics_formula I d v)
    -> (dynamic_semantics_formula I (KFimply a b) v
        <-> dynamic_semantics_formula I (KFimply c d) v).
Proof.
  introv cond1 cond2; split; introv h q;
    apply cond2; apply h; apply cond1; auto.
Qed.

Lemma dynamic_semantics_formula_KFlessEqual_KFgreaterEqual_equiv :
  forall I v a b,
    dynamic_semantics_formula I (KFlessEqual a b) v
    <-> dynamic_semantics_formula I (KFgreaterEqual b a) v.
Proof.
  introv; split; introv h; simpl in *.
  { apply Rle_ge; auto. }
  { apply Rge_le; auto. }
Qed.

Lemma dynamic_semantics_formula_KFless_KFgreater_equiv :
  forall I v a b,
    dynamic_semantics_formula I (KFless a b) v
    <-> dynamic_semantics_formula I (KFgreater b a) v.
Proof.
  introv; split; introv h; simpl in *.
  { apply Rlt_gt; auto. }
  { apply Rgt_lt; auto. }
Qed.


Lemma dynamic_semantics_formula_KFbox_equiv :
  forall I v p1 p2 f1 f2,
    (forall I v w, dynamic_semantics_program I p1 v w <-> dynamic_semantics_program I p2 v w)
    -> (forall I v, dynamic_semantics_formula I f1 v <-> dynamic_semantics_formula I f2 v)
    -> (dynamic_semantics_formula I (KFbox p1 f1) v
        <-> dynamic_semantics_formula I (KFbox p2 f2) v).
Proof.
  introv cond1 cond2; split; introv h q;
    apply cond2; apply h; apply cond1; auto.
Qed.


Ltac dest_cases_end := simpl in *; GC; repnd; repndors; ginv; sp; fail.

Ltac ginv_step_at H :=
  match type of H with
  | _ = _ =>
    first [ complete (inversion H)
          | destruct H; complete auto
          | inversion H; simpl in H; subst;
            match type of H with
            | ?x = ?x => clear H
            end
          ]
  end.

Ltac dest_cases_end_at z :=
  simpl in *; GC;
  try (ginv_step_at z;fail);
  try (match type of z with
       | _ <> _ => destruct z;auto
       end;fail).

Ltac dest_symbol_dec :=
  let d := fresh "d" in
  match goal with

  (* on hypotheses *)

  | [ H : context[FunctionSymbol_dec ?a ?b] |- _ ] =>
    destruct (FunctionSymbol_dec a b) as [d|d];
    try (dest_cases_end_at d);
    simpl in H;
    GC

  | [ H : context[PredicateSymbol_dec ?a ?b] |- _ ] =>
    destruct (PredicateSymbol_dec a b) as [d|d];
    try (dest_cases_end_at d);
    simpl in H;
    GC

  | [ H : context[QuantifierSymbol_dec ?a ?b] |- _ ] =>
    destruct (QuantifierSymbol_dec a b) as [d|d];
    try (dest_cases_end_at d);
    simpl in H;
    GC

  | [ H : context[ProgramConstName_dec ?a ?b] |- _ ] =>
    destruct (ProgramConstName_dec a b) as [d|d];
    try (dest_cases_end_at d);
    simpl in H;
    GC

  | [ H : context[ODEConst_dec ?a ?b] |- _ ] =>
    destruct (ODEConst_dec a b) as [d|d];
    try (dest_cases_end_at d);
    simpl in H;
    GC

  | [ H : context[Symbol_dec ?a ?b] |- _ ] =>
    destruct (Symbol_dec a b) as [d|d];
    try (dest_cases_end_at d);
    simpl in H;
    GC

  | [ H : context[KAssignable_dec ?a ?b] |- _ ] =>
    destruct (KAssignable_dec a b) as [d|d];
    try (dest_cases_end_at d);
    simpl in H;
    GC

  (* on conclusion *)

  | [ |- context[FunctionSymbol_dec ?a ?b] ] =>
    destruct (FunctionSymbol_dec a b) as [d|d];
    try (dest_cases_end_at d);
    simpl;
    GC

  | [ |- context[PredicateSymbol_dec ?a ?b] ] =>
    destruct (PredicateSymbol_dec a b) as [d|d];
    try (dest_cases_end_at d);
    simpl;
    GC

  | [ |- context[QuantifierSymbol_dec ?a ?b] ] =>
    destruct (QuantifierSymbol_dec a b) as [d|d];
    try (dest_cases_end_at d);
    simpl;
    GC

  | [ |- context[ProgramConstName_dec ?a ?b] ] =>
    destruct (ProgramConstName_dec a b) as [d|d];
    try (dest_cases_end_at d);
    simpl;
    GC

  | [ |- context[ODEConst_dec ?a ?b] ] =>
    destruct (ODEConst_dec a b) as [d|d];
    try (dest_cases_end_at d);
    simpl;
    GC

  | [ |- context[Symbol_dec ?a ?b] ] =>
    destruct (Symbol_dec a b) as [d|d];
    try (dest_cases_end_at d);
    simpl;
    GC

  | [ |- context[KAssignable_dec ?a ?b] ] =>
    destruct (KAssignable_dec a b) as [d|d];
    try (dest_cases_end_at d);
    simpl;
    GC
  end.

Definition US_formula_ofalse := uniform_substitution_formula_opt_false.
Definition US_formula_otrue  := uniform_substitution_formula_opt_true.

Tactic Notation "computeUS" :=
  try (unfold US_rule, US_formula_otrue, uniform_substitution_formula_opt_true);
  try (unfold US_rule, US_formula_ofalse, uniform_substitution_formula_opt_false);
  simpl;
  unfold
    bind,
    omap,
    lookup_func,
    lookup_quant,
    lookup_ode,
    lookup_pred,
    lookup_const,
    U_admissible_terms,
    free_vars_sub_restrict_terms,
    U_admissible_term,
    free_vars_sub_restrict_term; simpl;
    repeat dest_symbol_dec;simpl;
  unfold eassignables_disj, in_signature; simpl;
    repeat dest_symbol_dec;simpl;
  unfold
    U_admissible_formula,
    free_vars_sub_restrict_formula; simpl;
  repeat dest_symbol_dec;
  unfold eassignables_disj, in_signature; simpl;
    repeat dest_symbol_dec;simpl;
  repeat rewrite fold_VT1 in *;
  repeat rewrite fold_Fof1 in *;
  repeat rewrite fold_Pof1 in *;
  repeat fold tvarx in *.

Tactic Notation "computeUS" ident(h) :=
  try (unfold US_rule, uniform_substitution_formula_opt_true in h);
  try (unfold US_rule, uniform_substitution_formula_opt_false in h);
  simpl in h;
  unfold
    bind,
    omap,
    lookup_func,
    lookup_quant,
    lookup_ode,
    lookup_pred,
    lookup_const,
    U_admissible_terms,
    free_vars_sub_restrict_terms,
    U_admissible_term,
    free_vars_sub_restrict_term in h; simpl in h;
    repeat dest_symbol_dec;simpl;
  unfold eassignables_disj, in_signature in h; simpl in h;
    repeat dest_symbol_dec;simpl;
  unfold
    U_admissible_formula,
    free_vars_sub_restrict_formula in h; simpl in h;
  repeat dest_symbol_dec;
  unfold eassignables_disj, in_signature in h; simpl in h;
    repeat dest_symbol_dec;simpl;
  repeat rewrite fold_VT1 in *;
  repeat rewrite fold_Fof1 in *;
  repeat rewrite fold_Pof1 in *;
  repeat fold tvarx in *.



(**

  DI for KFlessEqual

  (p(x) -> g(x)<=h(x))
  -> [x'=f(x), c & p(x)](g(x)<=h(x)')
  -> [x'=f(x), c & p(x)]g(x)<=h(x)

 *)
Definition DI_le_axiom : Formula :=
  KFimply
    (KFimply (Pof1 predp tvarx) (KFlessEqual (Fof1 funcg tvarx) (Fof1 funch tvarx)))
    (KFimply
       (KFbox
          (KPodeSystem
             (ODEprod
                (ODEsing varx (Fof1 funcf tvarx))
                (ODEconst odec))
             (Pof1 predp tvarx))
          (KFlessEqual
             (KTdifferential (Fof1 funcg tvarx))
             (KTdifferential (Fof1 funch tvarx)))
       )
       (KFbox
          (KPodeSystem
             (ODEprod
                (ODEsing varx (Fof1 funcf tvarx))
                (ODEconst odec))
             (Pof1 predp tvarx))
          (KFlessEqual
             (Fof1 funcg tvarx)
             (Fof1 funch tvarx)))).

Definition DI_le_rule : rule := MkRule [] DI_le_axiom.

Lemma DI_le_sound : rule_true DI_le_rule.
Proof.
  introv imp; simpl in *; clear imp.

  pose proof (US_sound
                DI_ge_axiom
                [USE_function funcg 1 (Fof1 funch (KTdot 0)),
                 USE_function funch 1 (Fof1 funcg (KTdot 0))]) as h.
  unfold DI_ge_axiom in h.
  computeUS h.

  unfold rule_true in h; simpl in h.
  autodimp h hyp.
  { introv xx; repndors; tcsp; subst.
    apply DI_ge_sound; simpl; tcsp. }

  eapply Df_formula_valid_iff;[|exact h]; clear h.
  introv h.
  unfold DI_le_axiom.
  eapply dynamic_semantics_formula_KFimply_equiv;[| |exact h]; introv.
  { apply dynamic_semantics_formula_KFimply_equiv; introv; tcsp.
    apply dynamic_semantics_formula_KFlessEqual_KFgreaterEqual_equiv. }
  { apply dynamic_semantics_formula_KFimply_equiv; introv.
    { apply dynamic_semantics_formula_KFbox_equiv; introv; tcsp.
      apply dynamic_semantics_formula_KFlessEqual_KFgreaterEqual_equiv. }
    { apply dynamic_semantics_formula_KFbox_equiv; introv; tcsp.
      apply dynamic_semantics_formula_KFlessEqual_KFgreaterEqual_equiv. }
  }
Qed.


(**

  DI for KFless

  (p(x)->g(x)>h(x))
  -> [x'=f(x), c & p(x)](g(x)'<=h(x)')
  -> [x'=f(x), c & p(x)]g(x)<h(x)

 *)
Definition DI_lt_axiom : Formula :=
    KFimply
      (KFimply
         (Pof1 predp tvarx)
         (KFless (Fof1 funcg tvarx) (Fof1 funch tvarx)))
      (KFimply
         (KFbox
            (KPodeSystem
               (ODEprod
                  (ODEsing varx (Fof1 funcf tvarx))
                  (ODEconst odec))
               (Pof1 predp tvarx))
            (KFlessEqual
               (KTdifferential (Fof1 funcg tvarx))
               (KTdifferential (Fof1 funch tvarx)))
         )
         (KFbox
            (KPodeSystem
               (ODEprod
                  (ODEsing varx (Fof1 funcf tvarx))
                  (ODEconst odec))
               (Pof1 predp tvarx))
            (KFless
               (Fof1 funcg tvarx)
               (Fof1 funch tvarx)))).

Definition DI_lt_rule : rule := MkRule [] DI_lt_axiom.

Lemma DI_lt_sound : rule_true DI_lt_rule.
Proof.
  introv imp; simpl in *; clear imp.

  pose proof (US_sound
                DI_gt_axiom
                [USE_function funcg 1 (Fof1 funch (KTdot 0)),
                 USE_function funch 1 (Fof1 funcg (KTdot 0))]) as h.
  unfold DI_gt_axiom in h.
  computeUS h.

  unfold rule_true in h; simpl in h.
  autodimp h hyp.
  { introv xx; repndors; tcsp; subst.
    apply DI_gt_sound; simpl; tcsp. }

  eapply Df_formula_valid_iff;[|exact h]; clear h.
  introv h.
  unfold DI_lt_axiom.
  eapply dynamic_semantics_formula_KFimply_equiv;[| |exact h]; introv.
  { apply dynamic_semantics_formula_KFimply_equiv; introv; tcsp. }
  { apply dynamic_semantics_formula_KFimply_equiv; introv.
    { apply dynamic_semantics_formula_KFbox_equiv; introv; tcsp.
      apply dynamic_semantics_formula_KFlessEqual_KFgreaterEqual_equiv. }
    { apply dynamic_semantics_formula_KFbox_equiv; introv; tcsp. }
  }
Qed.


(**

  DI for KFequal

  (p(x)->g(x)≥h(x))
  -> [x'=f(x), c & p(x)](g(x)=h(x)')
  -> [x'=f(x), c & p(x)]g(x)=h(x)

 *)
Definition DI_eq_axiom : Formula :=
  KFimply
    (KFimply
       (Pof1 predp tvarx)
       (KFequal (Fof1 funcg tvarx) (Fof1 funch tvarx)))
    (KFimply
       (KFbox
          (KPodeSystem
             (ODEprod
                (ODEsing varx (Fof1 funcf tvarx))
                (ODEconst odec))
             (Pof1 predp tvarx))
          (KFequal
             (KTdifferential (Fof1 funcg tvarx))
             (KTdifferential (Fof1 funch tvarx)))
       )
       (KFbox
          (KPodeSystem
             (ODEprod
                (ODEsing varx (Fof1 funcf tvarx))
                (ODEconst odec))
             (Pof1 predp tvarx))
          (KFequal
             (Fof1 funcg tvarx)
             (Fof1 funch tvarx)))).

Definition DI_eq_rule : rule := MkRule [] DI_eq_axiom.

Lemma DI_eq_sound : rule_true DI_eq_rule.
Proof.
  introv imp; simpl in *; clear imp.
  repeat introv ; simpl.
  introv h1 h2 q.
  exrepnd; subst.
  allrw fold_VR1.

  assert (v assignx = phi 0%R assignx) as xx.
  { apply (q0 assignx); introv xx.
    unfold ode_footprint_diff in xx; simpl in xx;
      repndors; tcsp; [inversion xx|].
    apply in_map_iff in xx; exrepnd; ginv. }

  remember (I (SymbolFunction funcg 1)) as Fg; simpl in Fg.
  remember (I (SymbolFunction funch 1)) as Fh; simpl in Fh.
  destruct Fg as [Fg condg].
  destruct Fh as [Fh condh].
  simpl in *.
  hide_hyp HeqFh.
  hide_hyp HeqFg.

  fold assignx in *.
  assert (forall z,
             (0 <= z)%R
             -> (z <= r)%R
             -> (Derive (fun t : R => Fg (VR1 (phi t assignx))) z
                 =
                 Derive (fun t : R => Fh (VR1 (phi t assignx))) z)%R) as gtd.

  {
    introv le0z lezr.
    pose proof (h2 (phi (mk_preal_upto r (mk_preal z le0z) lezr))) as zz; clear h2.
    autodimp zz hyp; simpl in *.

    {
      exists (mk_preal z le0z) phi; simpl; dands; auto.

      {
        introv i; simpl in *.
        pose proof (q3 (ex_preal_upto_trans
                          r
                          (mk_preal_upto r (mk_preal z le0z) lezr)
                          zeta) v0) as q; simpl in q; tcsp.
      }

      {
        introv.
        pose proof (q1 (ex_preal_upto_trans
                          r
                          (mk_preal_upto r (mk_preal z le0z) lezr)
                          zeta)) as q; simpl in q; tcsp.
      }
    }

    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    symmetry in zz.
    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].

    autorewrite with core in zz.

    pose proof (differential_space_time
                  varx I r phi z
                  (Fof1 funcg tvarx)) as e1.
    repeat (autodimp e1 hyp); eauto with core;
      try (complete (destruct r; simpl; auto));
      try (complete (apply Rle_refl)).

    {
      introv; simpl.
      pose proof (q3 zeta varx) as h; simpl in h; autodimp h hyp.
      dest_cases w.
    }

    simpl in e1.
    autorewrite with core in e1.
    rewrite <- HeqFg in e1; simpl in *.
    erewrite Derive_ext in e1;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    fold assignx in *.
    rewrite e1 in zz; clear e1.

    pose proof (differential_space_time
                  varx I r phi z
                  (Fof1 funch tvarx)) as e2.
    repeat (autodimp e2 hyp); eauto with core; simpl in *;
      try (complete (destruct r; simpl; auto));
      try (complete (apply Rle_refl)).

    {
      introv; simpl.
      pose proof (q3 zeta varx) as h; simpl in h.
      autodimp h hyp; dest_cases x.
    }

    simpl in e2.
    autorewrite with core in e2.
    rewrite <- HeqFh in e2; simpl in *.
    erewrite Derive_ext in e2;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    fold assignx in *.
    rewrite e2 in zz; clear e2.

    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    symmetry in zz.
    erewrite Derive_ext in zz;[|introv;autorewrite with core;rewrite fold_VR1;reflexivity].
    auto.
  }
  clear h2.

  assert (forall z : R,
             (0 <= z)%R ->
             (z <= r)%R ->
             (Derive (fun t : R => Fh (VR1 (phi t assignx))) z * r
              = Derive (fun t : R => Fg (VR1 (phi t assignx))) z * r)%R) as gtd'.
  { introv le0z lezr.
    apply Rmult_eq_compat_r.
    pose proof (gtd z) as ss.
    repeat (autodimp ss hyp). }
  clear gtd.

  pose proof (MVT_gen
                (fun r => (Fg (VR1 (phi r assignx)) - Fh (VR1 (phi r assignx)))%R)
                0 r
                (fun r =>
                   (Derive (fun t : R => Fg (VR1 (phi t assignx))) r
                    - Derive (fun t : R => Fh (VR1 (phi t assignx))) r)%R)) as mvt.
  rewrite Rmin_left in mvt; auto.
  rewrite Rmax_right in mvt; auto.
  simpl in mvt.
  repeat (autodimp mvt hyp).

  {
    introv ltx.
    destruct ltx as [lt0x ltxr].
    apply @is_derive_minus; apply Derive_correct.

    {
      apply (ex_derive_comp
               (fun t => Fg (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      apply Rlt_le in lt0x.
      apply Rlt_le in ltxr.
      pose proof (q3 (mk_preal_upto r (mk_preal x lt0x) ltxr) varx) as q; simpl in q.
      autodimp q hyp; dest_cases w.
    }

    {
      apply (ex_derive_comp
               (fun t => Fh (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      apply Rlt_le in lt0x.
      apply Rlt_le in ltxr.
      pose proof (q3 (mk_preal_upto r (mk_preal x lt0x) ltxr) varx) as q; simpl in q.
      autodimp q hyp; dest_cases w.
    }
  }

  {
    introv lex.
    destruct lex as [le0x lexr].

    unfold continuity_pt.
    apply (cont_deriv
             _
             (fun r =>
                (Derive (fun t : R => Fg (VR1 (phi t assignx))) r
                 - Derive (fun t : R => Fh (VR1 (phi t assignx))) r)%R)).
    apply derivable_pt_lim_D_in.
    apply is_derive_Reals.
    apply @is_derive_minus; apply Derive_correct.

    {
      apply (ex_derive_comp
               (fun t => Fg (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      pose proof (q3 (mk_preal_upto r (mk_preal x le0x) lexr) varx) as q; simpl in q.
      autodimp q hyp; dest_cases w.
    }

    {
      apply (ex_derive_comp
               (fun t => Fh (VR1 t))
               (fun t => phi t assignx)
               x); simpl in *; eauto 2 with core.
      pose proof (q3 (mk_preal_upto r (mk_preal x le0x) lexr) varx) as q; simpl in q.
      autodimp q hyp; dest_cases w.
    }
  }

  {
    exrepnd.
    autorewrite with core in mvt0.
    repeat (rewrite <- xx in mvt0).
    apply subtract_both_side_equ in mvt0.
    pose proof (gtd' c) as ss.
    repeat (autodimp ss hyp).
    rewrite Rmult_minus_distr_r in mvt0.
    rewrite ss in mvt0.
    apply Rminus_diag_uniq.
    rewrite mvt0; clear mvt0.
    rewrite h1.
    autorewrite with core. auto.

    pose proof (q1 (mk_preal_upto r (mk_preal 0 (Rle_refl 0)) (preal_cond r))) as cz.
    simpl in cz; repnd.
    rewrite <- xx in cz0. auto.
  }
Qed.


(* More constants *)

Definition predH  : PredicateSymbol := predicate_symbol "H".
Definition predP1 : PredicateSymbol := predicate_symbol "P1".
Definition predP2 : PredicateSymbol := predicate_symbol "P2".
Definition predQ1 : PredicateSymbol := predicate_symbol "Q1".
Definition predQ2 : PredicateSymbol := predicate_symbol "Q2".

Definition fpredH  : Formula := KFpredOf predH  0 VT0.
Definition fpredP1 : Formula := KFpredOf predP1 0 VT0.
Definition fpredP2 : Formula := KFpredOf predP2 0 VT0.
Definition fpredQ1 : Formula := KFpredOf predQ1 0 VT0.
Definition fpredQ2 : Formula := KFpredOf predQ2 0 VT0.


(**

  DI for &

  P1 -> [c & H]P2 -> [c & H]P1       Q1 -> [c & H]Q2 -> [c & H]Q1
  ---------------------------------------------------------------
         (P1 & Q1) -> [c & H](P2 & Q2) -> [c & H](P1 & Q1)

 *)
Definition DI_box_schema (A B : Formula) : Formula :=
  KFimply
    A
    (KFimply
       (KFbox (KPodeSystem (ODEconst odec) fpredH) B)
       (KFbox (KPodeSystem (ODEconst odec) fpredH) A)).

Definition DI_and_rule (n : nat) : rule :=
  MkRule
    [DI_box_schema (PofVN predP1 varx n) (PofVN predP2 varx n),
     DI_box_schema (PofVN predQ1 varx n) (PofVN predQ2 varx n)]
    (DI_box_schema (KFand (PofVN predP1 varx n) (PofVN predQ1 varx n))
                   (KFand (PofVN predP2 varx n) (PofVN predQ2 varx n))).

Lemma DI_and_sound : forall n, rule_true (DI_and_rule n).
Proof.
  introv imp; simpl in *.
  repeat introv; simpl.
  introv ip cond box; exrepnd; subst.

  dLin_hyp h.
  pose proof (h  I v) as q1; clear h.
  pose proof (h0 I v) as q2; clear h0.
  simpl in *.
  repeat (autodimp q1 hyp).

  { introv h; exrepnd; subst.
    pose proof (cond (phi0 r0)) as q; clear cond.
    autodimp q hyp; tcsp.
    exists r0 phi0; dands; auto. }

  repeat (autodimp q2 hyp).

  { introv h; exrepnd; subst.
    pose proof (cond (phi0 r0)) as q; clear cond.
    autodimp q hyp; tcsp.
    exists r0 phi0; dands; auto. }

  pose proof (q1 (phi r)) as h1; clear q1.
  pose proof (q2 (phi r)) as h2; clear q2.

  autodimp h1 hyp.
  { exists r phi; dands; auto. }
  autodimp h2 hyp.
  { exists r phi; dands; auto. }
Qed.


(**

  DI for or

  P1 -> [c & H]P2 -> [c & H]P1       Q1 -> [c & H]Q2 -> [c & H]Q1
  ---------------------------------------------------------------
         (P1 | Q1) -> [c & H](P2 & Q2) -> [c & H](P1 | Q1)

 *)

Definition DI_or_rule (n : nat) : rule :=
  MkRule
    [DI_box_schema (PofVN predP1 varx n) (PofVN predP2 varx n),
     DI_box_schema (PofVN predQ1 varx n) (PofVN predQ2 varx n)]
    (DI_box_schema (KFor  (PofVN predP1 varx n) (PofVN predQ1 varx n))
                   (KFand (PofVN predP2 varx n) (PofVN predQ2 varx n))).

Lemma DI_or_sound : forall n, rule_true (DI_or_rule n).
Proof.
  introv imp; simpl in *.
  repeat introv; simpl.
  introv ip cond box; exrepnd; subst.

  dLin_hyp h.
  pose proof (h  I v) as q1; clear h.
  pose proof (h0 I v) as q2; clear h0.
  simpl in *.

  repndors.

  { clear q2.
    repeat (autodimp q1 hyp).

    { introv h; exrepnd; subst.
      pose proof (cond (phi0 r0)) as q; clear cond.
      autodimp q hyp; tcsp.
      exists r0 phi0; dands; auto. }

    pose proof (q1 (phi r)) as h1; clear q1.

    autodimp h1 hyp.
    { exists r phi; dands; auto. }
  }

  { clear q1.
    repeat (autodimp q2 hyp).

    { introv h; exrepnd; subst.
      pose proof (cond (phi0 r0)) as q; clear cond.
      autodimp q hyp; tcsp.
      exists r0 phi0; dands; auto. }

    pose proof (q2 (phi r)) as h2; clear q2.

    autodimp h2 hyp.
    { exists r phi; dands; auto. }
  }
Qed.


(**

  DI for negation

   <c&H>P1 -> [c & H]P2 -> [c & H]P1
  -----------------------------------
  <c&H>!P1 -> [c & H]P2 -> [c & H]!P1

 *)

Definition DI_diamond_box_schema (A B : Formula) : Formula :=
  KFimply
    (KFdiamond (KPodeSystem (ODEconst odec) fpredH) A)
    (KFimply
       (KFbox (KPodeSystem (ODEconst odec) fpredH) B)
       (KFbox (KPodeSystem (ODEconst odec) fpredH) A)).

Definition DI_not_rule : rule :=
  MkRule
    [DI_diamond_box_schema quantP quantQ]
    (DI_diamond_box_schema (KFnot quantP) quantQ).

Definition DI_not_sound : rule_true DI_not_rule.
Proof.
  introv imp hp1 hp2 hode ip1; simpl in *.
  dLin_hyp h.
  pose proof (h I v) as q; clear h.
  simpl in q.
  repeat (autodimp q hyp).

  { exists w; dands; auto. }

  clear hode ip1 hp2.
  exrepnd; subst.

  pose proof (q (phi r)) as h; clear q.
  autodimp h hyp.
  exists r phi; dands; auto.
Qed.


(*

  DI for forall

               P1 -> [c & H]P2 -> [c & H]P1
  ----------------------------------------------------------------
  (forall vs.P1) -> [c & H](forall vs.P2) -> [c & H](forall vs.P1)

  where vs for now is just [x].

 *)

Definition DI_forall_rule (n : nat): rule :=
  MkRule
    [DI_box_schema (PofVN predP1 varx n) (PofVN predP2 varx n)]
    (DI_box_schema
       (KFforallVars [varx] (PofVN predP1 varx n))
       (KFforallVars [varx] (PofVN predP2 varx n))).

Lemma DI_forall_sound: forall n, rule_true (DI_forall_rule n).
Proof.
  introv imp hp1 hp2 hbox len; simpl in *.
  repeat (destruct rs; simpl in *; ginv).
  exrepnd; subst.
  dLin_hyp himp.

  pose proof (hp1 [r]) as q; clear hp1; simpl in q; autodimp q hyp.

  pose proof (himp I (upd_state v (KAssignVar varx) r) q) as h; clear himp.
  simpl in h.
  repeat (autodimp h hyp).

  {
    introv cond; exrepnd; subst.
    pose proof (hp2 (phi0 r1)) as h.
    autodimp h hyp.

    Focus 2.
    { pose proof (h [r]) as h; simpl in h; autodimp h hyp.
      allrw fold_upd_state_var.

      assert (~ List.In (KAssignVar varx) (ode_footprint_diff I (ODEconst odec))) as d.
      {
        introv xx.
        unfold ode_footprint_diff in xx.
        apply in_map_iff in xx; exrepnd; ginv.
      }

      destruct (in_dec KAssignable_dec (KAssignVar varx) (ode_footprint_vars I (ODEconst odec))) as [e|e].

      {

        (*
      }

      Focus 2.

      {
        applydup cond0 in d.
        autorewrite with core in *.
        pose proof (cond1 (mk_preal_upto r1 r1 (Rle_refl r1))) as zz; simpl in zz; repnd.
        rewrite zz in d0; auto;
          [|unfold ode_footprint; rewrite in_app_iff; intro xx; repndors; tcsp].
        rewrite d0 in h.
        rewrite upd_state_var_ext in h; auto.
      }
    }
    { exists r1 phi0; dands; auto.
      introv i.
      applydup cond0 in i as j.
      unfold upd_state in j.
      dest_cases w.
      subst.
      applydup hbox0 in i.


  }

  {
    pose proof (h (phi r0)) as h; autodimp h hyp.
    exists r0 phi; dands; auto.
    {
    }
  }

  exrepnd. subst.
  autodimp ih1 hyp.
  pose proof (ih2 rs) as qq1. clear ih2.
  autodimp qq1 hyp.
  pose proof (ih3 (phi r)) as q1. clear ih3.
  autodimp q1 hyp.
  destruct rs in *. simpl in *. tcsp.
  exrepnd. simpl in *.
  exists r phi. split. auto. split. auto.
  split.  auto. auto.

  pose proof (q1 rs) as xx. clear q1.
  destruct rs in *. simpl in *. auto.

  simpl in *. rewrite fold_upd_state_var in *.
  SearchAbout upd_state dynamic_semantics_term.
*)

Abort.
