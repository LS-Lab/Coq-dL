Require Export Coquelicot.
Require Export reals_util.
Require Export deriv_util.

Hint Rewrite Rplus_minus : core.

Lemma subtract_both_side_equ:
  forall a b c : R, (a - b)%R  = c -> a = (b + c) %R.
Proof.
  introv h; subst.
  (*SearchAbout (?x + (_ - ?x))%R.*)
  autorewrite with core; auto.
Qed.


Require Import Reals.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Require Import Markov Rcomplements Rbar Lub Lim_seq Derive SF_seq.
Require Import Continuity Hierarchy Seq_fct RInt PSeries.

Lemma is_RInt_derive_sp (f df : R -> R) (a b c : R) :
  (forall x : R, Rmin a b <= x <= Rmax a b -> is_derive f x (df x)) ->
  (forall x : R, Rmin a b <= x <= Rmax a b -> df x = c) ->
    is_RInt df a b (f b - f a)%R.
Proof.
  intros Hf Hdf.
  wlog: a b Hf Hdf / (a < b) => [Hw | Hab].
    case: (Rle_lt_dec a b) => Hab.
    case: Hab => Hab.
    by apply Hw.
    rewrite Hab Rminus_eq_0.
    by apply @is_RInt_point.
    evar_last.
    apply is_RInt_swap.
    apply Hw => //.
    by rewrite Rmin_comm Rmax_comm.
    by rewrite Rmin_comm Rmax_comm.
    change opp with Ropp ; simpl ; ring.

    apply filterlim_locally.
    rewrite (proj1 (sign_0_lt _)).
    2: by apply Rminus_lt_0 in Hab.
    intros.
    eapply filter_imp.
    intros x Hx ; rewrite scal_one ; by apply norm_compat1, Hx.
    rewrite /Rmin /Rmax in Hf, Hdf ;
      destruct (Rle_dec a b) as [_ | Hab'].
    2: contradict Hab' ; by apply Rlt_le.

    assert (He : 0 < eps / (b - a)).
    apply Rdiv_lt_0_compat.
      by apply eps.
        by apply Rminus_lt_0 in Hab.
        set (e := mkposreal _ He).

        assert (@ex
                  posreal
                  (fun delta =>
                     forall x y : R,
                       a <= x <= b
                       -> a <= y <= b
                       -> ball x delta y
                       -> ball_norm (df x) e (df y))) as Hd.
        { exists R1pos; introv h1 h2 h3.
          repeat (rewrite Hdf; auto).
          unfold ball_norm.
          autorewrite with core.
          unfold norm; simpl.
          unfold abs; simpl.
          autorewrite with core; auto. }
        destruct Hd as [delta Hd].
        clear Hdf.

  exists delta.
  rewrite /Rmin /Rmax ;
  destruct (Rle_dec a b) as [_ | Hab'].
  2: contradict Hab' ; by apply Rlt_le.
  intros y Hstep [Hptd [Ha Hb]].
  replace (pos eps) with (e * (b - a))%R.
  move: e Hd => {eps He} e Hd.
  rewrite -Ha {a Ha} in Hf Hd Hab |- *.
  rewrite -Hb {b Hb} in Hf Hd Hab |- *.
  move: Hab Hstep Hptd Hf Hd.
  apply SF_cons_ind with (s := y) => {y} [x0 | x0 y IHy] /= Hab Hstep Hptd Hf Hd.
  by apply Rlt_irrefl in Hab.
  rewrite Riemann_sum_cons.
  change minus with Rminus ;
  change plus with Rplus ;
  change scal with Rmult.

  assert (Hab_0 : fst x0 <= SF_h y).
    eapply Rle_trans ; apply (Hptd _ (lt_O_Sn _)).
  assert (Hab_1 : SF_h y <= seq.last (SF_h y) (SF_lx y)).
    apply (sorted_last (SF_lx y) O).
    apply ptd_sort.
    by apply ptd_cons with x0.
    by apply lt_O_Sn.
  assert (Hstep_0 : Rabs (SF_h y - fst x0) < delta).
    eapply Rle_lt_trans, Hstep.
    by apply Rmax_l.
  assert (Hstep_1 : seq_step (SF_lx y) < delta).
    eapply Rle_lt_trans, Hstep.
    by apply Rmax_r.
  assert (Hptd_0 : fst x0 <= snd x0 <= SF_h y).
    by apply (Hptd _ (lt_O_Sn _)).
  assert (Hptd_1 : pointed_subdiv y).
    by apply ptd_cons with x0.
  assert (Hf_0 : forall x : R, fst x0 <= x <= (SF_h y) -> is_derive f x (df x)).
    intros ; apply Hf ; split.
    by apply H.
    eapply Rle_trans, Hab_1 ; by apply H.
  assert (Hf_1 : forall x : R,
    SF_h y <= x <= seq.last (SF_h y) (SF_lx y) -> is_derive f x (df x)).
    intros ; apply Hf ; split.
    by eapply Rle_trans, H.
    by apply H.
  assert (Hd_0 : forall x y0 : R,
    fst x0 <= x <= (SF_h y) -> fst x0 <= y0 <= (SF_h y) ->
    ball x delta y0 -> ball_norm (df x) e (df y0)).
    intros ; apply Hd => // ; split.
    by apply H.
    eapply Rle_trans, Hab_1 ; by apply H.
    apply H0.
    eapply Rle_trans, Hab_1 ; by apply H0.
  assert (Hd_1 : forall x y0 : R,
    SF_h y <= x <= seq.last (SF_h y) (SF_lx y) ->
    SF_h y <= y0 <= seq.last (SF_h y) (SF_lx y) ->
    ball x delta y0 -> ball_norm (df x) e (df y0)).
    intros ; apply Hd => // ; split.
    by eapply Rle_trans, H.
    by apply H.
    by eapply Rle_trans, H0.
    by apply H0.
  move: (fun H => IHy H Hstep_1 Hptd_1 Hf_1 Hd_1) => {IHy Hstep Hptd Hf Hd Hstep_1 Hf_1 Hd_1} IHy.

  assert (((SF_h y - fst x0) * df (snd x0) + Riemann_sum df y -
    (f (seq.last (SF_h y) (seq.unzip1 (SF_t y))) - f (fst x0)))%R
    = (((SF_h y - fst x0) * df (snd x0) - (f (SF_h y) - f (fst x0)))
        + (Riemann_sum df y - (f (seq.last (SF_h y) (seq.unzip1 (SF_t y))) - f (SF_h y))))%R)
    by ring.
  rewrite H {H}.
  eapply Rle_lt_trans.
  apply @norm_triangle.
  replace (e * (seq.last (SF_h y) (seq.unzip1 (SF_t y)) - fst x0))%R
    with ((SF_h y - fst x0) * e +
         (e * (seq.last (SF_h y) (seq.unzip1 (SF_t y)) - SF_h y)))%R
    by ring.

  case: Hab_0 => Hab_0 ; last first.
  rewrite Hab_0 !Rminus_eq_0 !Rmult_0_l Rminus_eq_0 norm_zero !Rplus_0_l.
  apply IHy.
  by rewrite -Hab_0.
  destruct (MVT_gen f (fst x0) (SF_h y) df) as [cc [Hc Hdf]] => //.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab_0) => // _ _.
  intros cc Hc ; apply Hf_0.
  move: Hc ;
  by split ; apply Rlt_le ; apply Hc.
  rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab_0) => // _ _.
  intros cc Hc ; apply continuity_pt_filterlim, @ex_derive_continuous.
  by eexists ; apply Hf_0.
  move: Hc ; rewrite /Rmin /Rmax ; case: Rle_dec (Rlt_le _ _ Hab_0) => // _ _ Hc.
  rewrite Hdf {Hdf} Rmult_comm -Rmult_minus_distr_r Rmult_comm.
  eapply Rle_lt_trans.
  apply Rplus_le_compat_r.
  apply @norm_scal.
  change abs with Rabs.
  rewrite Rabs_pos_eq.
  2: by apply Rminus_lt_0, Rlt_le in Hab_0.
  apply Rplus_lt_le_compat.
  apply Rmult_lt_compat_l.
  by apply Rminus_lt_0 in Hab_0.

  apply Hd_0 => //.
  eapply Rle_lt_trans, Hstep_0.
  rewrite Rabs_pos_eq.
  2: by apply Rminus_lt_0, Rlt_le in Hab_0.
  apply Rabs_le_between ; split.
  rewrite Ropp_minus_distr.
  apply Rplus_le_compat.
  by apply Hptd_0.
  by apply Ropp_le_contravar, Hc.
  apply Rplus_le_compat.
  by apply Hptd_0.
  by apply Ropp_le_contravar, Hc.

  case: Hab_1 => /= Hab_1 ; last first.
  rewrite -Hab_1 !Rminus_eq_0 Rmult_0_r.
  rewrite Riemann_sum_zero //.
  rewrite Rminus_eq_0 norm_zero.
  by apply Rle_refl.
  by apply ptd_sort.

  by apply Rlt_le, IHy.

  unfold e ; simpl ; field.
  apply Rgt_not_eq.
  by apply Rminus_lt_0 in Hab.
Qed.

Lemma RInt_Derive_sp (f : R -> R) (a b c : R):
  (forall x, Rmin a b <= x <= Rmax a b -> ex_derive f x) ->
  (forall x, Rmin a b <= x <= Rmax a b -> Derive f x = c) ->
  RInt (Derive f) a b = f b - f a.
Proof.
  intros Df Cdf.
  apply is_RInt_unique.
  apply (is_RInt_derive_sp _ _ _ _ c); auto.
  intros ; by apply Derive_correct, Df.
Qed.

Lemma evolve_from_initial :
  forall (C r : R) (F : R -> R),
    (0 <= r)%R
    -> (forall x : preal_upto r,
           ex_derive_R F x
           /\ Derive F x = C)
    -> F r = (F 0 + C * r)%R.
Proof.
  introv rge0 h.

  apply (subtract_both_side_equ (F r) (F 0) (C*r)).

  (* calculate integral of constant function *)
  pose proof (RInt_const 0 r C) as int_const.
  autorewrite with core in *.
  rewrite Rmult_comm.
  rewrite <- int_const; clear int_const.

  (* integral (derivative (f x)) = F(r) - F 0 *)
  rewrite <- (RInt_Derive_sp F 0 r C).

  { apply RInt_ext; introv cond.
    destruct cond as [cond1 cond2].
    rewrite Rmin_left in cond1; auto.
    rewrite Rmax_right in cond2; auto.

    pose proof (h (mk_preal_upto r (mk_preal x cond1) cond2)) as q; simpl in q; sp.
  }

  { introv cond.
    destruct cond as [cond1 cond2].
    rewrite Rmin_left in cond1; auto.
    rewrite Rmax_right in cond2; auto.

    pose proof (h (mk_preal_upto r (mk_preal x cond1) cond2)) as q; simpl in q; sp.
  }

  { introv cond.
    destruct cond as [cond1 cond2].
    rewrite Rmin_left in cond1; auto.
    rewrite Rmax_right in cond2; auto.

    pose proof (h (mk_preal_upto r (mk_preal x cond1) cond2)) as q;
      simpl in q; repnd; auto. }
Qed.
