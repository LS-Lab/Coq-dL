Require Export Coquelicot.Coquelicot.
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



Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Require Import Coquelicot.Markov Coquelicot.Rcomplements Coquelicot.Rbar Coquelicot.Lub Coquelicot.Lim_seq Coquelicot.Derive Coquelicot.SF_seq.
Require Import Coquelicot.Continuity Coquelicot.Hierarchy Coquelicot.Seq_fct Coquelicot.RInt Coquelicot.PSeries.


Lemma is_RInt_derive_sp (f df : R -> R) (a b c : R) :
  (forall x : R, Rmin a b <= x <= Rmax a b -> is_derive f x (df x)) ->
  (forall x : R, Rmin a b <= x <= Rmax a b -> df x = c) ->
    is_RInt df a b (minus (f b) (f a))%R.
Proof.
  intros Hf Hdf.

  wlog Hab: a b Hf Hdf / (a < b).
  intros H.
  destruct (Rlt_or_le a b) as [Hab|Hab].
    exact: H.
  destruct Hab as [Hab|Hab].
  + rewrite -(opp_opp (minus _ _)).
    apply: is_RInt_swap.
    rewrite opp_minus.
    apply H.
      by rewrite Rmin_comm Rmax_comm.
    by rewrite Rmin_comm Rmax_comm.
    easy.
  + rewrite Hab.
    rewrite /minus plus_opp_r.
    by apply: is_RInt_point.

rewrite Rmin_left in Hf; last by lra.
rewrite Rmax_right in Hf; last by lra.
rewrite Rmin_left in Hdf; last by lra.
rewrite Rmax_right in Hdf; last by lra.
have Hminab : Rmin a b = a by rewrite Rmin_left; lra.
have Hmaxab : Rmax a b = b by rewrite Rmax_right; lra.
evar_last.
apply (RInt_correct df a b).
eapply ex_RInt_ext.
introv w; symmetry; apply Hdf; auto; rewrite Hminab Hmaxab in w; destruct w; split; apply Rlt_le; auto.
apply ex_RInt_const.


apply (plus_reg_r (opp (f b))).
rewrite /minus -plus_assoc (plus_comm (opp _)) plus_assoc plus_opp_r.
rewrite -(RInt_point a df).
apply: sym_eq.

have Hext :  forall x : R, Rmin a b < x < Rmax a b -> c = df x.
move => x; rewrite Hminab Hmaxab => Hx.
symmetry; apply Hdf; try lra.
rewrite -(RInt_ext _ _ _ _ Hext).
rewrite RInt_point -(RInt_point a (fun _ => c)).
rewrite -!(extension_C1_ext f df a b) /=; try lra.
apply: (eq_is_derive (fun t => minus (RInt _ a t) (_ t))) => // t Ht.
have -> : zero = minus (extension_C0 df a b t) (extension_C0 df a b t) by rewrite minus_eq_zero.
apply: is_derive_minus; last first.
  apply: extension_C1_is_derive => /=; first by lra.
    by move => x Hax Hxb; apply: Hf; lra.

    unfold extension_C0.
    rewrite Hdf; auto; try lra.
    rewrite Hdf; auto; try lra; [|destruct Ht;split;[eapply Rle_trans; eauto|apply Rle_refl] ].
    rewrite Hdf; auto; try lra; [|destruct Ht;split;[apply Rle_refl|eapply Rle_trans; eauto] ].

    match goal with
    | [ |- is_derive _ _ ?x ] => assert (x = c) as xx
    end.
    { destruct (Rbar_le_dec a t); simpl; auto.
      destruct (Rbar_le_dec t b); simpl; auto. }
    rewrite xx; clear xx.

    eapply is_derive_ext; simpl.
    { introv; apply RInt_ext; introv w; reflexivity. }

    eapply is_derive_ext; simpl.
    { introv; rewrite RInt_const; simpl; reflexivity. }

    pose proof (scal_one c) as xx.
    rewrite <- xx at 1; clear xx.
    pose proof (is_derive_scal_l (fun x => minus x a) t one c) as zz.
    simpl in zz; apply zz; clear zz.

    pose proof (is_derive_minus (fun x => x) (fun _ => a) t one zero) as xx; simpl in xx.
    rewrite minus_zero_r in xx; apply xx; clear xx.
    { apply is_derive_id. }
    { apply is_derive_const. }
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
  simpl in *.

  assert (scal r C = r * C) as xx by auto; rewrite xx in int_const; clear xx.
  rewrite <- int_const; clear int_const.

  (* integral (derivative (f x)) = F(r) - F 0 *)
  rewrite <- (RInt_Derive_sp F 0 r C).

  { apply RInt_ext; introv cond.
    destruct cond as [cond1 cond2].
    rewrite Rmin_left in cond1; auto.
    rewrite Rmax_right in cond2; auto.

    assert (0 <= x) as cond1' by lra.
    assert (x <= r) as cond2' by lra.

    pose proof (h (mk_preal_upto r (mk_preal x cond1') cond2')) as q; simpl in q; sp.
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
