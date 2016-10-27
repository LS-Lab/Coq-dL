(*

  Copyright 2016 University of Luxembourg

  This file is part of our formalization of Platzer's
    "A Complete Uniform Substitution Calculus for Differential Dynamic Logic"
  available here: http://arxiv.org/pdf/1601.06183.pdf.
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

Require Export reals_util.
Require Export deriv_util.


(**

  This file implements formula which calculates nth derivative
  of multiplication of two functions. This file also implements
  formula which checks if nth derivative of multiplication of two
  functions exists, as well as formula which checks if nth derivative
  of power of function exists.

*)

(** proof that formula for nth derivative of multiplication of two functions is true *)
Lemma Derive_n_mult :
  forall (f g : R -> R) (n : nat) (x : R),
    locally_R x (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y)
    -> locally_R x (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y)
    -> Derive_n (fun x => f x * g x) n x
       = sum_f_R0 (fun k => (C n k) * (Derive_n f (n - k) x * Derive_n g k x)) n.
Proof.
  induction n; introv loc1 loc2.

  - simpl.
    rewrite Rcomplements.C_n_0.
    rewrite Rmult_1_l; auto.

  - match goal with | [ |- _ = ?x ] => remember x as D end.
    simpl.

    rewrite (Derive_ext_loc
               _
               (fun x => sum_f_R0 (fun k : nat => C n k * (Derive_n f (n - k) x * Derive_n g k x)) n));
      [|].

    {
      rewrite Derive_sum_f_R0.

      {
        assert (sum_f_R0
                  (fun k => Derive (fun r => C n k * (Derive_n f (n - k) r * Derive_n g k r)) x)
                  n
                = sum_f_R0
                    (fun k =>
                       C n k
                       *
                       (
                         (Derive_n f (n - k + 1) x * Derive_n g k x)
                         +
                         (Derive_n f (n - k) x * Derive_n g (k + 1) x)
                       )
                    )
                    n) as e.
        {
          apply sum_eq; introv lin.
          rewrite Derive_scal; f_equal.
          repeat rewrite Nat.add_1_r; simpl.
          rewrite Derive_mult; auto.

          {
            destruct loc1 as [eps loc].
            pose proof (loc x) as h; clear loc.
            autodimp h hyp;[apply Hierarchy.ball_center|].
            pose proof (h (S (n - i))) as q; simpl in q; apply q; try omega.
          }

          {
            destruct loc2 as [eps loc].
            pose proof (loc x) as h; clear loc.
            autodimp h hyp;[apply Hierarchy.ball_center|].
            pose proof (h (S i)) as q; simpl in q; apply q; try omega.
          }
        }
        rewrite e; clear e.

        assert (sum_f_R0
                  (fun k : nat =>
                     C n k *
                     (Derive_n f (n - k + 1) x * Derive_n g k x +
                      Derive_n f (n - k) x * Derive_n g (k + 1) x))
                  n
                = sum_f_R0
                    (fun k : nat =>
                       (C n k * Derive_n f (n - k + 1) x * Derive_n g k x)
                       + (C n k *  Derive_n f (n - k) x * Derive_n g (k + 1) x))
                      n) as e.
        {
          apply sum_eq; introv lin.
          rewrite (Rmul_comm RTheory (C n i)).
          rewrite (Rdistr_l RTheory).
          repeat rewrite (Rmul_comm RTheory _ (C n i)).
          repeat rewrite (Rmul_assoc RTheory (C n i)).
          auto.
        }
        rewrite e; clear e.

        rewrite plus_sum.

        assert (sum_f_R0
                  (fun i : nat =>
                     C n i
                     * Derive_n f (n - i) x
                     * Derive_n g (i + 1) x)
                  n
                = sum_f
                    1
                    (S n)
                    (fun i : nat =>
                       C n (i - 1)
                       * Derive_n f (S n - i) x
                       * Derive_n g i x)
               ) as e.
        {
          rewrite Rcomplements.sum_f_u_Sk; try omega.
          rewrite Rcomplements.sum_f_rw_0.
          apply sum_eq; introv lin.
          simpl.
          rewrite minus0; auto.
          rewrite (Nat.add_comm i 1); simpl; auto.
        }
        rewrite e; clear e.

        rewrite <- Rcomplements.sum_f_rw_0.
        rewrite sum_f_decomp.
        rewrite minus0.

        destruct (le_lt_dec n 0) as [d|d].

        {
          assert (n = 0%nat) as h by omega; clear d; subst; simpl.
          unfold sum_f; simpl.
          rewrite (pascal_step1 1 0); auto; simpl.
          repeat rewrite Rcomplements.C_n_n.
          repeat rewrite Rplus_0_r.
          repeat rewrite Rmult_1_l; auto.
        }

        rewrite Rcomplements.sum_f_n_Sm; auto.

        assert (S n = n + 1)%nat as xx.
        { rewrite (Nat.add_comm n 1); auto. }
        rewrite xx; clear xx.
        simpl.

        rewrite (pascal_step1 n 0); auto; simpl; try omega.
        rewrite minus0.
        rewrite Nat.add_sub.
        rewrite Nat.sub_diag; simpl.
        repeat rewrite Rcomplements.C_n_n.
        repeat rewrite Rmult_1_l.

        rewrite (Rplus_comm _ (f x * Derive_n g (n + 1) x)).
        rewrite Rplus_assoc.
        rewrite <- (Rplus_assoc _ (f x * Derive_n g (n + 1) x)).
        rewrite (Rplus_comm _ (f x * Derive_n g (n + 1) x)).
        repeat rewrite Rplus_assoc.
        rewrite <- sum_f_plus.

        assert (sum_f
                  1 n
                  (fun l : nat =>
                     C n l * Derive_n f (n - l + 1) x * Derive_n g l x +
                     C n (l - 1) * Derive_n f (n + 1 - l) x * Derive_n g l x)
                = sum_f
                    1 n
                    (fun l : nat =>
                       C (n + 1) l
                       * Derive_n f (n + 1 - l) x
                       * Derive_n g l x)) as e.
        {
          apply sum_f_eq; try omega.
          introv h1 h2.
          rewrite <- Nat.add_sub_swap; auto.
          repeat (rewrite <- Rmult_plus_distr_r); auto.
          f_equal; f_equal.
          rewrite (Nat.add_comm n 1); simpl.
          destruct i; simpl; try omega.
          rewrite minus0.
          rewrite Rplus_comm.
          rewrite pascal; auto.
        }
        rewrite e; clear e.

        subst.
        rewrite tech5.

        assert (S n = n + 1)%nat as xx.
        { rewrite (Nat.add_comm n 1); auto. }
        rewrite xx; clear xx.

        repeat rewrite Rcomplements.C_n_n.
        rewrite Nat.sub_diag; simpl.
        repeat rewrite Rmult_1_l; auto.

        rewrite (Rplus_comm (f x * Derive_n g (n + 1) x)).
        rewrite <- Rplus_assoc.
        f_equal.

        rewrite <- Rcomplements.sum_f_rw_0.

        rewrite (sum_f_decomp 0).
        destruct (le_lt_dec n 0) as [w|w]; try omega;[].
        simpl.

        rewrite (pascal_step1 _ 0); try omega.
        rewrite minus0.
        repeat rewrite Rcomplements.C_n_n.
        repeat rewrite Rmult_1_l; auto.
        f_equal.
        apply sum_f_eq; auto.
        introv h1 h2.
        rewrite Rmult_assoc; auto.
      }

      {
        introv h.
        apply ex_derive_mult;[|apply ex_derive_mult].
        - apply @ex_derive_const.
        - destruct loc1 as [eps1 loc1].
          pose proof (loc1 x) as q; clear loc1.
          autodimp q hyp;[apply Hierarchy.ball_center|].
          pose proof (q (S (n - k))) as w; simpl in w; apply w; try omega.
        - destruct loc2 as [eps2 loc2].
          pose proof (loc2 x) as q; clear loc2.
          autodimp q hyp;[apply Hierarchy.ball_center|].
          pose proof (q (S k)) as w; simpl in w; apply w; try omega.
      }
    }

    {
      destruct loc1 as [eps1 loc1].
      destruct loc2 as [eps2 loc2].
      exists (posreal_min (posreal_half eps1) (posreal_half eps2)).
      introv b.
      apply IHn.

      {
        exists (posreal_half eps1); introv h1 h2; auto.
        apply loc1; auto.
        eapply Hierarchy.ball_triangle in h1;[|eauto].
        eapply Hierarchy.ball_le;[|eauto].
        simpl.

        pose proof (Rmin_l (eps1 / 2) (eps2 / 2)) as q1.
        apply (Rplus_le_compat_r (eps1 / 2)) in q1.
        eapply Rle_trans;[exact q1|clear q1].
        rewrite <- posreal_eq_two_halves; auto.
        apply Rle_refl.
      }

      {
        exists (posreal_half eps2); introv h1 h2; auto.
        apply loc2; auto.
        eapply Hierarchy.ball_triangle in h1;[|eauto].
        eapply Hierarchy.ball_le;[|eauto].
        simpl.

        pose proof (Rmin_r (eps1 / 2) (eps2 / 2)) as q1.
        apply (Rplus_le_compat_r (eps2 / 2)) in q1.
        eapply Rle_trans;[exact q1|clear q1].
        rewrite <- posreal_eq_two_halves; auto.
        apply Rle_refl.
      }
    }
Qed.

(** nth derivative of multiplication of two functions exists *)
Lemma ex_derive_n_mult :
  forall (f g : R -> R) (n : nat) (x : R),
    locally_R x (fun y => forall k, (k <= n)%nat -> ex_derive_n f k y)
    -> locally_R x (fun y => forall k, (k <= n)%nat -> ex_derive_n g k y)
    -> ex_derive_n (fun x => f x * g x) n x.
Proof.
  introv loc1 loc2.
  destruct n; simpl; auto.
  unfold ex_derive_n.
  apply (@ex_derive_ext_loc
           Hierarchy.R_AbsRing
           Hierarchy.R_NormedModule
           (fun x => (sum_f_R0 (fun k : nat => C n k * (Derive_n f (n - k) x * Derive_n g k x)) n))).

  {
    destruct loc1 as [eps1 loc1].
    destruct loc2 as [eps2 loc2].
    exists (posreal_min (posreal_half eps1) (posreal_half eps2)).
    introv b; symmetry.
    apply Derive_n_mult.

    {
      exists (posreal_half eps1); introv h1 h2; auto.
      apply loc1; auto.
      eapply Hierarchy.ball_triangle in h1;[|eauto].
      eapply Hierarchy.ball_le;[|eauto].
      simpl.

      pose proof (Rmin_l (eps1 / 2) (eps2 / 2)) as q1.
      apply (Rplus_le_compat_r (eps1 / 2)) in q1.
      eapply Rle_trans;[exact q1|clear q1].
      rewrite <- posreal_eq_two_halves; auto.
      apply Rle_refl.
    }

    {
      exists (posreal_half eps2); introv h1 h2; auto.
      apply loc2; auto.
      eapply Hierarchy.ball_triangle in h1;[|eauto].
      eapply Hierarchy.ball_le;[|eauto].
      simpl.

      pose proof (Rmin_r (eps1 / 2) (eps2 / 2)) as q1.
      apply (Rplus_le_compat_r (eps2 / 2)) in q1.
      eapply Rle_trans;[exact q1|clear q1].
      rewrite <- posreal_eq_two_halves; auto.
      apply Rle_refl.
    }
  }

  {
    apply ex_derive_sum_f_R0.
    introv h.
    apply ex_derive_scal.
    apply ex_derive_mult.
    - destruct loc1 as [eps1 loc1].
      pose proof (loc1 x) as q; clear loc1.
      autodimp q hyp;[apply Hierarchy.ball_center|].
      pose proof (q (S (n - k))) as w; clear q; apply w; try omega.
    - destruct loc2 as [eps2 loc2].
      pose proof (loc2 x) as q; clear loc2.
      autodimp q hyp;[apply Hierarchy.ball_center|].
      pose proof (q (S k)) as w; clear q; apply w; try omega.
  }
Qed.

Lemma ex_derive_n_mult_gen :
  forall (f g : R -> R) (n : nat) (x : R),
    (forall y k, (k <= n)%nat -> ex_derive_n f k y)
    -> (forall y k, (k <= n)%nat -> ex_derive_n g k y)
    -> ex_derive_n (fun x => f x * g x) n x.
Proof.
  introv imp1 imp2.
  apply ex_derive_n_mult; exists R1pos; auto.
Qed.

(** nth derivative of power of function exists *)
Lemma ex_derive_n_pow :
  forall (n m : nat) (f : R -> R) (pt : R),
    (forall pt k, (k <= n)%nat -> ex_derive_n f k pt)
    -> ex_derive_n (fun x => (f x) ^ m) n pt.
Proof.
  induction n as [n IHn] using comp_ind; introv loc; destruct n;[simpl;auto|].
  simpl.

  apply ex_derive_n_S_if; auto.

  {
    apply ex_derive_pow; auto.
    pose proof (loc pt 1%nat) as q1; simpl in q1; apply q1; try omega.
  }

  {
    apply (@ex_derive_n_ext (fun x => INR m * Derive f x * f x ^ Init.Nat.pred m) _).

    {
      introv.
      rewrite (Derive_pow f); auto; simpl.
      pose proof (loc t 1%nat) as q1; simpl in q1; apply q1; try omega.
    }

    {
      apply ex_derive_n_mult_gen; introv w1.

      {
        apply ex_derive_n_mult_gen; introv w2;
          [apply ex_derive_n_const|].
        pose proof (loc y0 (S k0)) as q.
        autodimp q hyp; try omega.
        apply ex_derive_n_S_implies; auto.
        pose proof (loc y0 1%nat) as z; apply z; try omega.
      }

      {
        pose proof (IHn k) as h; clear IHn.
        repeat (autodimp h hyp); try omega.
        pose proof (h (Nat.pred m) f y) as q.
        repeat (autodimp q hyp).
        introv w; apply loc; try omega.
      }
    }
  }
Qed.
