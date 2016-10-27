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

Require Export deriv_util.
Require Export multiplication.

(**

  This file implements relaxation of Faa di Bruno formula, which is presented in
  McKiernan's paper " On the nth Derivative of Composite Functions".
  Note: Faa di Bruno formula computes nth derivative of composition.

*)


Lemma Derive_n_composition_S :
  forall (f g : R -> R) (n : nat) (x : R),
    locally_R x (fun y => ex_derive_R f (g y))
    -> locally_R x (fun y => forall k, (k <= n)%nat -> ex_derive_n (fun x => Derive f (g x)) k y)
    -> locally_R x (fun y => forall k, (k <= S n)%nat -> ex_derive_n g k y)
    -> Derive_n (fun x => f (g x)) (S n) x
       = sum_f_R0 (fun k => (C n k)
                            * Derive_n (fun x => Derive f (g x)) k x
                            * Derive_n g (n + 1 - k) x) n.
Proof.
  introv locC loc1 loc2.
  rewrite Derive_n_S.
  rewrite (Derive_n_ext_loc
             (Derive (fun x : R => f (g x)))
             (fun x => Derive g x * Derive f (g x))); auto.

  {
    rewrite Derive_n_mult; auto.

    {
      apply sum_eq; introv z.
      rewrite Rmult_assoc.
      f_equal.
      rewrite Rmult_comm.
      f_equal.
      rewrite (Nat.add_comm n 1).
      rewrite <- minus_Sn_m; auto.
      rewrite Derive_n_S.
      auto.
    }

    {
      destruct loc2 as [eps2 loc2].
      exists eps2.
      introv h1 h2.
      pose proof (loc2 y h1 (S k)) as q.
      autodimp q hyp; try omega.
      simpl in q.
      destruct k; [simpl; auto|].
      simpl.
      apply (@ex_derive_ext
                 Hierarchy.R_AbsRing
                 Hierarchy.R_NormedModule
                 (Derive_n g (S k))
                 (Derive_n (Derive g) k)) in q; auto.
      introv; rewrite Derive_n_S; auto.
    }
  }

  {
    destruct locC as [eps1 locC].
    destruct loc2 as [eps2 loc2].

    exists (posreal_min eps1 eps2).
    introv b.

    pose proof (Derive_comp f g) as h.
    apply h.

    {
      apply locC.
      eapply Hierarchy.ball_le;try (exact b); simpl; try (apply Rmin_l).
    }

    {
      pose proof (loc2 y) as q.
      autodimp q hyp.
      { eapply Hierarchy.ball_le;try (exact b); simpl; try (apply Rmin_r). }
      pose proof (q 1%nat) as w; clear q; simpl in w; apply w; try omega.
    }
  }
Qed.

Lemma ex_derive_n_composition_loc1 :
  forall (f g : R -> R) (n : nat) (x : R),
    locally_R x (fun y => ex_derive_R f (g y))
    -> locally_R x (fun y => forall k, (k <= n)%nat -> ex_derive_n (fun x => Derive f (g x)) k y)
    -> locally_R x (fun y => forall k, (k <= S n)%nat -> ex_derive_n g k y)
    -> ex_derive_n (fun x => f (g x)) n x.
Proof.
  introv locC loc1 loc2.
  unfold ex_derive_n.
  destruct n; auto.
  destruct n.

  {
    simpl.
    apply (@ex_derive_comp
             Hierarchy.R_AbsRing
             Hierarchy.R_NormedModule
             f g).
    - destruct locC as [eps locC].
      apply locC; apply Hierarchy.ball_center.
    - destruct loc2 as [esp2 loc2].
      pose proof (loc2 x) as q; clear loc2.
      autodimp q hyp; try (apply Hierarchy.ball_center).
      pose proof (q 1%nat) as h; autodimp h hyp.
  }

  {
    apply (@ex_derive_ext_loc
             Hierarchy.R_AbsRing
             Hierarchy.R_NormedModule
             (fun x => sum_f_R0 (fun k => (C n k)
                                          * Derive_n (fun x => Derive f (g x)) k x
                                          * Derive_n g (n + 1 - k) x) n)).

    {
      destruct locC as [epsC locC].
      destruct loc1 as [eps1 loc1].
      destruct loc2 as [eps2 loc2].
      exists (posreal_min (posreal_min (posreal_half eps1) (posreal_half eps2)) (posreal_half epsC)).
      introv b; symmetry.
      apply Derive_n_composition_S.

      {
        exists (posreal_half epsC); introv h1; auto.
        apply locC; auto.
        eapply Hierarchy.ball_triangle in h1;[|eauto].
        eapply Hierarchy.ball_le;[|eauto].
        simpl.

        pose proof (Rmin_r (Rmin (eps1 / 2) (eps2 / 2)) (epsC / 2)) as q1.
        apply (Rplus_le_compat_r (epsC / 2)) in q1.
        eapply Rle_trans;[exact q1|clear q1].
        rewrite <- posreal_eq_two_halves; auto.
        apply Rle_refl.
      }

      {
        exists (posreal_half eps1); introv h1 h2; auto.
        apply loc1; auto.
        eapply Hierarchy.ball_triangle in h1;[|eauto].
        eapply Hierarchy.ball_le;[|eauto].
        simpl.

        pose proof (Rmin_l (eps1 / 2) (eps2 / 2)) as q1.
        pose proof (Rmin_l (Rmin (eps1 / 2) (eps2 / 2)) (epsC / 2)) as q2.
        apply (Rplus_le_compat_r (eps1 / 2)) in q2.
        eapply Rle_trans;[exact q2|clear q2].
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
        pose proof (Rmin_l (Rmin (eps1 / 2) (eps2 / 2)) (epsC / 2)) as q2.
        apply (Rplus_le_compat_r (eps2 / 2)) in q2.
        eapply Rle_trans;[exact q2|clear q2].
        apply (Rplus_le_compat_r (eps2 / 2)) in q1.
        eapply Rle_trans;[exact q1|clear q1].
        rewrite <- posreal_eq_two_halves; auto.
        apply Rle_refl.
      }
    }

    {
      apply ex_derive_sum_f_R0.
      introv h.
      apply ex_derive_mult.
      - apply @ex_derive_scal.
        destruct loc1 as [eps1 loc1].
        pose proof (loc1 x) as q; clear loc1.
        autodimp q hyp;[apply Hierarchy.ball_center|].
        pose proof (q (S k)) as w; clear q; apply w; try omega.
      - destruct loc2 as [eps2 loc2].
        pose proof (loc2 x) as q; clear loc2.
        autodimp q hyp;[apply Hierarchy.ball_center|].
        rewrite (Nat.add_comm n 1).
        rewrite <- minus_Sn_m; auto.
        pose proof (q (S (S (n - k)))) as w; clear q; apply w; try omega.
    }
  }
Qed.

Lemma ex_derive_n_composition :
  forall (n : nat) (f g : R -> R) (pt : R),
    (forall pt k, (k <= n)%nat -> ex_derive_n f k (g pt))
    -> (forall pt k, (k <= n)%nat -> ex_derive_n g k pt)
    -> ex_derive_n (fun x => f (g x)) n pt.
Proof.
  induction n as [n IHn] using comp_ind; introv loc1 loc2; destruct n;[simpl;auto|].
  simpl.

  apply ex_derive_n_S_if; auto.

  {
    apply (@ex_derive_comp Hierarchy.R_AbsRing Hierarchy.R_NormedModule f).
    { pose proof (loc1 pt 1%nat) as q1; simpl in q1; apply q1; try omega. }
    { pose proof (loc2 pt 1%nat) as q2; simpl in q2; apply q2; try omega. }
  }

  {
    apply (@ex_derive_n_ext (fun x => Derive g x * Derive f (g x)) _).

    { introv.
      rewrite (Derive_comp f g); auto; simpl.
      { pose proof (loc1 t 1%nat) as q1; simpl in q1; apply q1; try omega. }
      { pose proof (loc2 t 1%nat) as q2; simpl in q2; apply q2; try omega. }
    }

    {
      apply ex_derive_n_mult_gen; introv h.

      { pose proof (loc2 y (S k)) as q2.
        autodimp q2 hyp; try omega;[].
        apply ex_derive_n_S_implies in q2; auto.
        clear q2.
        pose proof (loc2 y 1%nat) as q2; simpl in q2; apply q2; try omega.
      }

      {
        pose proof (IHn k) as q; clear IHn.
        repeat (autodimp q hyp); try omega.
        pose proof (q (Derive f) g y) as w; clear q.
        repeat (autodimp w hyp); try (introv ltk).
        { pose proof (loc1 pt0 (S k0)) as q1; autodimp q1 hyp; try omega.
          apply ex_derive_n_S_implies in q1; auto.
          clear q1.
          pose proof (loc1 pt0 1%nat) as q2; simpl in q2; apply q2; try omega. }
        { pose proof (loc2 pt0 k0) as q2; simpl in q2; apply q2; try omega. }
      }
    }
  }
Qed.

Fixpoint compRec (g : R -> R) (n r : nat) (pt : R) : R :=
  if lt_dec n r then 0
  else
    match n with
    | 0 => 1
    | S n =>
      match r with
      | 0 => 0
      | S r => (Derive g pt * compRec g n r pt)
               + Derive (compRec g n (S r)) pt
      end
    end.

Lemma ex_derive_n_compRec :
  forall g n r pt m,
    (forall pt k, ex_derive_n g k pt)
    -> ex_derive_n (compRec g n r) m pt.
Proof.
  induction n; introv imp; simpl; dest_cases h;
    [apply @ex_derive_n_const
    |apply @ex_derive_n_const
    |apply @ex_derive_n_const
    |].

  destruct r;[apply @ex_derive_n_const|].
  apply @ex_derive_n_plus.

  {
    exists R1pos.
    introv h1 h2.
    apply @ex_derive_n_mult_gen; introv h3.

    {
      pose proof (imp y0 (S k0)) as q.
      apply ex_derive_n_S_implies; auto.
      clear q.
      pose proof (imp y0 1%nat) as q; auto.
    }

    {
      apply IHn; introv; apply imp; try omega.
    }
  }

  {
    exists R1pos.
    introv h1 h2.
    pose proof (IHn (S r) y (S k)) as q.
    autodimp q hyp.
    apply ex_derive_n_S_implies in q; auto.
    clear q.
    pose proof (IHn (S r) y 1%nat) as q.
    autodimp q hyp.
  }
Qed.

Lemma ex_derive_compRec :
  forall g n r pt,
    (forall pt k, ex_derive_n g k pt)
    -> ex_derive_R (compRec g n r) pt.
Proof.
  introv imp.
  pose proof (ex_derive_n_compRec g n r pt 1 imp) as h.
  auto.
Qed.

Lemma compRec_Sn_0 :
  forall g n pt, (0 < n)%nat -> compRec g n 0 pt = 0.
Proof.
  introv h.
  destruct n; simpl; auto; try omega.
Qed.

Lemma compRec_lt :
  forall g n m pt, (n < m)%nat -> compRec g n m pt = 0.
Proof.
  introv h.
  simpl.
  destruct n; simpl; dest_cases w.
Qed.

(* This is formula (4n) of "On the nth derivative of composite functions" *)
Lemma Derive_n_composition :
  forall (f g : R -> R) (n : nat) (pt : R),
    (n > 0)%nat
    -> (forall pt k, (k <= n)%nat -> ex_derive_n f k (g pt))
    -> (forall pt k, ex_derive_n g k pt)
    -> Derive_n (fun x => f (g x)) n pt
       = sum_f
           1 n
           (fun r => Derive_n f r (g pt) * compRec g n r pt).
Proof.
  induction n; introv gtn loc1 loc2; try omega.
  (* not dealing with n = 0 *)

  remember (sum_f 1 (S n) (fun r : nat => Derive_n f r (g pt) * compRec g (S n) r pt)) as R.

  simpl.
  destruct n.

  {
    (* case n = 1 is trivial *)
    subst R; simpl.
    rewrite Rcomplements.sum_f_u_Sk; auto.
    unfold sum_f; simpl.
    rewrite Derive_const.
    rewrite Rmult_1_r.
    rewrite Rplus_0_r.
    rewrite Derive_comp; auto.

    { rewrite Rmult_comm; auto. }

    { pose proof (loc1 pt 1%nat) as q; apply q; auto. }

    { pose proof (loc2 pt 1%nat) as q; apply q; auto. }
  }

  (* case n > 1 *)
  remember (S n) as m.
  assert (m > 0)%nat as gtm by omega.
  clear dependent n.
  clear gtn.

  rewrite (Derive_ext
             _
             (fun pt => sum_f 1 m (fun r : nat => Derive_n f r (g pt) * compRec g m r pt)));
    [|introv; apply IHn; auto].

  rewrite Derive_sum_f; auto;
    [|introv h1 h2;
      apply ex_derive_mult;
      [apply (@ex_derive_comp
                Hierarchy.R_AbsRing
                Hierarchy.R_NormedModule
                (Derive_n f k))|];
      [pose proof (loc1 pt (S k)) as q1; simpl in q1; autodimp q1 hyp; try omega
      |pose proof (loc2 pt 1%nat) as q2; simpl in q2; apply q2; try omega
      |apply ex_derive_compRec;auto]
    ].

  pose proof (sum_f_eq
                (fun k => Derive (fun r => Derive_n f k (g r) * compRec g m k r) pt)
                (fun k => (Derive_n f (S k) (g pt) * Derive g pt * compRec g m k pt)
                          + (Derive_n f k (g pt) * Derive (compRec g m k) pt))
                1 m) as e.
  repeat (autodimp e hyp);[|].
  {
    introv h1 h2.
    rewrite Derive_mult; auto;
      [|apply (@ex_derive_comp
                 Hierarchy.R_AbsRing
                 Hierarchy.R_NormedModule
                 (Derive_n f i)); auto;
        [pose proof (loc1 pt (S i)) as q1; simpl in q1; autodimp q1 hyp; try omega
        |pose proof (loc2 pt 1%nat) as q2; simpl in q2; apply q2; try omega]
       |apply ex_derive_compRec;auto];[].
    f_equal.
    f_equal.
    rewrite (Derive_comp (Derive_n f i)); auto;
      [rewrite Rmult_comm;auto
      |pose proof (loc1 pt (S i)) as q1; simpl in q1; autodimp q1 hyp; try omega
      |pose proof (loc2 pt 1%nat) as q2; simpl in q2; apply q2; try omega].
  }
  rewrite e; clear e.

  rewrite sum_f_plus.

  pose proof (Rcomplements.sum_f_u_Sk
                (fun l => Derive_n f l (g pt) * Derive g pt * compRec g m (l - 1) pt)
                1 m)
    as h.
  simpl in h.
  autodimp h hyp.
  rewrite (sum_f_eq
             _
             (fun k => Derive (Derive_n f k) (g pt) * Derive g pt * compRec g m k pt)
             1 m)
    in h ;auto;[|introv h1 h2; rewrite minus0; auto].
  simpl; rewrite <- h; clear h.

  pose proof (sum_f_decomp
                1 (S m)
                (fun l => Derive_n f l (g pt) * Derive g pt * compRec g m (l - 1) pt))
    as h.
  dest_cases w; try omega;[].
  simpl in h.
  rewrite compRec_Sn_0 in h; auto.
  rewrite Rmult_0_r in h.
  rewrite Rplus_0_l in h.
  rewrite <- h.
  clear h.

  pose proof (Rcomplements.sum_f_n_Sm
                (fun l0 => Derive_n f l0 (g pt) * Derive (compRec g m l0) pt)
                1 m) as h.
  autodimp h hyp.
  simpl in h.

  rewrite (Derive_constant_fun (compRec g m (S m)) R0 pt) in h;
    [|introv; rewrite compRec_lt; auto].
  rewrite Rmult_0_r in h.
  rewrite Rplus_0_r in h.
  rewrite <- h.
  clear h.

  rewrite <- sum_f_plus.
  subst R.
  apply sum_f_eq; auto.
  introv h1 h2.

  rewrite Rmult_assoc.
  rewrite <- Rmult_plus_distr_l.
  f_equal.
  simpl.
  dest_cases w; try omega;[].
  destruct i; try omega;[].
  simpl.
  rewrite minus0; auto.
Qed.

Definition instF (k : nat) (x : R) : R := (x^k) / INR (fact k).

Lemma ex_derive_n_instF :
  forall k n x, ex_derive_n (instF k) n x.
Proof.
  introv.
  apply ex_derive_n_scal_r.
  apply ex_derive_n_id_pow.
Qed.

Definition pow_f (g : R -> R) (n : nat) (x : R) := (g x)^n.

Lemma sum_f_decomp :
  forall f n m k,
    (n <= k)%nat
    -> (k <= m)%nat
    -> sum_f n m f
       = (if lt_dec n k then sum_f n (k - 1) f else 0)
         + f k
         + (if le_dec (k + 1) m then sum_f (k + 1) m f else 0).
Proof.
  introv h1 h2.

  unfold sum_f.

  destruct (deq_nat k m) as [d|d]; subst.

  {
    destruct (le_dec (m + 1) m) as [d|d]; try omega.
    rewrite Rplus_0_r.

    destruct (deq_nat m n) as [d1|d1]; subst.

    {
      destruct (le_dec n n) as [d1|d1]; try omega.
      rewrite Nat.sub_diag; simpl.
      destruct (lt_dec n n) as [d2|d2]; try omega.
      rewrite Rplus_0_l; auto.
    }

    {
      destruct (lt_dec n m) as [d2|d2]; try omega.
      rewrite (S_pred m n); auto.
      pose proof (tech5 (fun x => f (x + n)%nat) ((Init.Nat.pred m) - n)) as h.
      rewrite minus_Sn_m in h; try omega.
      rewrite h; clear h.
      rewrite Nat.sub_add; try omega.
      simpl.
      rewrite minus0; auto.
    }
  }

  {
    pose proof (tech2 (fun x => f (x + n)%nat) (k - 1 - n) (m - n)) as h.
    autodimp h hyp; try omega.
    rewrite h; clear h.
    destruct (lt_dec n k) as [d1|d1].

    {
      rewrite Rplus_assoc; f_equal.
      repeat (rewrite minus_Sn_m; try omega;[]).
      simpl; rewrite minus0.
      rewrite <- Nat.sub_add_distr.
      rewrite le_plus_minus_r; try omega;[].
      rewrite (decomp_sum _ (m - k)); try omega;[].
      rewrite Nat.add_0_r.
      rewrite Nat.sub_add; auto;[].
      f_equal.
      destruct (le_dec (k + 1) m) as [d2|d2]; try omega;[].
      rewrite <- Nat.sub_succ_r.
      rewrite (plus_comm k 1); simpl.
      apply sum_eq; introv w.

      rewrite <- plus_assoc.
      rewrite (plus_comm (S i) n).
      rewrite plus_assoc.
      rewrite Nat.sub_add; try omega.
      repeat (rewrite <- plus_n_Sm).
      rewrite (plus_comm k i); auto.
    }

    {
      assert (k = n) as xx by omega; subst.
      assert ((n - 1 - n)%nat = 0%nat) as xx by omega.
      rewrite xx; simpl; clear xx.
      rewrite Rplus_0_l.
      f_equal.
      destruct (le_dec (n + 1) m) as [d2|d2]; try omega.
      rewrite Nat.sub_add_distr.
      apply sum_eq.
      introv w.
      rewrite (plus_comm n 1); auto.
    }
  }
Qed.

Lemma compRec_n_1 :
  forall g n pt, (0 < n)%nat -> compRec g n 1 pt = Derive_n g n pt.
Proof.
  induction n; introv h; simpl; auto; try omega.
  destruct (deq_nat n 0) as [d|d]; subst.

  {
    simpl.
    rewrite Rmult_1_r.
    rewrite Derive_const.
    rewrite Rplus_0_r; auto.
  }

  {
    assert (0 < n)%nat as q by omega.
    clear h d.
    rewrite compRec_Sn_0; auto.
    rewrite Rmult_0_r.
    rewrite Rplus_0_l.
    apply Derive_ext; introv; auto.
  }
Qed.

Lemma pow_f_1 : forall g pt, pow_f g 1 pt = g pt.
Proof.
  unfold pow_f; simpl; introv.
  autorewrite with core; auto.
Qed.
Hint Rewrite pow_f_1 : core.

Lemma pow_f_0 : forall g pt, pow_f g 0 pt = 1.
Proof.
  unfold pow_f; simpl; introv.
  autorewrite with core; auto.
Qed.
Hint Rewrite pow_f_0 : core.

Lemma Derive_n_pow_f_1 :
  forall g n pt, Derive_n (pow_f g 1) n pt = Derive_n g n pt.
Proof.
  introv.
  apply Derive_n_ext; introv.
  autorewrite with core; auto.
Qed.
Hint Rewrite Derive_n_pow_f_1 : core.

Lemma Derive_n_pow_f_0 :
  forall g n pt, (0 < n)%nat -> Derive_n (pow_f g 0) n pt = 0.
Proof.
  introv h.
  rewrite (Derive_n_ext _ (fun _ => 1)); auto.
  destruct n; try omega.
  rewrite Derive_n_const; auto.
Qed.

(* This is formula (7n,k) of "On the nth derivative of composite functions" *)
Lemma compRec_prop1 :
  forall (g : R -> R) (n k : nat) pt,
    (0 < n)%nat
    -> (0 <= k)%nat
    -> (k <= n)%nat
    -> (forall pt k, ex_derive_n g k pt)
    -> compRec g n k pt
       = ((1 / (INR (fact k))) * (Derive_n (pow_f g k) n pt))
         - (sum_f_R0
              (fun r => ((pow_f g (k - r) pt) / (INR (fact (k - r)))) * (compRec g n r pt))
              (k - 1)%nat).
Proof.
  introv h1 h2 h3 Hdg.

  pose proof (Derive_n_composition (instF k) g n pt) as h.
  repeat (autodimp h hyp).
  { introv q; apply ex_derive_n_instF. }
  unfold instF in h; simpl in h.
  rewrite (Derive_n_ext _ (fun x => g x ^ k  * / INR (fact k))) in h;
    [|introv;rewrite (Fdiv_def Rfield);auto];[].
  rewrite Derive_n_scal_r in h.
  rewrite <- (Fdiv_def Rfield) in h.

  assert
    (sum_f
       1 n
       (fun r =>
          Derive_n (fun x : R => x ^ k / INR (fact k)) r (g pt) * compRec g n r pt)
     = sum_f
         1 n
         (fun r =>
            Derive_n (fun x : R => x ^ k) r (g pt) / INR (fact k) * compRec g n r pt))
    as xx1.
  {
    apply sum_eq; introv q.
    rewrite (Derive_n_ext
               (fun x : R => x ^ k / INR (fact k))
               (fun x : R => x ^ k * / INR (fact k)));
      [|introv;rewrite (Fdiv_def Rfield);auto];[].
    rewrite Derive_n_scal_r; auto.
  }
  rewrite xx1 in h; clear xx1.

  destruct (deq_nat k 0) as [d|d]; subst.

  {
    simpl in *.
    rewrite compRec_Sn_0; auto; simpl.
    autorewrite with core.
    unfold pow_f; simpl.
    destruct n; try omega.
    rewrite Derive_n_const; auto.
  }

  pose proof (sum_f_decomp
                (fun r =>
                   Derive_n (fun x : R => x ^ k) r (g pt) / INR (fact k)
                   * compRec g n r pt)
                1 n k) as xx.
  repeat (autodimp xx hyp); try omega.
  rewrite xx in h; clear xx.

  destruct (deq_nat k 1) as [d1|d1].

  {
    subst.
    simpl in *.
    rewrite compRec_Sn_0; auto; simpl.
    autorewrite with core.
    rewrite compRec_n_1; auto.
  }

  destruct (lt_dec 1 k) as [d2|d2]; try omega;[].

  match type of h with
  | _ = _ + _ + ?x => assert (x = 0) as xx
  end.
  {
    destruct (le_dec (k + 1) n) as [d3|d3]; auto; try omega.
    apply sum_eq_R0; introv q.
    rewrite Derive_n_id_pow.
    destruct (lt_dec k (n0 + (k + 1))); try omega.
    rewrite zero_div_is_zero;[|apply INR_fact_neq_0].
    autorewrite with core; auto.
  }
  rewrite xx in h; clear xx.
  autorewrite with core in *.

  match type of h with
  | _ = _ + (?x * _) => assert (x = 1) as xx
  end.
  {
    rewrite Derive_n_id_pow.
    destruct (lt_dec k k); try omega.
    autorewrite with core.
    rewrite (Fdiv_def Rfield).
    rewrite Rmult_comm.
    rewrite (Finv_l Rfield); auto.
    apply INR_fact_neq_0.
  }
  rewrite xx in h; clear xx.
  autorewrite with core in *.

  match type of h with
  | ?a = ?b + ?c => assert (c = a - b) as q
  end.
  {
    rewrite h.
    rewrite Rplus_minus_comm.
    autorewrite with core; auto.
  }
  clear h.

  rewrite (Fdiv_def Rfield) in q.
  rewrite (Fdiv_def Rfield).
  rewrite Rmult_comm in q.
  autorewrite with core.

  rewrite q.
  f_equal;[].

  rewrite decomp_sum; simpl; try omega;[].
  autorewrite with core.
  rewrite compRec_Sn_0; auto.
  autorewrite with core.

  unfold sum_f; simpl.
  rewrite <- Rcomplements.MyNat.sub_succ_r.
  rewrite <- Nat.sub_add_distr; simpl.

  apply sum_eq; introv w.
  rewrite (plus_comm i 1).
  f_equal;[].
  rewrite Derive_n_id_pow; simpl.
  destruct (lt_dec k (S i)); try omega;[].
  rewrite (Fdiv_def Rfield).
  rewrite (Rmult_comm _ (g pt ^ (k - S i))).
  rewrite Rmult_assoc.
  repeat rewrite (Fdiv_def Rfield).
  f_equal.
  rewrite Rmult_assoc.
  rewrite (Rmult_comm _ (/ INR (fact k))).
  rewrite <- Rmult_assoc.
  rewrite (Rmult_comm _ (/ INR (fact k))).
  rewrite (Finv_l Rfield);[|apply INR_fact_neq_0].
  autorewrite with core; auto.
Qed.

Lemma minus1_mult : forall r, -1 * r = - r.
Proof.
  introv.
  rewrite <- Rminus_0_l.
  rewrite Rcomplements.Rmult_minus_distr_r.
  autorewrite with core.
  rewrite <- Rminus_0_l; auto.
Qed.

Lemma pow_f_add :
  forall g n m x, pow_f g n x * pow_f g m x = pow_f g (n + m) x.
Proof.
  introv.
  unfold pow_f.
  rewrite pow_add; auto.
Qed.

Lemma sum_f_same :
  forall n g, sum_f n n g = g n.
Proof.
  introv; unfold sum_f; autorewrite with core; simpl; auto.
Qed.
Hint Rewrite sum_f_same : core.

Lemma sum_sum_prop1 :
  forall F G (r : nat),
    sum_f_R0 (fun k => sum_f_R0 (fun s => F k s * G s) k) r
    = sum_f_R0 (fun s => G s * sum_f s r (fun k => F k s)) r.
Proof.
  induction r.

  {
    simpl; autorewrite with core.
    unfold sum_f; simpl.
    rewrite Rmult_comm; auto.
  }

  {
    rewrite tech5.
    rewrite IHr; clear IHr.
    repeat rewrite tech5.
    autorewrite with core.
    rewrite <- Rplus_assoc.
    rewrite (Rmult_comm (G (S r))).
    f_equal;[].
    rewrite <- sum_plus.
    apply sum_eq; introv w.

    rewrite (Rmult_comm _ (G i)).
    rewrite <- Rmult_plus_distr_l.
    f_equal.
    rewrite Rcomplements.sum_f_n_Sm; auto.
  }
Qed.

Lemma scal_sum_f_r :
  forall (An : nat -> R) (n m : nat) (x : R),
    sum_f n m (fun i : nat => An i * x) = x * sum_f n m An.
Proof.
  introv.
  unfold sum_f.
  rewrite scal_sum; auto.
Qed.

Lemma scal_sum_f_l :
  forall (An : nat -> R) (n m : nat) (x : R),
    sum_f n m (fun i : nat => x * An i) = x * sum_f n m An.
Proof.
  introv.
  unfold sum_f.
  rewrite scal_sum; auto.
  apply sum_eq; introv w.
  rewrite Rmult_comm; auto.
Qed.

Lemma sum_f_R0_fact_prop1 :
  forall n,
    (0 < n)%nat
    -> sum_f_R0 (fun x => (-1) ^ x / INR (fact (n - x) * fact x)) (n - 1)
       = (-1) ^ (n - 1) * / INR (fact n).
Proof.
  introv ltn.
  pose proof (binomial (-1) 1 n) as h.
  unfold C in h.
  autorewrite with core in *.
  rewrite pow_i in h; auto;[].
  rewrite sum_N_predN in h; auto.
  rewrite <- Nat.sub_1_r in h.
  autorewrite with core in h.
  rewrite (Fdiv_def Rfield) in h.
  rewrite (Rmult_comm (INR (fact n))) in h.
  rewrite Rinv_l in h; try (apply INR_fact_neq_0);[].
  autorewrite with core in *.

  match goal with
  | [ H : _ = ?x + ?y |- _ ] => assert ((x + y) - y = -y) as q
  end.
  {
    rewrite <- h.
    autorewrite with core; auto.
  }
  clear h.
  rewrite (Rsub_def RTheory) in q.
  rewrite Rplus_assoc in q.
  rewrite <- (Rsub_def RTheory) in q.
  autorewrite with core in q.

  match goal with
  | [ H : ?x = _ |- _ ] =>
    assert (x = INR (fact n)
                * sum_f_R0
                    (fun i => (-1) ^ i / (INR (fact (n - i) * (fact i))))
                    (n - 1)) as h
  end.
  {
    rewrite scal_sum.
    apply sum_eq; introv w.
    autorewrite with core.
    repeat rewrite (Fdiv_def Rfield).
    repeat (rewrite Rinv_mult_distr;
            try (rewrite mult_INR);
            try (apply Rmult_integral_contrapositive;dands);
            try (apply INR_fact_neq_0);[]).
    rewrite (Rmult_comm _ ((-1) ^ i)).
    repeat rewrite Rmult_assoc.
    f_equal;[].
    repeat rewrite <- Rmult_assoc.
    rewrite (Rmult_comm _ (INR (fact n))).
    rewrite (Rmult_comm (/ INR (fact (n - i)))).
    repeat rewrite <- Rmult_assoc; auto.
  }

  rewrite h in q; clear h.
  apply (Rmult_eq_compat_r (/ INR (fact n))) in q.
  rewrite (Rmult_comm (INR (fact n))) in q.
  rewrite Rmult_assoc in q.
  rewrite (Rmult_comm (INR (fact n))) in q.
  rewrite Rinv_l in q; try (apply INR_fact_neq_0);[].
  autorewrite with core in q.
  rewrite q; clear q.
  rewrite <- minus1_mult.
  destruct n; simpl; autorewrite with core; try omega.
  rewrite <- Rmult_assoc.
  rewrite minus1_mult.
  autorewrite with core; auto.
Qed.

(* This is formula (8n,r) of "On the nth derivative of composite functions" *)
Lemma compRec_prop2 :
  forall g n r pt,
    (1 <= r)%nat
    -> (r <= n)%nat
    -> (forall pt k, ex_derive_n g k pt)
    -> compRec g n r pt
       = sum_f_R0
           (fun s =>
              ((pow (-1) (r - s) / INR ((fact s) * (fact (r - s))))
               * pow_f g (r - s) pt
               * Derive_n (pow_f g s) n pt))
           r.
Proof.
  induction r as [r IH] using comp_ind; introv h1 h2 Hdg; try omega.

  destruct (deq_nat r 1) as [d1|d1]; subst.

  {
    rewrite compRec_n_1; auto;[].
    simpl.
    autorewrite with core.
    rewrite Derive_n_pow_f_0; auto;[].
    autorewrite with core; auto.
  }

  rewrite compRec_prop1; auto; try omega;[].
  symmetry.
  assert (sum_f_R0
            (fun k => pow_f g (r - k) pt / INR (fact (r - k))
                      * compRec g n k pt)
            (r - 1)
          = sum_f_R0
              (fun k =>
                 (pow_f g (r - k) pt / INR (fact (r - k)))
                 * sum_f_R0
                     (fun s : nat =>
                        (((-1) ^ (k - s))
                           / INR (fact s * fact (k - s)) * pow_f g (k - s) pt)
                        * Derive_n (pow_f g s) n pt)
                     k)
              (r - 1)) as xx.
  {
    apply sum_eq; introv w.
    f_equal.
    destruct (deq_nat i 0) as [d2|d2]; subst.
    {
      simpl; autorewrite with core.
      rewrite compRec_Sn_0; try omega.
      rewrite Derive_n_pow_f_0; auto; try omega.
    }
    apply IH; auto; try omega.
  }
  rewrite xx; clear xx.
  clear IH.

  rewrite (sum_N_predN _ r); auto;[].
  rewrite Rplus_comm.
  rewrite (Rsub_def RTheory).
  autorewrite with core; simpl.
  f_equal;[].
  rewrite <- Nat.sub_1_r.

  match goal with
  | [ |- _ = - ?x ] =>
    assert (x = sum_f_R0
                  (fun k =>
                     sum_f_R0
                       (fun s =>
                          ((-1) ^ (k - s) / INR (fact (r - k) * fact s * fact (k - s)))
                          * pow_f g (r - s) pt
                          * Derive_n (pow_f g s) n pt)
                       k)
                  (r - 1)) as xx
  end.
  {
    apply sum_eq; introv w1.
    rewrite scal_sum.
    apply sum_eq; introv w2.

    rewrite Rmult_assoc.
    rewrite (Rmult_comm (Derive_n (pow_f g i0) n pt)).
    rewrite <- Rmult_assoc.
    f_equal;[].

    rewrite Rmult_assoc.
    repeat rewrite (Fdiv_def Rfield).
    rewrite <- (Rmult_assoc (pow_f g (i - i0) pt)).
    rewrite pow_f_add.
    assert ((i - i0 + (r - i))%nat = (r - i0)%nat) as xx by omega.
    rewrite xx; clear xx.

    rewrite Rmult_assoc.
    rewrite (Rmult_comm (pow_f g (r - i0) pt)).
    repeat rewrite <- Rmult_assoc.
    f_equal;[].

    rewrite Rmult_assoc.
    f_equal;[].

    rewrite <- Rinv_mult_distr;
      [|rewrite mult_INR;
        apply Rmult_integral_contrapositive;
        dands; apply INR_fact_neq_0
       |apply INR_fact_neq_0
      ];[].
    rewrite <- mult_INR.
    rewrite (mult_comm _ (fact (r - i))).
    rewrite mult_assoc; auto.
  }
  rewrite xx; clear xx.

  rewrite sum_sum_prop1.

  match goal with
  | [ |- _ = ?x ] =>
    assert (x = sum_f_R0
                  (fun s =>
                     - sum_f
                         s (r - 1)
                         (fun k =>
                            ((-1) ^ (k - s) / INR (fact (r - k) * fact s * fact (k - s))))
                       * pow_f g (r - s) pt
                       * Derive_n (pow_f g s) n pt)
                  (r - 1)) as xx
  end.
  {
    rewrite <- minus1_mult.
    rewrite scal_sum.
    apply sum_eq; introv w.
    rewrite <- (minus1_mult (sum_f _ _ _)).
    rewrite (Rmult_comm _ (-1)).
    repeat rewrite Rmult_assoc.
    f_equal;[].
    repeat rewrite <- Rmult_assoc.
    rewrite (Rmult_comm _ (Derive_n (pow_f g i) n pt)).
    f_equal;[].
    rewrite scal_sum_f_r.
    rewrite (Rmult_comm _ (pow_f g (r - i) pt)).
    auto.
  }
  rewrite xx; clear xx.

  apply sum_eq.
  introv w.
  repeat rewrite Rmult_assoc.
  f_equal;[].

  match goal with
  | [ |- _ = - ?x ] =>
    assert (x = sum_f
                    i (r - 1)
                    (fun k =>
                       / INR (fact i)
                       * ((-1) ^ (k - i) / INR (fact (r - k) * fact (k - i))))) as xx
  end.
  {
    apply sum_f_eq; auto.
    introv w1 w2.
    repeat rewrite (Fdiv_def Rfield).
    repeat rewrite mult_INR.
    repeat (rewrite Rinv_mult_distr;
            try (rewrite mult_INR);
            try (apply Rmult_integral_contrapositive;dands);
            try (apply INR_fact_neq_0);[]).
    repeat rewrite Rmult_assoc.
    rewrite (Rmult_comm (/ INR (fact i))).
    repeat rewrite <- Rmult_assoc.
    rewrite (Rmult_comm _ (/ INR (fact i))).
    repeat rewrite <- Rmult_assoc.
    auto.
  }
  rewrite xx; clear xx.
  rewrite scal_sum_f_l.
  unfold sum_f.

  rewrite <- (minus1_mult (_ * _)).
  rewrite <- Rmult_assoc.
  match goal with
  | [ |- _ = _ * ?z ] =>
    assert (z = sum_f_R0
                  (fun x =>
                     (-1) ^ x / INR (fact (r - x - i) * fact x))
                  (r - 1 - i)) as xx
  end.
  {
    apply sum_eq.
    introv w1.
    rewrite <- Nat.add_sub_assoc; auto.
    autorewrite with core.
    rewrite Nat.sub_add_distr; auto.
  }
  rewrite xx; clear xx.

  repeat rewrite (Fdiv_def Rfield).
  repeat rewrite mult_INR.
  repeat (rewrite Rinv_mult_distr;
          try (rewrite mult_INR);
          try (apply Rmult_integral_contrapositive;dands);
          try (apply INR_fact_neq_0);[]).
  rewrite (Rmult_comm (/ INR (fact i))).
  repeat rewrite <- Rmult_assoc.
  repeat rewrite (Rmult_comm _ (/ INR (fact i))).
  repeat rewrite Rmult_assoc.
  f_equal;[].

  pose proof (sum_f_R0_fact_prop1 (r - i)) as h.
  autodimp h hyp; try omega;[].
  assert ((r - i - 1)%nat = (r - 1 - i)%nat) as xx by omega.
  rewrite xx in h; clear xx.

  match goal with
  | [ H : sum_f_R0 ?f ?z = _ |- _ ] =>
    assert (sum_f_R0 f z
            = sum_f_R0
                (fun x => (-1) ^ x / INR (fact (r - x - i) * fact x))
                z) as xx
  end.
  {
    apply sum_eq.
    introv w1.
    assert ((r - i - i0)%nat = (r - i0 - i)%nat) as xx by omega.
    rewrite xx; auto.
  }
  rewrite xx in h; clear xx.
  rewrite h; clear h.

  rewrite <- Rmult_assoc.
  f_equal;[].
  rewrite tech_pow_Rmult.
  f_equal; omega.
Qed.

Lemma Derive_n_composition_mckiernan :
  forall (f g : R -> R) (n : nat) (pt : R),
    (n > 0)%nat
    -> (forall pt k, (k <= n)%nat -> ex_derive_n f k (g pt))
    -> (forall pt k, ex_derive_n g k pt)
    -> Derive_n (fun x => f (g x)) n pt
       = sum_f
           1 n
           (fun r =>
              Derive_n f r (g pt)
              * sum_f_R0
                  (fun s =>
                     ((pow (-1) (r - s) / INR ((fact s) * (fact (r - s))))
                      * pow_f g (r - s) pt
                      * Derive_n (pow_f g s) n pt))
                  r).
Proof.
  introv h1 h2 h3.
  rewrite Derive_n_composition; auto.
  apply sum_eq; introv w.
  rewrite <- compRec_prop2; auto; try omega.
Qed.
