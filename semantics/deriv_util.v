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

Require Export tactics_util.
Require Export reals_util.
Require Export Coquelicot.Derive.
Require Export Eqdep_dec.
Require Export Omega.


(**

  This file contains some definitions and lemmas about nth derivatives
  of functions.

  Note: In order to define dynamic semantics of programs, we
  introduced posreal definition.  Posreal stand for positive real,
  i.e., the type of real numbers that are greater or equal than zero.

 *)


Definition locally_R   := @Coquelicot.Hierarchy.locally (Coquelicot.Hierarchy.AbsRing_UniformSpace Coquelicot.Hierarchy.R_AbsRing).
Definition ex_derive_R := @ex_derive Coquelicot.Hierarchy.R_AbsRing Hierarchy.R_NormedModule.
Definition is_derive_R := @is_derive Hierarchy.R_AbsRing Hierarchy.R_NormedModule.

Definition ex_derive_all f := forall pt, ex_derive_R f pt.

Lemma is_derive_sum_f_R0 :
  forall (f : R -> nat -> R) x n,
    (forall k, (k <= n)%nat -> ex_derive_R (fun r => f r k) x)
    -> is_derive_R
         (fun x => sum_f_R0 (f x) n)
         x
         (sum_f_R0 (fun k => Derive (fun r => f r k) x) n).
Proof.
  induction n; introv imp; simpl; auto.

  {
    pose proof (imp 0%nat) as q; clear imp.
    autodimp q hyp.
    apply Derive_correct; auto.
  }

  {
    autodimp IHn hyp.
    apply @is_derive_plus; auto.
    apply Derive_correct; auto.
    apply imp; auto.
  }
Qed.

Lemma is_derive_sum_f_R0_dep :
  forall (f : R -> nat -> R) x n
         (imp : forall k, (k <=? n)%nat = true -> {d : R & is_derive_R (fun r => f r k) x d}),
    is_derive_R
      (fun x => sum_f_R0 (f x) n)
      x
      (sum_f_R0 (fun k => match le_dec k n with
                          | left p => projT1 (imp k (leb_correct _ _ p))
                          | _  => R0
                          end) n).
Proof.
  induction n; introv; simpl; auto.

  {
    match goal with | [ |- context[imp ?x ?y] ] => remember (imp x y) as h end.
    destruct h; simpl; auto.
  }

  {
    apply @is_derive_plus.

    {
      pose proof (IHn (fun k p => imp k (leb_correct _ _ (le_S k n (leb_complete _ _ p))))) as h;
        clear IHn; simpl in h.

      match goal with
      | [ H : is_derive_R _ _ ?d1 |- is_derive _ _ ?d2 ] =>
        let h := fresh "h" in assert (d1 = d2) as h;[|rewrite <- h;auto]
      end.
      apply sum_eq; introv q.
      destruct (le_dec i n) as [z|z];
        destruct (le_dec i (S n)) as [w|w];
        auto;
        try (complete omega);[].

      rewrite (UIP_dec
                 bool_dec
                 (leb_correct i (S n) (le_S i n (leb_complete i n (leb_correct i n z))))
                 (leb_correct i (S n) w)).
      auto.
    }

    {
      destruct (le_dec (S n) (S n)); try omega;[].
      match goal with | [ |- context[imp ?x ?y] ] => remember (imp x y) as h end.
      destruct h; simpl; auto.
    }
  }
Qed.

Lemma Derive_sum_f_R0 :
  forall (f : R -> nat -> R) x n,
    (forall k, (k <= n)%nat -> ex_derive_R (fun r => f r k) x)
    -> Derive (fun r => sum_f_R0 (f r) n) x
       = sum_f_R0 (fun k => Derive (fun r => f r k) x) n.
Proof.
  induction n; introv imp; simpl; auto.
  rewrite Derive_plus; auto;
    [rewrite IHn; auto| |apply imp; auto].
  exists (sum_f_R0 (fun k => Derive (fun r => f r k) x) n).
  apply is_derive_sum_f_R0; auto.
Qed.

Lemma ex_derive_sum_f_R0 :
  forall (f : R -> nat -> R) x n,
    (forall k, (k <= n)%nat -> ex_derive_R (fun r => f r k) x)
    -> ex_derive_R (fun r => sum_f_R0 (f r) n) x.
Proof.
  introv imp.
  exists (sum_f_R0 (fun k => Derive (fun r => f r k) x) n).
  apply is_derive_sum_f_R0; auto.
Qed.

Lemma sum_f_decomp :
  forall n m f,
    sum_f n m f = f n + if le_lt_dec m n then 0 else sum_f (S n) m f.
Proof.
  introv; unfold sum_f.
  destruct (le_lt_dec m n) as [d|d]; subst.
  - rewrite Rcomplements.MyNat.minus_0_le; auto.
    simpl.
    rewrite Rplus_0_r; auto.
  - rewrite Nat.sub_succ_r.
    rewrite decomp_sum; try omega; simpl; auto.
    f_equal.
    apply sum_eq.
    introv h.
    f_equal.
    omega.
Qed.

Lemma sum_f_plus :
  forall (An Bn : nat -> R) (n m : nat),
    sum_f n m (fun l : nat => An l + Bn l)
    = sum_f n m An + sum_f n m Bn.
Proof.
  introv.
  unfold sum_f.
  rewrite sum_plus; auto.
Qed.

Lemma sum_f_eq :
  forall (An Bn : nat -> R) (n m : nat),
    (n <= m)%nat
    -> (forall i : nat, (n <= i)%nat -> (i <= m)%nat -> An i = Bn i)
    -> sum_f n m An = sum_f n m Bn.
Proof.
  introv q imp; unfold sum_f.
  apply sum_eq.
  introv h.
  apply imp; try omega.
Qed.

Lemma Derive_n_S :
  forall n f x, Derive_n f (S n) x = Derive_n (Derive f) n x.
Proof.
  induction n; introv; auto.
  simpl.
  rewrite (Derive_ext
             (Derive_n (Derive f) n)
             (Derive_n f (S n))); auto.
Qed.

Lemma Derive_sum_f :
  forall (f : R -> nat -> R) x n m,
    (n <= m)%nat
    -> (forall k, (n <= k)%nat -> (k <= m)%nat -> ex_derive_R (fun r => f r k) x)
    -> Derive (fun r => sum_f n m (f r)) x
       = sum_f n m (fun k => Derive (fun r => f r k) x).
Proof.
  introv q imp.
  unfold sum_f.
  rewrite Derive_sum_f_R0; auto.
  introv h.
  apply imp; auto; try omega.
Qed.

Lemma ex_derive_n_S :
  forall n f x,
    ex_derive_R f x
    -> ex_derive_n f (S n) x <-> ex_derive_n (Derive f) n x.
Proof.
  induction n; introv imp; simpl; split; intro h; auto.

  {
    eapply ex_derive_ext;[|exact h].
    introv; simpl.
    rewrite <- Derive_n_S; simpl; auto.
  }

  {
    eapply ex_derive_ext;[|exact h].
    introv; simpl.
    rewrite <- Derive_n_S; simpl; auto.
  }
Qed.

Lemma ex_derive_n_S_implies :
  forall n f x,
    ex_derive_R f x
    -> ex_derive_n f (S n) x
    -> ex_derive_n (Derive f) n x.
Proof.
  introv h1 h2.
  apply ex_derive_n_S; auto.
Qed.

Lemma ex_derive_n_S_if :
  forall n f x,
    ex_derive_R f x
    -> ex_derive_n (Derive f) n x
    -> ex_derive_n f (S n) x.
Proof.
  introv h1 h2.
  apply ex_derive_n_S; auto.
Qed.

Lemma Derive_constant_fun :
  forall c d pt, (forall x, c x = d) -> Derive c pt = 0.
Proof.
  introv imp.
  rewrite (Derive_ext _ (fun _ => d)); auto.
  apply Derive_const.
Qed.

Lemma is_derive_id_pow :
  forall (n : nat) (x : R),
    is_derive_R (fun x => x^n) x (INR n * x^(pred n)).
Proof.
  introv.
  pose proof (is_derive_pow (fun x => x) n x R1) as h; simpl in h.
  rewrite Rmult_1_r in h.
  autodimp h hyp.
  apply @is_derive_id.
Qed.

Lemma ex_derive_id_pow :
  forall (n : nat) (x : R), ex_derive_R (fun x => x^n) x.
Proof.
  introv.
  exists (INR n * x^(pred n)).
  apply is_derive_id_pow.
Qed.

Lemma Derive_id_pow :
  forall (n : nat) (x : R),
    Derive (fun x => x^n) x = (INR n * x^(pred n)).
Proof.
  introv.
  apply is_derive_unique.
  apply is_derive_id_pow.
Qed.

Lemma ex_derive_n_id_pow :
  forall (n : nat) (m : nat) (x : R), ex_derive_n (fun x => x^m) n x.
Proof.
  induction n; introv;[simpl;auto|].
  apply ex_derive_n_S_if;[apply ex_derive_id_pow|].
  apply (ex_derive_n_ext (fun x => INR m * x^(pred m))).
  { introv; symmetry; apply Derive_id_pow. }
  apply ex_derive_n_scal_l; auto.
Qed.

Lemma Derive_n_id_pow :
  forall n k pt,
    Derive_n (fun x => x^k) n pt
    = if lt_dec k n then 0
      else (INR (fact k) / INR (fact (k - n))) * (pt^(k - n)).
Proof.
  induction n; introv; dest_cases w; simpl; auto.

  {
    rewrite minus0; auto.
    rewrite (Fdiv_def Rfield).
    rewrite Rinv_r;[rewrite Rmult_1_l; auto|].
    apply INR_fact_neq_0.
  }

  {
    rewrite (Derive_ext
               _
               (fun pt =>
                  if lt_dec k n then 0
                  else INR (fact k) / INR (fact (k - n)) * pt ^ (k - n))); auto.
    dest_cases w.

    { rewrite Derive_const; auto. }

    {
      assert (k = n) as xx by omega; subst.
      rewrite Nat.sub_diag; simpl.
      rewrite Rmult_1_r.
      rewrite Rcomplements.Rdiv_1.
      rewrite Derive_const; auto.
    }
  }

  {
    rewrite (Derive_ext
               _
               (fun pt =>
                  if lt_dec k n then 0
                  else INR (fact k) / INR (fact (k - n)) * pt ^ (k - n))); auto.
    dest_cases w; try omega.
    rewrite Derive_scal.
    rewrite Derive_id_pow.
    rewrite Rcomplements.MyNat.sub_succ_r.
    rewrite <- Rmult_assoc.
    f_equal.
    rewrite (S_pred (k - n) 0); try omega.
    rewrite fact_simpl.
    rewrite <- (S_pred (k - n) 0); try omega.
    rewrite mult_INR.
    repeat rewrite (Fdiv_def Rfield).
    rewrite Rinv_mult_distr;
      try (apply INR_fact_neq_0);
      try (apply not_0_INR);
      try omega;[].

    rewrite (Rmult_comm _ (INR (k - n))).
    rewrite <- Rmult_assoc.
    rewrite (Rmult_comm (INR (k - n))).
    rewrite Rmult_assoc.
    rewrite <- (Rmult_assoc (INR (k - n))).
    rewrite Rinv_r;
      try (apply not_0_INR);
      try omega;[].
    rewrite Rmult_1_l.
    auto.
  }
Qed.

Lemma ex_derive_n_id :
  forall (n : nat) (x : R), ex_derive_n (fun x => x) n x.
Proof.
  introv.
  pose proof (ex_derive_n_id_pow n 1 x) as h.
  eapply ex_derive_n_ext; try (exact h).
  introv; simpl; autorewrite with core; auto.
Qed.

(* Another equivalent definition of Derive_n *)
Fixpoint Derive__n (f : R -> R) (n : nat) : R -> R :=
  match n with
  | 0%nat => f
  | S n => Derive (Derive__n f n)
  end.

Lemma Derive__n_eq :
  forall f n x, Derive__n f n x = Derive_n f n x.
Proof.
  induction n; simpl; introv; auto.
  apply (Derive_ext _ _ x) in IHn; auto.
Qed.
