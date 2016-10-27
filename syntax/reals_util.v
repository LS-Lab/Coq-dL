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


Require Export Reals.
Require Export tactics2.
Require Export Rcomplements.

(**

  Some useful lemmas about reals which we used in our proofs.

*)


Hint Rewrite Rminus_0_r.
Hint Rewrite Ropp_0.
Hint Rewrite Rabs_R0.
Hint Rewrite Rmult_1_l : core.
Hint Rewrite Rmult_1_r : core.
Hint Rewrite Rmult_0_l : core.
Hint Rewrite Rmult_0_r : core.
Hint Rewrite Rplus_0_l : core.
Hint Rewrite Rplus_0_r : core.
Hint Rewrite Nat.sub_diag : core.
Hint Rewrite minus0 : core.
Hint Rewrite pow_O : core.
Hint Rewrite Nat.mul_1_r : core.
Hint Rewrite Nat.add_0_r : core.
Hint Rewrite Rinv_1 : core.
Hint Rewrite Rplus_opp_l : core.
Hint Rewrite Rminus_0_l : core.
Hint Rewrite pow1 : core.
Hint Rewrite Ropp_involutive : core.
Hint Rewrite Rcomplements.Rdiv_1 : core.



(** Dummy real number *)
Definition DumR : R := 0.


(** for non zero elements, division by zero returns zero *)
Lemma zero_div_is_zero :
  forall (r : R), r <> R0 -> (0 / r)%R = R0.
Proof.
  intros r d.
  rewrite (Fdiv_def Rfield).
  rewrite Rmult_0_l; auto.
Qed.


(** plus and minus are comutative *)
Lemma Rplus_minus_comm :
  forall r1 r2 r3 : R,
    (r1 + r2 - r3)%R = (r2 + (r1 - r3))%R.
Proof.
  intros r1 r2 r3.
  repeat rewrite (Rsub_def (F_R Rfield)).
  rewrite (Radd_comm (F_R Rfield) r1 r2).
  rewrite <- (Radd_assoc (F_R Rfield) r2 r1).
  auto.
Qed.

(** subtraction of two same numbers equals zero *)
Lemma Rminus_same :
  forall r, (r - r)%R = R0.
Proof.
  intros r.
  rewrite (Rsub_def (F_R Rfield) r).
  rewrite (Ropp_def (F_R Rfield)); auto.
Qed.
Hint Rewrite Rminus_same.

(** R1 as posreal *)
Definition R1pos : posreal := mkposreal R1 Rlt_0_1.

(* this definition is used in definition of dynamic semantics of programs *)
(** returns all reals which are greater or equal than zero *)
Record preal : Set :=
  mk_preal
    {
      preal_r :> R;
      preal_cond : (0 <= preal_r)%R
    }.

(* this definition is used in definition of dynamic semantics of programs *)
(** returns all reals which are greater or equal than zero, but less or equal than r  *)
Record preal_upto (r : R) : Set :=
  mk_preal_upto
    {
      preal_upto_preal :> preal;
      preal_upto_cond : (preal_upto_preal <= r)%R
    }.

Lemma preal_upto_are_pos :
  forall r (z : preal_upto r), (0 <= z)%R.
Proof.
  introv.
  destruct z as [x z]; simpl.
  destruct x; simpl in *; auto.
Qed.

Lemma lt_preal_upto_trans :
  forall (r : R)
         (r1 : preal_upto r)
         (r2 : preal_upto r1),
    (preal_upto_preal r1 r2 <= r)%R.
Proof.
  introv.
  destruct r1 as [rr1 cr1].
  destruct r2 as [rr2 cr2].
  simpl in *.
  eapply Rle_trans; eauto.
Qed.

Definition ex_preal_upto_trans
           (r : R)
           (r1 : preal_upto r)
           (r2 : preal_upto r1) : preal_upto r :=
  mk_preal_upto
    r
    (preal_upto_preal r1 r2)
    (lt_preal_upto_trans r r1 r2).

Lemma Rmult_lt_pos :
  forall r1 r2 : R, (0 < r1)%R -> (0 < r2)%R -> (0 < r1 * r2)%R.
Proof.
  introv lt0r1 lt0r2.
  pose proof (Rmult_le_0_lt_compat 0 r1 0 r2) as q.
  autorewrite with core in q; apply q; auto; try apply Rle_refl.
Qed.

Definition posreal_plus (p1 p2 : posreal) : posreal :=
  match p1, p2 with
  | mkposreal r1 c1, mkposreal r2 c2 =>
    mkposreal (r1 + r2) (Rplus_lt_0_compat r1 r2 c1 c2)
  end.

Definition posreal_half (p : posreal) : posreal :=
  mkposreal (p / 2) (Rcomplements.is_pos_div_2 p).

Lemma posreal_eq_two_halves :
  forall p : posreal, pos p = (p / 2) + (p / 2).
Proof.
  introv;apply double_var.
Qed.

Definition posreal_min (p1 p2 : posreal) : posreal :=
  mkposreal (Rmin p1 p2) (Rmin_stable_in_posreal p1 p2).



(** definition of zero for preal type *)
Definition R0preal : preal := mk_preal R0 (Rle_refl 0).
(** definition of one for preal type *)
Definition R1preal : preal := mk_preal R1 Rle_0_1.

(* Used in definition of interpretation of primed terms *)
Fixpoint big_sum {T} (vars : list T) (f : T -> R) : R :=
  match vars with
  | [] => R0
  | h :: t => Rplus (f h) (big_sum t f)
  end.
