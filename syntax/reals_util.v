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


Require Export tactics2.
(*Require Export Reals.*)
(*Require Export Rcomplements.*)

Require Export CoRN.reals.fast.CRIR.
Require Export CoRN.reals.Intervals.
Require Export MathClasses.interfaces.canonical_names.


(**

  Some useful lemmas about reals which we used in our proofs.

*)


Hint Rewrite cg_minus_correct     : core.
Hint Rewrite cg_inv_zero          : core. (* Hint Rewrite Rminus_0_r. *)
Hint Rewrite cg_inv_zero          : core. (* Hint Rewrite minus0 : core. *)
Hint Rewrite cg_inv_zero          : core.
Hint Rewrite div_1                : core.
Hint Rewrite cring_mult_zero      : core.
Hint Rewrite mult_one             : core.
Hint Rewrite one_mult             : core.
Hint Rewrite cm_rht_unit_unfolded : core.
Hint Rewrite cm_lft_unit_unfolded : core.

(*Hint Rewrite Ropp_0.
Hint Rewrite Rabs_R0.
Hint Rewrite Rmult_1_l : core.
Hint Rewrite Rmult_1_r : core.
Hint Rewrite Rmult_0_l : core.
Hint Rewrite Rmult_0_r : core.
Hint Rewrite Rplus_0_l : core.
Hint Rewrite Rplus_0_r : core.
Hint Rewrite Nat.sub_diag : core.
Hint Rewrite pow_O : core.
Hint Rewrite Nat.mul_1_r : core.
Hint Rewrite Nat.add_0_r : core.
Hint Rewrite Rinv_1 : core.
Hint Rewrite Rplus_opp_l : core.
Hint Rewrite Rminus_0_l : core.
Hint Rewrite pow1 : core.
Hint Rewrite Ropp_involutive : core.
Hint Rewrite Rcomplements.Rdiv_1 : core.*)

(** Dummy real number *)
Definition DumR : IR := [0].

(** division of zero returns zero *)
Lemma zero_div_is_zero :
  forall (r : IR) x_,
    ([0] [/] r [//] x_) [=] [0].
Proof.
  apply div_prop.
Qed.
Hint Rewrite zero_div_is_zero : core.

Hint Resolve eq_reflexive_unfolded : core.

(** plus and minus are comutative *)
Lemma Rplus_minus_comm :
  forall (r1 r2 r3 : IR),
    r1 [+] r2 [-] r3 [=] r2 [+] (r1 [-] r3).
Proof.
  introv.
  rewrite assoc_2; auto.
  rewrite cag_commutes; eauto.
Qed.

(** subtraction of two same numbers equals zero *)
Lemma Rminus_same :
  forall (r : IR), r [-] r [=] [0].
Proof.
  introv.
  autorewrite with core; auto.
Qed.
Hint Rewrite Rminus_same : core.

Record posreal :=
  mkposreal
    {
      posreal_r :> IR;
      posreal_cond : [0] [<] posreal_r
    }.

Lemma zero_lt_one : ([0] : IR) [<] [1].
Proof.
  apply pos_one.
Qed.

(** R1 as posreal *)
Definition R1pos : posreal := mkposreal [1] zero_lt_one.

(* this definition is used in definition of dynamic semantics of programs *)
(** returns all reals which are greater or equal than zero *)
Record preal :=
  mk_preal
    {
      preal_r :> IR;
      preal_cond : [0] [<=] preal_r
    }.
Hint Resolve preal_cond : core.

(* this definition is used in definition of dynamic semantics of programs *)
(** returns all reals which are greater or equal than zero, but less or equal than r  *)
Record preal_upto (r : IR) :=
  mk_preal_upto
    {
      preal_upto_preal :> preal;
      preal_upto_cond : preal_upto_preal [<=] r
    }.

Lemma preal_upto_are_pos :
  forall r (z : preal_upto r), [0] [<=] z.
Proof.
  introv.
  destruct z as [x z]; simpl.
  destruct x; simpl in *; auto.
Qed.

Lemma lt_preal_upto_trans :
  forall (r : IR)
         (r1 : preal_upto r)
         (r2 : preal_upto r1),
    preal_upto_preal r1 r2 [<=] r.
Proof.
  introv.
  destruct r1 as [rr1 cr1].
  destruct r2 as [rr2 cr2].
  simpl in *.
  eapply leEq_transitive; eauto.
Qed.

Definition ex_preal_upto_trans
           (r : IR)
           (r1 : preal_upto r)
           (r2 : preal_upto r1) : preal_upto r :=
  mk_preal_upto
    r
    (preal_upto_preal r1 r2)
    (lt_preal_upto_trans r r1 r2).

Lemma Rmult_lt_pos :
  forall r1 r2 : IR, [0] [<] r1 -> [0] [<] r2 -> [0] [<] r1 [*] r2.
Proof.
  introv lt0r1 lt0r2.
  apply mult_resp_pos; auto.
Qed.

Lemma Rplus_lt_pos :
  forall r1 r2 : IR, [0] [<] r1 -> [0] [<] r2 -> [0] [<] r1 [+] r2.
Proof.
  introv lt0r1 lt0r2.
  apply plus_resp_pos; auto.
Qed.

Definition posreal_plus (p1 p2 : posreal) : posreal :=
  match p1, p2 with
  | mkposreal r1 c1, mkposreal r2 c2 =>
    mkposreal (r1 [+] r2) (Rplus_lt_pos r1 r2 c1 c2)
  end.

Definition posreal_half (p : posreal) : posreal :=
  mkposreal (p [/]TwoNZ) (pos_div_two IR p (posreal_cond p)).

Instance Zero_instance_IR : Zero IR := [0].
Instance One_instance_IR  : One IR  := [1].
Instance Plus_instance_IR : Plus IR := csg_op.
Instance Mult_instance_IR : Mult IR := cr_mult.

Lemma posreal_eq_two_halves :
  forall (p : posreal), p [=] (p [/]TwoNZ) [+] (p [/]TwoNZ).
Proof.
  introv.

  apply (mult_cancel_rht _ _ _ Two); auto.

  { apply pos_ap_zero; auto.
    apply pos_two. }

  rewrite ring_distl_unfolded.
  autorewrite with core.
  simpl.
  repeat (rewrite ring_dist_unfolded); autorewrite with core; auto.
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

Lemma R_move_sub1 :
  forall (a b c d : R),
    (a - b <= c - d)%R -> (a <= c - (d - b))%R.
Proof.
  introv h.
  apply (Rplus_le_compat_r b) in h.
  repeat rewrite (Rsub_def (F_R Rfield)) in h.
  rewrite <- (Radd_assoc (F_R Rfield)) in h.
  autorewrite with core in *.
  rewrite <- (Radd_assoc (F_R Rfield)) in h.

  rewrite (Rsub_def (F_R Rfield) c (d - b)%R).
  rewrite Ropp_minus_distr'.
  rewrite (Rsub_def (F_R Rfield)).
  rewrite (Radd_comm (F_R Rfield) b); auto.
Qed.
