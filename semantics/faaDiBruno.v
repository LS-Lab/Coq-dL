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

Require Export list_util.
Require Export composition.


Lemma Rdiv_same :
  forall r, r <> 0 -> r / r = 1.
Proof.
  introv d.
  rewrite (Fdiv_def Rfield).
  rewrite Rinv_r; auto.
Qed.

Lemma Rmult_Rdiv_same :
  forall a r, r <> 0 -> r * (a / r) = a.
Proof.
  introv d.
  rewrite (Fdiv_def Rfield).
  rewrite (Rmult_comm a).
  rewrite <- Rmult_assoc.
  rewrite Rinv_r; auto.
  autorewrite with core; auto.
Qed.


(* genAll(n) generates [0;1;2;...;n] *)
Fixpoint genAll (n : nat) : list nat :=
  match n with
  | 0 => [0%nat]
  | S n => snoc (genAll n) (S n)
  end.

(*
  genAllLists(0) generates

   [ [] ]

  genAllLists(1) generates

   [ [0] [1] ]

  genAllLists(2) generates

   [ [0,0] [0,1] [1,0] [1,1] [2,0] [2,1] ]

  and so on
*)
Fixpoint genAllLists (n : nat) : list (list nat) :=
  match n with
  | 0 => [ [] ]
  | S n =>
    let l := genAll(S n) in
    flat_map (fun x => map (fun k => x :: k) (genAllLists n)) l
  end.

Eval compute in (genAllLists 0).
Eval compute in (genAllLists 1).
Eval compute in (genAllLists 2).

Eval compute in (seq.sumn [3%nat;2%nat;6%nat]).

Fixpoint computeSol (k : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: l => (k * x) + computeSol (S k) l
  end.

(*

  Only keeps those lists in genAllLists(n) such that computeSol returns n

*)
Fixpoint genSols (n : nat) : list (list nat) :=
  let L := genAllLists n in
  seq.pmap
    (fun l =>
       if deq_nat n (computeSol 1 l)
       then Some l
       else None)
    L.

Eval compute in (genSols 0).
Eval compute in (genSols 1).
Eval compute in (genSols 2).

Fixpoint sum_L {T} (L : list T) (f : T -> R) : R :=
  match L with
  | [] => 0
  | l :: K => f l + sum_L K f
  end.

Fixpoint prod_L_i {T} (n : nat) (L : list T) (f : nat -> T -> R) : R :=
  match L with
  | [] => 1
  | l :: K => f n l * prod_L_i (S n) K f
  end.

Fixpoint factL (l : list nat) : nat :=
  match l with
  | [] => 1
  | x :: l => fact x * factL l
  end.

Definition faa_di_bruno (f g : R -> R) (n : nat) (pt : R) : R :=
  sum_L
    (genSols n)
    (fun l =>
       (INR (fact n) / INR (factL l))
       * Derive_n f (seq.sumn l) (g pt)
       * prod_L_i
           1
           l
           (fun k b => pow (Derive_n g k pt / INR (fact k)) b)
    ).

(* Let's check that the formula is true for n=1 *)
Lemma faa_di_bruno_1 :
  forall f g pt,
    ex_derive_R f (g pt)
    -> ex_derive_R g pt
    -> faa_di_bruno f g 1 pt
       = Derive_n (fun x => f (g x)) 1 pt.
Proof.
  introv exf exg; simpl in *.
  unfold faa_di_bruno; simpl; autorewrite with core.
  rewrite (Derive_comp f g); auto.
  rewrite (Rmult_comm (Derive g pt)); auto.
Qed.

(* We now prove that the formula is true for n=1 *)
Lemma faa_di_bruno_2 :
  forall f g pt,
    (forall n pt, ex_derive_n f n (g pt))
    -> (forall n pt, ex_derive_n g n pt)
    -> faa_di_bruno f g 2 pt
       = Derive_n (fun x => f (g x)) 2 pt.
Proof.
  introv exf exg; simpl in *.
  unfold faa_di_bruno; simpl; autorewrite with core.

  (* Some cleaning up *)
  rewrite (Derive_ext (fun x => f x) f); auto.
  rewrite (Derive_ext (fun x => g x) g); auto.
  rewrite (Derive_ext (fun x => Derive (fun x => f x) x) (fun x => Derive f x)); auto.
  rewrite (Derive_ext (fun x => Derive (fun x => g x) x) (fun x => Derive g x)); auto.
  rewrite (Derive_ext (fun x => Derive f x) (Derive f)); auto.
  rewrite (Derive_ext (fun x => Derive g x) (Derive g)); auto.

  symmetry.
  erewrite Derive_ext;
    [|introv; apply (Derive_comp f g); auto;
      try (apply (exf 1%nat));
      try (apply (exg 1%nat))].

  rewrite Derive_mult; auto;
    try (apply (exg 2%nat));
    try (apply (@ex_derive_comp
                  Hierarchy.R_AbsRing
                  Hierarchy.R_NormedModule
                  (Derive f) g pt); auto;
         try (apply (exg 1%nat));
         try (apply (exf 2%nat))).

  rewrite (Rmult_assoc 2 _ _).
  symmetry.
  rewrite (Rmult_comm (Derive f (g pt))); auto.
  rewrite <- Rmult_assoc.
  rewrite Rdiv_same; auto;
    [|apply tech_Rplus; auto; try (apply Rlt_0_1); try (apply Rle_0_1)].
  autorewrite with core.

  rewrite Rmult_Rdiv_same;
    [|apply tech_Rplus; auto; try (apply Rlt_0_1); try (apply Rle_0_1)].

  f_equal.

  rewrite (Derive_comp (Derive f) g); auto;
    try (apply (exf 2%nat));
    try (apply (exg 1%nat)).
  rewrite <- (Rmult_assoc (Derive g pt)).
  apply Rmult_comm.
Qed.

(* This is the general case *)
Lemma faa_di_bruno_valid :
  forall (f g : R -> R) (n : nat) (pt : R),
    (n > 0)%nat
    -> (forall k pt, ex_derive_n f k pt)
    -> (forall k pt, ex_derive_n g k pt)
    -> Derive_n (fun x => f (g x)) n pt
       = faa_di_bruno f g n pt.
Proof.

Qed.
