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

(**

  This file contains useful functions and lemmas on vectors.

 *)

Require Export Coq.Lists.List.
Export List.ListNotations.
Require Export Omega.
Require Export tactics_util.
Require Vector.
(*
Require Import mathcomp.ssreflect.ssreflect.
*)

Hint Rewrite minus0 : core.

Lemma vec_fold_left_greater :
  forall {T : Type} {n} (v : Vector.t T n) (F : T -> nat) a b,
    (a <= b)%nat
    -> (a <= Vector.fold_left (fun n u => n + F u) b v)%nat.
Proof.
  induction v; introv lab; simpl in *; auto.
  apply IHv; omega.
Qed.

Ltac eqDepDec :=
  match goal with
  | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
    apply Eqdep_dec.inj_pair2_eq_dec in H;
    try (apply deq_nat)
  end.

Lemma vec_fold_left_greater_F :
  forall {T : Type} t {n} (v : Vector.t T n) (F : T -> nat) m,
    Vector.In t v
    -> (F t <= Vector.fold_left (fun n u => n + F u) m v)%nat.
Proof.
  induction v; simpl; introv i.

  { inversion i. }

  { inversion i as [|? ? ? j]; subst; clear i.

    { apply vec_fold_left_greater; omega. }

    { eqDepDec;subst; apply IHv; auto. }
  }
Qed.


(**

   we need this definition in order to work with functions with multiple arguments
   for a given vector l with n elements and a function f,
   returns a list such that function f is applied to each element of that list

 *)
Fixpoint vec_flat_map
         {A B : Type}
         (f : A -> list B)
         {n : nat}
         (l : Vector.t A n) : list B :=
  match l with
  | Vector.nil _ => []
  | Vector.cons _ x _ t => f x ++ vec_flat_map f t
  end.


(**

  we need this definition in order to work with functions with multiple arguments
  converts vector with n elements into a list

 *)
Fixpoint vec_flatten
         {A : Type}
         {n : nat}
         (l : Vector.t (list A) n) : list A :=
  match l with
  | Vector.nil _ => []
  | Vector.cons _ x _ t => x ++ vec_flatten t
  end.

Lemma in_vec_flatten :
  forall A (a : A) n (v : Vector.t (list A) n),
    In a (vec_flatten v)
    <-> exists l, Vector.In l v /\ In a l.
Proof.
  induction v; simpl.

  { split; intro h; tcsp.
    exrepnd.
    inversion h1. }

  { rewrite in_app_iff.
    rewrite IHv; clear IHv.
    split; intro q; repndors; exrepnd.

    { exists h; dands; auto.
      constructor. }

    { exists l; dands; auto.
      constructor; auto. }

    { inversion q1; subst; tcsp.
      eqDepDec; subst; tcsp; try (apply deq_nat).
      right; exists l; dands; auto. }
  }
Qed.

Lemma in_vec_map :
  forall A B (b : B) (f : A -> B) n (v : Vector.t A n),
    Vector.In b (Vector.map f v)
    <-> exists a, Vector.In a v /\ b = f a.
Proof.
  induction v; introv; simpl; split; intro q; exrepnd; subst.

  { inversion q. }

  { inversion q1. }

  { inversion q; clear q; subst;
      eqDepDec; subst; try (apply deq_nat).

    { exists h; dands; auto.
      constructor. }

    { match goal with
      | [ H1 : ?a <-> ?b, H2 : ?a |- _ ] =>
        apply H1 in H2; rename H2 into q; clear H1
      end.
      exrepnd; subst.
      exists a; dands; auto.
      constructor; auto. }
  }

  { inversion q1; clear q1; subst;
      eqDepDec; subst; try (apply deq_nat).

    { constructor. }

    { constructor.
      apply IHv.
      exists a; auto. }
  }
Qed.

Lemma eq_vec_map :
  forall {A B} (f g : A -> B) {n} (v : Vector.t A n),
    (forall a, Vector.In a v -> f a = g a)
    -> Vector.map f v = Vector.map g v.
Proof.
  introv.
  induction v; simpl; introv ih; auto.
  rewrite ih;[|constructor].
  f_equal.
  apply IHv; introv i.
  apply ih; constructor; auto.
Qed.

Lemma vec_map_map :
  forall {A B C} (f : A -> B) (g : B -> C) {n} (v : Vector.t A n),
    Vector.map g (Vector.map f v) = Vector.map (compose g f) v.
Proof.
  induction v; simpl; auto.
  rewrite IHv; auto.
Qed.

Fixpoint vec_nth {A n} (v : Vector.t A n) (i : nat) (d : A) : A :=
  match v, i with
  | Vector.nil _, _ => d
  | Vector.cons _ a m w, 0 => a
  | Vector.cons _ _ _ w, S k => vec_nth w k d
  end.

Lemma vec_nth_map :
  forall {A B} (f : A -> B) {n} (v : Vector.t A n) m a b,
    m < n
    -> vec_nth (Vector.map f v) m b = f (vec_nth v m a).
Proof.
  induction v; introv q; simpl; try omega.
  destruct m; auto.
  apply IHv; try omega.
Qed.

Lemma vec_nth_default :
  forall {A} {n} (v : Vector.t A n) m a,
    n <= m
    -> vec_nth v m a = a.
Proof.
  induction v; introv q; simpl; try omega; auto.
  destruct m; auto; try omega.
  apply IHv; try omega.
Qed.

Lemma vec_nth_in :
  forall {A} {n} (v : Vector.t A n) m a,
    m < n
    -> Vector.In (vec_nth v m a) v.
Proof.
  induction v; introv q; simpl; try omega.
  destruct m; simpl; auto.
  { constructor. }
  { constructor.
    apply IHv; try omega. }
Qed.

Lemma vec_in_dec :
  forall {A} (deq : Deq A) (a : A) {n} (l : Vector.t A n),
    {Vector.In a l} + {~ Vector.In a l}.
Proof.
  induction n; introv.

  { apply (@Vector.case0
             A
             (fun l =>
                {Vector.In a l} + {~ Vector.In a l})); simpl.
    right; intro xx; inversion xx. }

  apply (Vector.caseS' l); introv; clear l.
  destruct (IHn t) as [d|d].

  { left; constructor; auto. }

  destruct (deq a h) as [e|e]; subst.

  { left; constructor. }

  { right; introv xx; inversion xx; eqDepDec; subst; tcsp. }
Qed.

Lemma vec_change_len :
  forall {T : Type} {n m : nat} (e : n = m) (v : Vector.t T n),
    Vector.t T m.
Proof.
  introv v e; subst; auto.
Defined.

Lemma vec_len_app1 :
  forall {n k}, k <= n -> n - k + S k = S n.
Proof.
  induction n; simpl; introv le; destruct k; try omega.
Qed.

Definition vec_app {T} {n m k}
           (v1 : Vector.t T n)
           (v2 : Vector.t T m)
           (e : n + m = k) : Vector.t T k :=
  vec_change_len e (Vector.append v1 v2).

Lemma vec_to_list_cons :
  forall {T n} x (v : Vector.t T n),
    Vector.to_list (Vector.cons T x n v) = x :: Vector.to_list v.
Proof.
  tcsp.
Qed.
Hint Rewrite @vec_to_list_cons : core.

Lemma length_vector_to_list :
  forall {T} n (v : Vector.t T n),
    length (Vector.to_list v) = n.
Proof.
  induction n; introv; simpl; auto.

  { apply (@Vector.case0 T (fun v => length (Vector.to_list v) = 0)); simpl; auto. }

  apply (Vector.caseS' v); introv; clear v.
  autorewrite with core; simpl; rewrite IHn; auto.
Qed.
Hint Rewrite @length_vector_to_list : core.

Fixpoint vec_last {T n} (v : Vector.t T (S n)) : T :=
  match v with
  | Vector.nil _ => False
  | Vector.cons _ t 0 _ => t
  | Vector.cons _ _ _ v => vec_last v
  end.

Fixpoint vec_iseg {T n} (v : Vector.t T (S n)) : Vector.t T n :=
  match v with
  | Vector.nil _ => False
  | Vector.cons _ t 0 _ => (Vector.nil _)
  | Vector.cons _ t _ v => Vector.cons _ t _ (vec_iseg v)
  end.

Fixpoint vec_mapn {A B} (f : A -> nat -> B) {n} (v : Vector.t A n) : Vector.t B n :=
  match v in (Vector.t _ m) return (Vector.t B m) with
  | Vector.nil _ => Vector.nil B
  | Vector.cons _ a m w => Vector.cons B (f a m) m (vec_mapn f w)
  end.

Lemma vec_nth_map_cases :
  forall {A B} (a : A) (b : B) (f : A -> B) {n} (v : Vector.t A n) m,
    vec_nth (Vector.map f v) m b
    = if le_gt_dec n m
      then b
      else f (vec_nth v m a).
Proof.
  induction n; introv.

  { apply (@Vector.case0
             A
             (fun v =>
                vec_nth (Vector.map f v) m b
                = (if le_gt_dec 0 m then b else f (vec_nth v m a))));
      simpl; clear v; auto. }

  { apply (Vector.caseS' v); introv; clear v.
    dest_cases w; simpl; destruct m; auto; try omega;
      rewrite IHn; dest_cases w; try omega. }
Qed.

Lemma vec_nth_mapn_cases :
  forall {A B} (a : A) (b : B) (f : A -> nat -> B) {n} (v : Vector.t A n) m,
    vec_nth (vec_mapn f v) m b
    = if le_gt_dec n m
      then b
      else f (vec_nth v m a) (n - S m).
Proof.
  induction n; introv.

  { apply (@Vector.case0
             A
             (fun v =>
                vec_nth (vec_mapn f v) m b
                = (if le_gt_dec 0 m then b else f (vec_nth v m a) (0 - S m))));
      simpl; clear v; auto. }

  { apply (Vector.caseS' v); introv; clear v.
    dest_cases w; simpl; destruct m; auto; try omega;
      autorewrite with core; auto;
      rewrite IHn; dest_cases w; try omega. }
Qed.

Lemma in_vec_mapn :
  forall {A B} (a : A) (b : B) (f : A -> nat -> B) n (v : Vector.t A n),
    Vector.In b (vec_mapn f v)
    <-> exists m, m < n /\ b = f (vec_nth v m a) (n - S m).
Proof.
  induction n; introv.

  { apply (@Vector.case0
             A
             (fun v =>
                Vector.In b (vec_mapn f v) <->
                (exists m, m < 0 /\ b = f (vec_nth v m a) (0 - S m))));
      simpl; clear v.
    split; intro h.
    { inversion h. }
    { exrepnd; omega. }
  }

  { apply (Vector.caseS' v); introv; clear v; simpl.
    split; intro q; exrepnd; subst.

    { inversion q; subst; eqDepDec; subst; clear q.

      { exists 0; autorewrite with core; dands; auto; omega. }

      { match goal with | [ H : Vector.In _ _ |- _ ] => rename H into i end.
        apply IHn in i; clear IHn; exrepnd; subst.
        exists (S m); dands; auto; omega. }
    }

    { destruct m; autorewrite with core.

      { constructor. }

      { constructor.
        apply IHn.
        exists m; dands; auto; omega. }
    }
  }
Qed.

Inductive no_repeats_vec {T} : forall {n}, Vector.t T n -> Prop :=
| no_rep_vec_nil : no_repeats_vec (Vector.nil T)
| no_rep_vec_cons :
    forall x n xs,
      ~ Vector.In x xs
      -> no_repeats_vec xs
      -> no_repeats_vec (Vector.cons T x n xs).
Hint Constructors no_repeats_vec.

Fixpoint vec_opt2opt_vec {A n} (v : Vector.t (option A) n) : option (Vector.t A n) :=
  match v with
  | Vector.nil _ => Some (Vector.nil A)
  | Vector.cons _ (Some a) m w =>
    match vec_opt2opt_vec w with
    | Some z => Some (Vector.cons A a m z)
    | None => None
    end
  | Vector.cons _ None _ _ => None
  end.

Lemma vec_opt2opt_vec_map_some_implies_some :
  forall {A} {n : nat}
         (v1 v2 : Vector.t A n)
         (F : A -> option A)
         (m : nat)
         (d : A),
    F d = Some d
    -> vec_opt2opt_vec (Vector.map F v1) = Some v2
    -> match F (vec_nth v1 m d) with
       | Some u => u = vec_nth v2 m d
       | None => False
       end.
Proof.
  induction n; introv e.

  { apply (@Vector.case0
             A
             (fun v1 =>
                vec_opt2opt_vec (Vector.map F v1) = Some v2 ->
                match F (vec_nth v1 m d) with
                | Some u => u = vec_nth v2 m d
                | None => False
                end)); simpl; clear v1.
    intro xx; ginv; simpl.
    rewrite e; auto. }

  { apply (Vector.caseS' v1); introv; clear v1.
    apply (Vector.caseS' v2); introv; clear v2.
    simpl.
    intro hyp.
    remember (F h) as opa; destruct opa; simpl; ginv;[].
    remember (vec_opt2opt_vec (Vector.map F t)) as opv; destruct opv; ginv;[].
    inversion hyp; subst; eqDepDec; subst; clear hyp.
    destruct m.

    { rewrite <- Heqopa; auto. }

    {apply IHn; auto. }
  }
Qed.

Lemma eq_vec_map2 :
  forall {A B : Type} d (f g : A -> B) (n : nat) (v1 v2 : Vector.t A n),
    (forall m, m < n -> f (vec_nth v1 m d) = g (vec_nth v2 m d))
    -> Vector.map f v1 = Vector.map g v2.
Proof.
  induction n; introv.

  { apply (@Vector.case0
             A
             (fun v1 =>
                (forall m : nat, m < 0 -> f (vec_nth v1 m d) = g (vec_nth v2 m d)) ->
                Vector.map f v1 = Vector.map g v2)); simpl; clear v1.
    apply (@Vector.case0
             A
             (fun v2 =>
                (forall m : nat, m < 0 -> f d = g (vec_nth v2 m d)) ->
                Vector.nil B = Vector.map g v2)); simpl; clear v2.
    auto. }

  { apply (Vector.caseS' v1); introv; clear v1.
    apply (Vector.caseS' v2); introv; clear v2.
    intro imp.
    simpl; f_equal.
    { apply (imp 0); try omega. }
    { apply IHn; introv ltmn.
      apply (imp (S m)); try omega. }
  }
Qed.
