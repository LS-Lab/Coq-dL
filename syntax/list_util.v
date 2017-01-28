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


Require Export Coq.Lists.List.
Export List.ListNotations.
Require Export tactics2.
Require Export tactics_util.
Require Export Omega.


Hint Rewrite app_nil_r : core.

(** subset of two lists *)
Definition subset {T} (l1 l2 : list T) :=
  forall v, List.In v l1 -> List.In v l2.

(** nil is subset of any lists *)
Lemma subset_nil_l :
  forall {T} (l : list T), subset [] l.
Proof.
  repeat introv; simpl; tcsp.
Qed.
Hint Resolve subset_nil_l : core.

(** nil is subset of any list *)
Lemma subset_nil_l_iff :
  forall {T} (l : list T), subset [] l <-> True.
Proof.
  introv; split; intro h; auto.
Qed.
Hint Rewrite @subset_nil_l_iff : core.

(** iff some list is subset of list l2,
than head of that list is subset of l2
and the tail of that list is also subset of l2 *)
Lemma subset_cons_l :
  forall {T} v (l1 l2 : list T),
    subset (v :: l1) l2 <-> (List.In v l2 /\ subset l1 l2).
Proof.
  repeat introv; unfold subset; simpl; split; intro h; dands; tcsp.
  introv q; repndors; subst; tcsp.
Qed.
Hint Rewrite @subset_cons_l : core.

(** reflexivity for subsets of lists *)
Lemma subset_refl : forall {T} (l : list T), subset l l.
Proof.
  introv i; auto.
Qed.
Hint Resolve subset_refl : core.

Inductive sublist {A} : list A -> list A -> Prop :=
| sublist_nil : forall l, sublist [] l
| sublist_in  : forall v l1 l2, sublist l1 l2 -> sublist (v :: l1) (v :: l2)
| sublist_out : forall v l1 l2, sublist l1 l2 -> sublist l1 (v :: l2).
Hint Constructors sublist.

Lemma sublist_nil_r :
  forall T (l : list T), sublist l [] <-> l = [].
Proof.
  destruct l; split; intro h; auto; ginv.
  inversion h.
Qed.

Lemma sublist_app_r_weak :
  forall {T} (l l1 l2 : list T),
    sublist l l2
    -> sublist l (l1 ++ l2).
Proof.
  induction l1; simpl; auto.
Qed.

Lemma sublist_cons_l :
  forall T v (l1 l2 : list T),
    sublist (v :: l1) l2
    <-> exists la lb, l2 = la ++ (v :: lb) /\ sublist l1 lb.
Proof.
  induction l2; introv; split; intro h; exrepnd; subst; auto.

  { inversion h. }

  { destruct la; simpl in *; ginv. }

  { inversion h as [|? ? ? ss|? ? ? ss]; subst; clear h.

    { exists (@nil T) l2; dands; auto. }

    { apply IHl2 in ss; clear IHl2; auto; exrepnd; subst.
      exists (a :: la) lb; dands; auto. }
  }

  { destruct la; simpl in *; ginv.

    { apply sublist_in; auto. }

    { apply sublist_out.
      apply IHl2.
      exists la lb; dands; auto. }
  }
Qed.

Lemma sublist_app_l :
  forall T (l l1 l2 : list T),
    sublist (l1 ++ l2) l
    <-> exists la lb, l = la ++ lb /\ sublist l1 la /\ sublist l2 lb.
Proof.
  induction l; split; intro h; exrepnd; subst; simpl in *; tcsp.

  { apply sublist_nil_r in h.
    apply app_eq_nil in h; repnd; subst.
    exists (@nil T) (@nil T); dands; auto. }

  { symmetry in h0.
    apply app_eq_nil in h0; repnd; subst.
    apply sublist_nil_r in h1.
    apply sublist_nil_r in h2.
    subst; simpl; auto. }

  { inversion h as [? e|? ? ? ss|? ? ? ss]; subst.

    { symmetry in e.
      apply app_eq_nil in e; repnd; subst; simpl in *.
      exists (a :: l) (@nil T); autorewrite with core; simpl; dands; auto. }

    { destruct l1; simpl in *; ginv.

      { destruct l2; ginv.
        exists (@nil T) (t :: l); simpl; dands; auto. }

      { apply IHl in ss; exrepnd; subst.
        exists (t :: la) lb; dands; auto. }
    }

    { apply IHl in ss; exrepnd; subst.
      exists (a :: la) lb; dands; auto. }
  }

  { destruct la; simpl in *; ginv.

    { destruct lb; ginv.
      apply sublist_nil_r in h2; subst; simpl; auto. }

    { inversion h2; subst; simpl in *; auto.

      { apply sublist_out.
        apply sublist_app_r_weak; auto. }

      { apply sublist_in.
        apply IHl.
        exists la lb; dands; auto. }

      { apply sublist_out.
        apply IHl.
        exists la lb; dands; auto. }
    }
  }
Qed.

(** [sublist] is reflexive  *)
Lemma sublist_refl : forall {T} (l : list T), sublist l l.
Proof.
  induction l; auto.
Qed.

(** [sublist] is transitive *)
Lemma sublist_trans :
  forall {T} (l1 l2 l3 : list T),
    sublist l1 l2 -> sublist l2 l3 -> sublist l1 l3.
Proof.
  induction l1; introv ss1 ss2; auto.
  rewrite sublist_cons_l in *; exrepnd; subst.
  apply sublist_app_l in ss2; exrepnd.
  apply sublist_cons_l in ss2; exrepnd; subst.
  exists (la0 ++ la1) lb1; dands; auto.

  { rewrite app_assoc; auto. }

  { eapply IHl1; eauto. }
Qed.

Lemma sublist_cons_r :
  forall T v (l1 l2 : list T),
    sublist l1 (v :: l2)
    <->
    (
      l1 = []
      \/
      (exists l, l1 = v :: l /\ sublist l l2)
      \/
      sublist l1 l2
    ).
Proof.
  induction l1; introv; split; intro h; repndors; exrepnd; subst; auto; ginv.

  { inversion h as [|? ? ? ss|? ? ? ss]; subst; clear h; tcsp.
    right; left.
    exists l1; dands; auto. }

  { constructor; auto. }
Qed.

(** disjoint for two lists *)
Definition disjoint {T} (l1 l2 : list T) :=
  forall v, List.In v l1 -> not (List.In v l2).

(** nil is disjoint with any list *)
Lemma disjoint_nil_l :
  forall {T} (l : list T), disjoint [] l.
Proof.
  repeat introv; simpl; tcsp.
Qed.
Hint Resolve disjoint_nil_l : core.
(** nil is disjoint with any list *)
Lemma disjoint_nil_l_iff :
  forall {T} (l : list T), disjoint [] l <-> True.
Proof.
  introv; split; intro h; auto.
Qed.
Hint Rewrite @disjoint_nil_l_iff : core.

(** if l1 is disjoint with l2, then l2 is disjoint with l2 *)
Lemma disjoint_sym_impl :
  forall {T} (l1 l2 : list T),
    disjoint l1 l2 -> disjoint l2 l1.
Proof.
  unfold disjoint; introv ss h1 h2.
  apply_in_hyp p; sp.
Qed.

(** symmetry fro disjoint *)
Lemma disjoint_sym :
  forall {T} (l1 l2 : list T),
    disjoint l1 l2 <-> disjoint l2 l1.
Proof.
  introv; split; introv ss i j;
    apply disjoint_sym_impl in ss; apply ss in i; sp.
Qed.

(** if l2 is disjoint with some list,
then l2 is disjoint with head of that list, as well as with the tail of that list *)
Lemma disjoint_cons_l :
  forall {T} v (l1 l2 : list T),
    disjoint (v :: l1) l2 <-> ((not (List.In v l2)) /\ disjoint l1 l2).
Proof.
  repeat introv; unfold disjoint; simpl; split; introv h1; dands;
    try (apply h1; complete sp); introv h2;
      try (complete (apply h1; sp)).
  repnd; repndors; intro h; repndors; subst; tcsp.
  apply h1 in h2; sp.
Qed.
Hint Rewrite @disjoint_cons_l : core.

Lemma disjoint_cons_r :
  forall (T : Type) (v : T) (l1 l2 : list T),
    disjoint l1 (v :: l2) <-> disjoint l1 l2 /\ ~ In v l1.
Proof.
  introv; split; intro h; repnd; dands; auto.
  { introv i j; apply h in i; simpl in i; tcsp. }
  { intro i; apply h in i; simpl in i; tcsp. }
  { introv i j; simpl in j; repndors; subst; tcsp.
    apply h0 in i; tcsp. }
Qed.

Lemma list_ind_len :
  forall (A : Type) (P : list A -> Prop),
    (forall l, (forall k, (List.length k < List.length l)%nat -> P k) -> P l) ->
    forall l, P l.
Proof.
  introv imp; introv.
  remember (List.length l) as n.
  revert imp l Heqn.
  induction n as [m ind] using comp_ind_type; introv imp e; subst.
  destruct l.

  { apply imp; simpl; tcsp. }

  { apply imp; simpl; introv h.
    apply (ind (List.length k)); simpl; auto. }
Qed.

Fixpoint snoc {X} (l:list X) (v:X) : list X :=
  match l with
  | []     => [v]
  | h :: t => h :: (snoc t v)
  end.

Lemma last_snoc :
  forall {T} (l : list T) v w,
    last (snoc l v) w = v.
Proof.
  induction l; simpl; introv; auto.
  rewrite IHl.
  destruct l; simpl; auto.
Qed.
Hint Rewrite @last_snoc : core.

Lemma removelast_snoc :
  forall {T} (l : list T) v, removelast (snoc l v) = l.
Proof.
  induction l; introv; simpl; auto.
  rewrite IHl.
  destruct l; simpl; auto.
Qed.
Hint Rewrite @removelast_snoc : core.

Lemma snoc_cases :
  forall {T} (l : list T),
    l = [] [[+]] {a : T $ {k : list T $ l = snoc k a}}.
Proof.
  induction l; tcsp.
  repndors; exrepnd; subst; tcsp; right.
  { exists a ([] : list T); simpl; auto. }
  { exists a0 (a :: k); simpl; auto. }
Qed.

Lemma length_snoc :
  forall T (n : T) (l : list T),
    length (snoc l n) = S (length l).
Proof.
  induction l; simpl; sp.
Qed.
Hint Rewrite length_snoc : core.

Lemma list_ind_snoc :
  forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall (a : A) (l : list A), P l -> P (snoc l a)) ->
    forall l : list A, P l.
Proof.
  introv B I; introv.
  assert ({n : nat $ length l = n}) as p by (exists (length l); auto).
  destruct p as [n e].
  revert l e.
  induction n; intros.
  { destruct l; allsimpl; ginv. }
  destruct (snoc_cases l) as [h|h]; exrepnd; subst; auto.
  allrw length_snoc; ginv.
  apply I; auto.
Qed.

Lemma in_snoc :
  forall {T} (a b : T) l,
    In a (snoc l b) <-> (In a l \/ a = b).
Proof.
  induction l; simpl; split; intro h; repndors; tcsp.

  { apply IHl in h; repndors; tcsp. }

  { right; apply IHl; tcsp. }

  { subst; right; apply IHl; tcsp. }
Qed.

Lemma disjoint_snoc_r :
  forall {T} (a : T) l1 l2,
    disjoint l1 (snoc l2 a)
    <-> (disjoint l1 l2 /\ ~ In a l1).
Proof.
  introv; split; intro h; repnd; dands.

  { introv i j; apply h in i; destruct i; apply in_snoc; tcsp. }

  { intro i; apply h in i; destruct i; apply in_snoc; tcsp. }

  { introv i j; apply in_snoc in j; repndors; subst; tcsp.
    apply h0 in i; tcsp. }
Qed.

Lemma app_snoc :
  forall {T} (a : T) l1 l2,
    (l1 ++ snoc l2 a)%list = snoc (l1 ++ l2) a.
Proof.
  induction l1; introv; simpl; auto.
  rewrite IHl1; auto.
Qed.

Lemma sublist_in_implies :
  forall {T} (l1 l2 : list T) v,
    sublist l1 l2 -> In v l1 -> In v l2.
Proof.
  introv sl.
  induction sl; introv i; simpl in *; tcsp.
Qed.

Fixpoint remove_elt {T} (dec : Deq T) z (l : list T) : list T :=
  match l with
  | [] => []
  | x :: xs =>
    if dec z x
    then remove_elt dec z xs
    else x :: remove_elt dec z xs
  end.

(** equality of two lists *)
Definition eqset {T} (l1 l2 : list T) :=
  forall x, List.In x l1 <-> List.In x l2.

(** reflexivity for equality on two lists *)
Lemma eqset_refl :
  forall {T} (l : list T), eqset l l.
Proof.
  introv; introv; sp.
Qed.
Hint Resolve eqset_refl : core.

(** transitivity for equality on two lists *)
Lemma eqset_trans :
  forall {T} (l1 l2 l3 : list T),
    eqset l1 l2
    -> eqset l2 l3
    -> eqset l1 l3.
Proof.
  introv eqs1 eqs2; introv.
  rewrite (eqs1 x).
  rewrite <- (eqs2 x); sp.
Qed.

(** if first two elements in list can change orders *)
Lemma eqset_cons_swap :
  forall {T} a b (l : list T),
    eqset (a :: b :: l) (b :: a :: l).
Proof.
  introv; introv; simpl.
  repeat (rewrite <- or_assoc).
  rewrite (or_comm (a = x) (b = x)); sp.
Qed.

(*used in definition of interpretation of teta prime*)
(** Removes duplicates from list **)
Fixpoint remove_duplicates {T} (dec : Deq T) (l : list T) : list T :=
  match l with
  | [] => []
  | x::xs =>
    if in_dec dec x xs
    then remove_duplicates dec xs
    else x :: remove_duplicates dec xs
  end.

(** remove duplicate from the list *)
Lemma remove_duplicates_eqset :
  forall {T} dec (l : list T), eqset (remove_duplicates dec l) l.
Proof.
  induction l; simpl; auto.
  dest_cases w; auto;
    introv; split; intro j; allsimpl; tcsp.
  { apply IHl in j; sp. }
  { apply IHl; repndors; subst; tcsp. }
  { repndors; tcsp; apply IHl in j; tcsp. }
  { repndors; tcsp; apply IHl in j; tcsp. }
Qed.

Lemma eqset_redundant_left :
  forall {T} (v : T) l1 l2,
    eqset (v :: l1) l2
    -> List.In v l1
    -> eqset l1 l2.
Proof.
  introv eqs i; introv; split; intro h.
  { apply eqs; simpl; tcsp. }
  { apply eqs in h; simpl in h; repndors; substs; tcsp. }
Qed.

Lemma in_remove_elt :
  forall {T} (x v : T) dec l,
    List.In x (remove_elt dec v l)
    <-> (List.In x l /\ x <> v).
Proof.
  induction l; simpl; split; intro h; repndors; tcsp;
    dest_cases w; subst; tcsp;
      simpl in *; repndors; subst; tcsp;
        try (complete (apply IHl in h; tcsp)).
  { apply IHl; tcsp. }
  { repnd; repndors; subst; tcsp.
    right; apply IHl; tcsp. }
Qed.

Lemma eqset_not_redundant_left :
  forall {T} (v : T) l1 l2 dec,
    eqset (v :: l1) l2
    -> ~ List.In v l1
    -> (eqset l1 (remove_elt dec v l2) /\ List.In v l2).
Proof.
  introv eqs i; introv.
  dands.

  { split; intro h.
    { apply in_remove_elt; dands.
      { apply eqs; simpl; tcsp. }
      { intro xx; subst; tcsp. }
    }
    { apply in_remove_elt in h; repnd.
      apply eqs in h0; simpl in h0; repndors; subst; tcsp. }
  }

  { apply eqs; simpl; tcsp. }
Qed.

Lemma remove_elt_if_not_in :
  forall {T} (v : T) l dec,
    ~ List.In v l
    -> remove_elt dec v l = l.
Proof.
  induction l; introv q; simpl in *; tcsp.
  apply not_or in q; repnd.
  dest_cases w; GC.
  rewrite IHl; auto.
Qed.

Lemma not_in_remove_elt :
  forall {T} (v : T) l dec,
    ~ In v (remove_elt dec v l).
Proof.
  induction l; introv; simpl; auto.
  dest_cases w.
Qed.
Hint Resolve not_in_remove_elt : core.

Lemma snoc_cons :
  forall {T} (a b : T) l, snoc (a :: l) b = a :: snoc l b.
Proof.
  auto.
Qed.

Fixpoint list_const {T} (n : nat) (x : T) : list T :=
  match n with
  | 0 => []
  | S n => x :: list_const n x
  end.

Lemma length_list_const :
  forall {T} n (x : T), length (list_const n x) = n.
Proof.
  induction n; introv; simpl; auto.
Qed.
Hint Rewrite @length_list_const : core.

Lemma disjoint_app_r :
  forall {T} (l1 l2 l3 : list T),
    disjoint l1 (l2 ++ l3) <-> (disjoint l1 l2 /\ disjoint l1 l3).
Proof.
  introv; split; intro h; repnd; dands; introv i j.
  { apply h in i; destruct i; apply in_app_iff; auto. }
  { apply h in i; destruct i; apply in_app_iff; auto. }
  { apply in_app_iff in j; repndors.
    { apply h0 in i; sp. }
    { apply h in j; sp. }
  }
Qed.

Lemma sublist_app_r :
  forall (T : Type) (l1 l2 l : list T),
    sublist l (l1 ++ l2)
    <->
    exists la lb, l = (la ++ lb)%list /\ sublist la l1 /\ sublist lb l2.
Proof.
  induction l1; introv; split; intro h; exrepnd; subst; simpl in *; auto.

  { exists ([] : list T) l; simpl; dands; auto. }

  { inversion h2; subst; simpl; auto. }

  { apply sublist_cons_r in h; repndors; subst; simpl in *.

    { exists ([] : list T) ([] : list T); simpl; auto. }

    { exrepnd; subst.
      apply IHl1 in h0; exrepnd; subst.
      exists (a :: la) lb; simpl; dands; auto. }

    { apply IHl1 in h; exrepnd; subst.
      exists la lb; dands; auto. }
  }

  { apply sublist_cons_r in h2; repndors; exrepnd; subst; simpl in *.

    { apply sublist_cons_r; right; right.
      apply IHl1.
      exists ([] : list T) lb; simpl; dands; auto. }

    { constructor.
      apply IHl1.
      exists l lb; dands; auto. }

    { constructor.
      apply IHl1.
      exists la lb; dands; auto. }
  }
Qed.

Lemma disjoint_sublist_app_l_implies :
  forall {T} (l1 l2 l : list T),
    disjoint l l1
    -> sublist (l1 ++ l2) l
    -> l1 = [].
Proof.
  destruct l1; introv disj sl; auto; simpl in *.
  apply sublist_cons_l in sl; exrepnd; subst.
  apply disjoint_cons_r in disj; repnd; simpl in *.
  rewrite in_app_iff in disj; simpl in disj.
  destruct disj; auto.
Qed.

Lemma disjoint_sublist_app_implies :
  forall {T} (la lb l1 l2 : list T),
    disjoint lb l1
    -> sublist (l1 ++ l2) (la ++ lb)
    -> exists l l', l2 = (l ++ l')%list /\ sublist (l1 ++ l) la /\ sublist l' lb.
Proof.
  induction la; introv disj sl; simpl in *.

  { applydup @disjoint_sublist_app_l_implies in sl; subst; simpl in *; auto.
    exists ([] : list T) l2; auto. }

  { apply sublist_cons_r in sl; repndors; exrepnd; subst; ginv.

    { destruct l1; simpl in *; ginv; subst; auto.
      exists ([] : list T) ([] : list T); dands; auto. }

    { destruct l1; simpl in *; subst; ginv.

      { apply sublist_app_r in sl0; exrepnd; subst.
        exists (a :: la0) lb0; auto. }

      { apply disjoint_cons_r in disj; repnd.
        pose proof (IHla lb l1 l2) as q; repeat (autodimp q hyp); exrepnd; subst.
        exists l l'; dands; auto. }
    }

    { pose proof (IHla lb l1 l2) as q; repeat (autodimp q hyp); exrepnd; subst.
      exists l l'; dands; auto. }
  }
Qed.

Lemma disjoint_app_l:
  forall (T : Type) (l1 l2 l : list T),
    disjoint (l1 ++ l2) l <-> (disjoint l1 l /\ disjoint l2 l).
Proof.
  introv.
  rewrite disjoint_sym.
  rewrite disjoint_app_r; split; sp; apply disjoint_sym; auto.
Qed.

Lemma disjoint_sublist_implies_nil :
  forall {T} (l1 l2 : list T),
    sublist l1 l2
    -> disjoint l1 l2
    -> l1 = [].
Proof.
  introv sl disj.
  destruct l1; auto.
  apply sublist_cons_l in sl; exrepnd; subst.
  apply disjoint_cons_l in disj; repnd.
  destruct disj0.
  apply in_app_iff; simpl; auto.
Qed.

Lemma disjoint_eq_app_implies :
  forall {T} (la lb l1 l2 : list T),
    disjoint lb l1
    -> (l1 ++ l2)%list = (la ++ lb)%list
    -> exists l, l2 = (l ++ lb)%list /\ la = (l1 ++ l)%list.
Proof.
  induction la; introv disj sl; simpl in *; subst.

  { destruct l1; simpl in *.

    { exists ([] : list T); auto. }

    { apply disjoint_cons_l in disj; repnd; simpl in *.
      destruct disj0; auto. }
  }

  { destruct l1; simpl in *; subst; ginv.

    { clear disj.
      exists (a :: la); simpl; dands; auto. }

    { inversion sl; subst; clear sl.
      match goal with | [ H : _ = _ |- _ ] => rename H into e end.
      apply disjoint_cons_r in disj; repnd.
      pose proof (IHla lb l1 l2) as q; repeat (autodimp q hyp); exrepnd; subst.
      exists l; dands; auto. }
  }
Qed.

Lemma sublist_cons_app_prop1 :
  forall {T} (v1 v2 : T) l1 l2 la lb,
    ~ In v2 lb
    -> disjoint lb l1
    -> sublist (v1 :: (l1 ++ l2)%list) (v2 :: (la ++ lb)%list)
    ->
    (
      (In v1 lb /\ l1 = [])
      \/
      (In v1 (v2 :: la) /\ sublist (v1 :: l1) (v2 :: la))
    ).
Proof.
  introv ni disj sl.
  apply sublist_cons_r in sl; repndors; ginv; exrepnd; ginv.

  { right; simpl; dands; auto.
    pose proof (disjoint_sublist_app_implies la lb l1 l2) as q.
    repeat (autodimp q hyp); exrepnd; subst.
    constructor.
    apply sublist_app_l in q2; exrepnd; subst; auto.
    apply sublist_app_r.
    exists l1 ([] : list T); autorewrite with core; auto. }

  { apply sublist_app_r in sl; exrepnd.
    destruct la0; simpl in *; subst; ginv.

    { apply sublist_cons_l in sl1; exrepnd; subst.
      apply disjoint_app_l in disj; repnd.
      apply disjoint_cons_l in disj; repnd.
      apply sublist_app_l in sl1; exrepnd; subst.
      apply disjoint_app_l in disj; repnd.
      pose proof (disjoint_sublist_implies_nil l1 la1) as q.
      repeat (autodimp q hyp);[apply disjoint_sym;auto|]; subst.
      left; dands; auto.
      apply in_app_iff; simpl; auto. }

    { inversion sl0; subst; clear sl0.
      match goal with | [ H : _ = _ |- _ ] => rename H into e end.
      apply sublist_cons_l in sl2; exrepnd; subst.
      apply disjoint_eq_app_implies in e; auto;
        [|introv i j; apply disj in j; auto; eapply sublist_in_implies; eauto].
      exrepnd; subst.
      apply sublist_app_l in sl2; exrepnd; subst.
      right; dands; auto.
      { right; apply in_app_iff; simpl; auto. }
      constructor.
      apply sublist_app_r_weak.
      constructor.
      apply sublist_app_r.
      exists l1 ([] : list T); autorewrite with core; dands; auto.
    }
  }
Qed.

Lemma sublist_implies_le_length :
  forall {T} (l1 l2 : list T),
    sublist l1 l2 -> length l1 <= length l2.
Proof.
  induction l1; introv sl; simpl; try omega.
  apply sublist_cons_l in sl; exrepnd; subst.
  apply IHl1 in sl1.
  rewrite app_length; simpl; omega.
Qed.

Lemma implies_sublist_cons_r_weak :
  forall {T} (v : T) l1 l2,
    sublist l1 l2
    -> sublist l1 (v :: l2).
Proof.
  introv sl.
  apply sublist_cons_r.
  destruct l1; auto.
Qed.

Lemma implies_sublist_snoc_r_weak :
  forall {T} (v : T) l1 l2,
    sublist l1 l2
    -> sublist l1 (snoc l2 v).
Proof.
  induction l1; introv sl; auto.
  apply sublist_cons_l in sl; exrepnd; subst.
  apply sublist_cons_l.
  exists la (snoc lb v); simpl; dands; auto.
  rewrite <- app_snoc; simpl; auto.
Qed.

Inductive no_repeats {T} : list T -> Prop :=
| no_rep_nil : no_repeats []
| no_rep_cons :
    forall x xs,
      ~ In x xs
      -> no_repeats xs
      -> no_repeats (x :: xs).
Hint Constructors no_repeats.

Fixpoint norepeatsb {T} (d : Deq T) (l : list T) : bool :=
  match l with
  | [] => true
  | x :: xs =>
    if in_dec d x xs
    then false
    else norepeatsb d xs
  end.

Definition norepeats {T} (d : Deq T) (l : list T) : Prop :=
  norepeatsb d l = true.

Lemma norepeatsb_is_no_repeats :
  forall {T} (d : Deq T) (l : list T),
    norepeats d l <-> no_repeats l.
Proof.
  induction l; unfold norepeats; introv; simpl; split; intro h; auto; dest_cases w; auto.

  { constructor; auto; apply IHl; auto. }

  { inversion h; tcsp. }

  { apply IHl; inversion h; auto. }
Qed.

Lemma norepeatsb_proof_irrelevance :
  forall {T} (d : Deq T) (l : list T) (x y : norepeats d l), x = y.
Proof.
  introv.
  apply Eqdep_dec.UIP_dec.
  apply bool_dec.
Qed.

Lemma subset_trans :
  forall {T} (l1 l2 l3 : list T),
    subset l1 l2
    -> subset l2 l3
    -> subset l1 l3.
Proof.
  introv ss1 ss2 i.
  apply ss1 in i; apply ss2 in i; tcsp.
Qed.

Definition null {T} (l : list T) : Prop :=
  l = [].

Definition nullb {T} (l : list T) : bool :=
  if l then true else false.

Lemma nullb_prop :
  forall {T} (l : list T), nullb l = true <-> null l.
Proof.
  destruct l; unfold null; simpl; split; introv h; tcsp.
Qed.

Lemma null_app :
  forall {T} (l1 l2 : list T),
    null (l1 ++ l2) <-> (null l1 /\ null l2).
Proof.
  introv; unfold null; split; intro h; repnd; subst; auto.
  apply app_eq_nil in h; auto.
Qed.

Lemma implies_subset_app_lr :
  forall (T : Type) (l1 l2 la lb : list T),
    subset l1 la
    -> subset l2 lb
    -> subset (l1 ++ l2) (la ++ lb).
Proof.
  introv ss1 ss2.
  introv i; allrw in_app_iff; repndors;[apply ss1 in i|apply ss2 in i]; auto.
Qed.

Lemma implies_subset_app_r :
  forall (T : Type) (l1 l2 l : list T),
    (subset l l1 \/ subset l l2)
    -> subset l (l1 ++ l2).
Proof.
  introv imp i; apply in_app_iff.
  repndors; apply imp in i; sp.
Qed.

Lemma implies_subset_map_lr :
  forall {A B} (l1 l2 : list A) (f : A -> B),
    subset l1 l2
    -> subset (map f l1) (map f l2).
Proof.
  introv ss i; allrw in_map_iff; exrepnd; subst.
  apply ss in i0; eexists; dands; eauto.
Qed.

Lemma subset_eqset_l :
  forall {T} (l1 l2 l3 : list T),
    subset l1 l2
    -> eqset l1 l3
    -> subset l3 l2.
Proof.
  introv ss eqs i.
  apply eqs in i; apply ss in i; auto.
Qed.

Lemma eqset_sym :
  forall {T} (l1 l2 : list T), eqset l1 l2 -> eqset l2 l1.
Proof.
  introv eqs; introv.
  rewrite (eqs x); sp.
Qed.

Lemma implies_eqset_app_lr :
  forall {T} (l1 l2 l3 l4 : list T),
    eqset l1 l2
    -> eqset l3 l4
    -> eqset (l1 ++ l3) (l2 ++ l4).
Proof.
  introv eqs1 eqs2; introv.
  allrw in_app_iff.
  split; introv i; repndors;
    try (complete (apply eqs1 in i; tcsp));
    try (complete (apply eqs2 in i; tcsp)).
Qed.

Lemma subset_app_l :
  forall {T} (l1 l2 : list T) l,
    subset (l1 ++ l2) l <-> (subset l1 l /\ subset l2 l).
Proof.
  introv; split; intro h; repnd; dands; introv i.
  - apply h; rw in_app_iff; sp.
  - apply h; rw in_app_iff; sp.
  - rw in_app_iff in i; repndors;[apply h0|apply h];auto.
Qed.
