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


Require Export symbol_lemmas.


(**

  This file defines FCsets and EAssignables, as well
  as some lemmas about conversion of KAssignables to EAssignables,
  and vice versa.  Beside that, lemmas for intersection, union and
  ubstraction (difference) which work with EAssignables are implemented.

*)



(* ========= About Finite/CoFinite Sets ========= *)


Inductive FCset {T} :=
| FCS_finite   (l : list T)
| FCS_infinite (l : list T).

Definition in_fcset {T} (dec : Deq T) (a : T) (e : FCset) : bool :=
  match e with
  | FCS_finite l => if in_dec dec a l then true else false
  | FCS_infinite l => if in_dec dec a l then false else true
  end.

Fixpoint disj_dec {T} (dec : Deq T) (l1 l2 : list T) : bool :=
  match l1 with
  | [] => true
  | a :: l =>
    if in_dec dec a l2 then false
    else disj_dec dec l l2
  end.

Fixpoint included_dec {T} (dec : Deq T) (l1 l2 : list T) : bool :=
  match l1 with
  | [] => true
  | a :: l =>
    if in_dec dec a l2
    then included_dec dec l l2
    else false
  end.

(* substraction (minus) for decidable lists *)
Fixpoint minus_dec {T} (dec : Deq T) (l1 l2 : list T) :=
  match l1 with
  | [] => []
  | h :: t =>
    if in_dec dec h l2 then minus_dec dec t l2
    else h :: minus_dec dec t l2
  end.

(** intersection of 2 decidable lists *)
Fixpoint inter_dec {T} (dec : Deq T) (l1 l2 : list T) :=
  match l1 with
  | [] => []
  | h :: t =>
    if in_dec dec h l2 then h :: inter_dec dec t l2
    else inter_dec dec t l2
  end.

Lemma disj_dec_prop :
  forall {T} dec (l1 l2 : list T),
    disj_dec dec l1 l2 = true
    <-> disjoint l1 l2.
Proof.
  induction l1; simpl; introv; autorewrite with core;
    repeat (dest_cases w); try (rewrite IHl1); split; intro h; tcsp.
Qed.
Hint Rewrite @disj_dec_prop : core.

Lemma included_dec_prop :
  forall {T} dec (l1 l2 : list T),
    included_dec dec l1 l2 = true
    <-> subset l1 l2.
Proof.
  induction l1; simpl; introv; autorewrite with core;
    repeat (dest_cases w); try (rewrite IHl1); split; intro h; tcsp.
Qed.
Hint Rewrite @included_dec_prop : core.

Fixpoint fcset_disj {T} (dec : Deq T) (e1 e2 : FCset) : bool :=
  match e1, e2 with
  | FCS_finite   l1, FCS_finite   l2 => disj_dec dec l1 l2
  | FCS_finite   l1, FCS_infinite l2 => included_dec dec l1 l2
  | FCS_infinite l1, FCS_finite   l2 => included_dec dec l2 l1
  | FCS_infinite l1, FCS_infinite l2 => false
  end.

Definition fcset_subset {T} (dec : Deq T) (e1 e2 : FCset) : bool :=
  match e1, e2 with
  | FCS_finite   l1, FCS_finite   l2 => included_dec dec l1 l2
  | FCS_finite   l1, FCS_infinite l2 => disj_dec dec l1 l2
  | FCS_infinite l1, FCS_finite   l2 => false
  | FCS_infinite l1, FCS_infinite l2 => included_dec dec l2 l1
  end.

(** append 2 fcsets *)
Definition fcset_app {T} (dec : Deq T) (e1 e2 : FCset) : FCset :=
  match e1, e2 with
  | FCS_finite l1, FCS_finite l2 => FCS_finite (l1 ++ l2)
  | FCS_finite l1, FCS_infinite l2 => FCS_infinite (minus_dec dec l2 l1)
  | FCS_infinite l1, FCS_finite l2 => FCS_infinite (minus_dec dec l1 l2)
  | FCS_infinite l1, FCS_infinite l2 => FCS_infinite (inter_dec dec l1 l2)
  end.

(** intersection of 2 fcsets *)
Definition fcset_inter {T} (dec : Deq T) (e1 e2 : FCset) : FCset :=
  match e1, e2 with
  | FCS_finite l1, FCS_finite l2 => FCS_finite (inter_dec dec l1 l2)
  | FCS_finite l1, FCS_infinite l2 => FCS_finite (minus_dec dec l1 l2)
  | FCS_infinite l1, FCS_finite l2 => FCS_finite (minus_dec dec l2 l1)
  | FCS_infinite l1, FCS_infinite l2 => FCS_infinite (l1 ++ l2)
  end.

(** substraction of list from fcset *)
Definition fcset_remove_list
           {T}
           (dec : Deq T)
           (e : FCset)
           (vs : list T) : FCset :=
  match e with
  | FCS_finite l => FCS_finite (minus_dec dec l vs)
  | FCS_infinite l => FCS_infinite (l ++ vs)
  end.

(** substraction of one fcset form other *)
Fixpoint fcset_remove {T} (dec : Deq T) (l1 l2 : FCset) : FCset :=
  match l1, l2 with
  | FCS_finite l1, FCS_finite l2 => FCS_finite (minus_dec dec l1 l2)
  | FCS_infinite l1, FCS_finite l2 => FCS_infinite (l1 ++ l2)
  | FCS_finite l1, FCS_infinite l2 => FCS_finite (inter_dec dec l1 l2)
  | FCS_infinite l1, FCS_infinite l2 => FCS_finite (minus_dec dec l2 l1)
  end.




(*========= some FCset lemmas =========*)



(** a is in subtraction (minus) of two decidable lists,
than a is element of first list and it's not in second list *)
Lemma in_minus_dec :
  forall {T} (dec : Deq T) a l1 l2,
    List.In a (minus_dec dec l1 l2)
    <-> (List.In a l1 /\ ~ List.In a l2).
Proof.
  induction l1; introv; split; intro h; simpl in *;
    repnd; dands; auto;
      repeat (dest_cases w); auto;
        try (complete (simpl in *; repndors; subst; auto;
                       apply IHl1 in h; repnd; auto));
        simpl in *; repndors; subst; auto; tcsp.

  { apply IHl1; dands; auto. }

  { right; apply IHl1; dands; auto. }
Qed.

(** a is in intersection of two decidable lists,
then a is in both lists *)
Lemma in_inter_dec :
  forall {T} (dec : Deq T) a l1 l2,
    List.In a (inter_dec dec l1 l2)
    <-> (List.In a l1 /\ List.In a l2).
Proof.
  induction l1; introv; split; intro h; simpl in *;
    repnd; dands; auto;
      repeat (dest_cases w); auto;
        try (complete (simpl in *; repndors; subst; auto;
                       apply IHl1 in h; repnd; auto));
        tcsp; repndors; subst; simpl; tcsp.

  { right; apply IHl1; dands; auto. }

  { apply IHl1; dands; auto. }
Qed.

(**
  if a is not in intersection of two fcsets,
  then a is not element of either of them
 *)
Lemma in_fcset_app_false_implies :
  forall {T} (dec : Deq T) a e1 e2,
    in_fcset dec a (fcset_app dec e1 e2) = false
    ->
    (
      in_fcset dec a e1 = false
      /\
      in_fcset dec a e2 = false
    ).
Proof.
  destruct e1, e2; simpl; repeat (dest_cases w);
    allrw in_app_iff; introv h; allapply not_or; repnd; tcsp;
      dands; auto;
        try (complete (allrw @in_minus_dec; tcsp));
        try (complete (allrw @in_inter_dec; tcsp)).
Qed.


(**

 a is in intersectopn of two fcsets,
 iff a is element of one of them

 *)
Lemma in_fcset_app_true_iff :
  forall {T} (dec : Deq T) a e1 e2,
    in_fcset dec a (fcset_app dec e1 e2) = true
    <->
    (
      in_fcset dec a e1 = true
      \/
      in_fcset dec a e2 = true
    ).
Proof.
  destruct e1, e2; simpl; repeat (dest_cases w);
    allrw in_app_iff; repndors; split; intro h;
      auto; repndors; ginv;
        try (complete (allrw @in_minus_dec; tcsp));
        try (complete (allrw @in_inter_dec; tcsp)).
Qed.

(** v is in FCS_finite l iff v is in list l *)
Lemma in_fcset_finite :
  forall {T} (dec : Deq T) v l,
    in_fcset dec v (FCS_finite l) = true
    <-> List.In v l.
Proof.
  introv; simpl; dest_cases w; split; tcsp.
Qed.

Definition fcset_subset_list
           {T}
           (dec : Deq T)
           (e : FCset)
           (l : list T) : bool :=
  match e with
  | FCS_finite k => included_dec dec k l
  | FCS_infinite k => false
  end.

Lemma fset_subset_list_prop :
  forall {T} (dec : Deq T) e l a,
    fcset_subset_list dec e l = true
    -> in_fcset dec a e = true
    -> List.In a l.
Proof.
  destruct e; simpl; introv ss i; dest_cases w.
  eapply included_dec_prop; eauto.
Qed.

Lemma fcset_subset_prop :
  forall {T} (dec : Deq T) e1 e2 a,
    fcset_subset dec e1 e2 = true
    -> in_fcset dec a e1 = true
    -> in_fcset dec a e2 = true.
Proof.
  destruct e1, e2; simpl; introv ss i; repeat (dest_cases w); GC;
    autorewrite with core in *;
    try (complete (apply ss in i0; sp)).
Qed.

(** we need this in order to prove eassignables_subset_iff lemma *)
Definition FreshFun (T : Type) :=
  forall (l : list T), {x : T & not (List.In x l)}.

Lemma fcset_subset_iff :
  forall {T} (dec : Deq T) (fresh : FreshFun T) e1 e2,
    fcset_subset dec e1 e2 = true
    <-> (forall a, in_fcset dec a e1 = true -> in_fcset dec a e2 = true).
Proof.
  introv; split; introv h;
    try (introv q; eapply fcset_subset_prop; eauto).
  destruct e1, e2; simpl in *; autorewrite with core in *; tcsp.

  { introv i; pose proof (h v) as q; repeat (dest_cases w); autodimp q hyp; tcsp. }

  { introv i; pose proof (h v) as q; repeat (dest_cases w); autodimp q hyp; tcsp. }

  { pose proof (fresh (List.app l l0)) as q; exrepnd.
    allrw in_app_iff.
    apply not_or in q0; repnd.
    pose proof (h x) as q; clear h.
    repeat (dest_cases w). }

  { introv i.
    pose proof (h v) as q; clear h.
    repeat (dest_cases w).
    autodimp q hyp; tcsp. }
Qed.

(** we need this in order to prove eassignables_subset_iff lemma *)
Fixpoint append_string_list (l : list String.string) : String.string :=
  match l with
    | [] => ""
    | s :: l => String.append s (append_string_list l)
  end.

(** we need this in order to prove eassignables_subset_iff lemma *)
Lemma string_append_assoc :
  forall s1 s2 s3,
    String.append s1 (String.append s2 s3)
    = String.append (String.append s1 s2) s3.
Proof.
  induction s1; introv; allsimpl; auto.
  rw IHs1; auto.
Qed.

(** we need this in order to prove eassignables_subset_iff lemma *)
Lemma string_length_append :
  forall s1 s2,
    String.length (String.append s1 s2)
    = (String.length s1 + String.length s2)%nat.
Proof.
  induction s1; introv; allsimpl; auto.
Qed.

Lemma in_fcset_remove :
  forall {T} (dec : Deq T) a e1 e2,
    in_fcset dec a (fcset_remove dec e1 e2) = true
    <-> (in_fcset dec a e1 = true /\ not (in_fcset dec a e2 = true)).
Proof.
  destruct e1, e2; simpl; repeat (dest_cases w); split;
    intro h; tcsp; repnd; dands; tcsp;
      allrw @in_inter_dec;
      allrw @in_minus_dec;
      allrw in_app_iff;
      tcsp.
Qed.

Lemma included_dec_nil_implies :
  forall {T} (dec : Deq T) l, included_dec dec l [] = true -> l = [].
Proof.
  introv.
  destruct l; simpl; tcsp.
Qed.

Lemma fcset_subset_app_l_true_iff :
  forall {T} (dec : Deq T) (fresh : FreshFun T) e1 e2 e,
    fcset_subset dec (fcset_app dec e1 e2) e = true
    <-> (fcset_subset dec e1 e = true /\ fcset_subset dec e2 e = true).
Proof.
  introv fresh; introv.
  repeat (rewrite @fcset_subset_iff; auto); split; introv h; repnd; dands; introv i.
  { apply h; apply in_fcset_app_true_iff; sp. }
  { apply h; apply in_fcset_app_true_iff; sp. }
  { apply in_fcset_app_true_iff in i; repndors; tcsp. }
Qed.

Lemma implies_fcset_subset_app_r_true :
  forall {T} (dec : Deq T) (fresh : FreshFun T) e1 e2 e,
    (fcset_subset dec e e1 = true \/ fcset_subset dec e e2 = true)
    -> fcset_subset dec e (fcset_app dec e1 e2) = true.
Proof.
  introv fresh; introv.
  repeat (rewrite @fcset_subset_iff; auto); introv h i.
  apply in_fcset_app_true_iff; tcsp.
Qed.

Lemma fcset_subset_app_right :
  forall {T} (dec : Deq T) a b v,
    fcset_subset dec a v = true
    -> fcset_subset dec (fcset_app dec a b) (fcset_app dec v b) = true.
Proof.
  introv ss.
  destruct a, b, v; simpl in *;
    allrw @included_dec_prop;
    allrw @disj_dec_prop; ginv;
      try (complete (introv i; allrw @in_minus_dec; repnd; dands; auto)).

  { introv i; allrw in_app_iff; repndors; tcsp. }

  { introv i j; apply in_minus_dec in j; repnd.
    allrw in_app_iff; repndors; tcsp.
    apply ss in i; sp. }

  { introv i;
      allrw @in_minus_dec;
      allrw @in_inter_dec;
      repnd; dands; auto.
    intro j; apply ss in j; tcsp. }

  { introv i;
      allrw @in_inter_dec;
      repnd; dands; auto. }
Qed.

Lemma in_fcset_inter_iff :
  forall {T} (dec : Deq T) a e1 e2,
    in_fcset dec a (fcset_inter dec e1 e2) = true
    <-> (in_fcset dec a e1 = true /\ in_fcset dec a e2 = true).
Proof.
  destruct e1, e2; simpl; repeat (dest_cases w); auto;
    allrw @in_inter_dec;
    allrw @in_minus_dec;
    allrw in_app_iff;
    repnd; tcsp; split; introv xx; repnd; GC; tcsp.
Qed.

Lemma implies_fcset_subset_inter_l_true :
  forall {T} (dec : Deq T) (fresh : FreshFun T) e1 e2 e,
    (fcset_subset dec e1 e = true \/ fcset_subset dec e2 e = true)
    -> fcset_subset dec (fcset_inter dec e1 e2) e = true.
Proof.
  introv fresh h.
  rewrite fcset_subset_iff; auto.
  repeat (rewrite fcset_subset_iff in h; auto).
  introv i.
  apply in_fcset_inter_iff in i; repnd.
  repndors; apply h; auto.
Qed.

Lemma fcset_subset_refl :
  forall {T} (dec : Deq T) e, fcset_subset dec e e = true.
Proof.
  destruct e; simpl; auto; apply included_dec_prop; apply subset_refl.
Qed.

Lemma fcset_subset_trans :
  forall {T} (dec : Deq T) e1 e2 e3,
    fcset_subset dec e1 e2 = true
    -> fcset_subset dec e2 e3 = true
    -> fcset_subset dec e1 e3 = true.
Proof.
  destruct e1, e2, e3; introv h1 h2; simpl in *; tcsp;
    allrw @included_dec_prop;
    allrw @disj_dec_prop.

  { introv i; apply h1 in i; apply h2 in i; auto. }

  { introv i j; apply h1 in i; apply h2 in i; auto. }

  { introv i j; apply h1 in i; apply h2 in j; auto. }

  { introv i; apply h2 in i; apply h1 in i; auto. }
Qed.

Lemma fcset_subset_app_remove :
  forall {T} (dec : Deq T) e x,
    fcset_subset dec e (fcset_app dec (fcset_remove dec e x) x) = true.
Proof.
  destruct e, x; simpl;
    allrw @included_dec_prop;
    allrw @disj_dec_prop;
    introv i; allrw in_app_iff;
      allrw @in_minus_dec;
      allrw @in_inter_dec;
      allrw in_app_iff;
      tcsp.

  { destruct (in_dec dec v l0) as [d|d]; tcsp. }

  { repnd; destruct (in_dec dec v l) as [d|d]; tcsp.
    destruct i; sp. }
Qed.

Lemma minus_dec_app_r :
  forall {T} (dec : Deq T) l1 l2 l3,
    minus_dec dec l1 (l2 ++ l3)
    = minus_dec dec (minus_dec dec l1 l2) l3.
Proof.
  induction l1; introv; simpl; auto.
  repeat (repeat (dest_cases w); allrw in_app_iff; simpl);
    try (rewrite IHl1); auto;
      destruct n; tcsp.
Qed.

Lemma minus_dec_swap :
  forall {T} (dec : Deq T) l1 l2 l3,
    minus_dec dec (minus_dec dec l1 l2) l3
    = minus_dec dec (minus_dec dec l1 l3) l2.
Proof.
  induction l1; introv; simpl; auto.
  repeat (repeat (dest_cases w); allrw in_app_iff; simpl);
    try (rewrite IHl1); auto;
      destruct n; tcsp.
Qed.

Lemma minus_inter_dec_cancel_ss :
  forall {T} (dec : Deq T) l1 l2 l3,
    subset l1 l3
    -> minus_dec dec (inter_dec dec l1 l2) l3 = [].
Proof.
  induction l1; introv ss; simpl; auto.
  allrw @subset_cons_l; repnd.
  repeat (dest_cases w; simpl); simpl.
Qed.

Lemma minus_inter_dec_cancel :
  forall {T} (dec : Deq T) l1 l2,
    minus_dec dec (inter_dec dec l1 l2) l1 = [].
Proof.
  introv; apply minus_inter_dec_cancel_ss; auto.
Qed.

Lemma inter_minus_dec_swap :
  forall {T} (dec : Deq T) l1 l2 l3,
    inter_dec dec (minus_dec dec l1 l2) l3
    = minus_dec dec (inter_dec dec l1 l3) l2.
Proof.
  induction l1; introv; simpl; auto;
  repeat (repeat (dest_cases w); allrw in_app_iff; simpl);
  try (rewrite IHl1;clear IHl1); auto;
    rewrite minus_inter_dec_cancel; auto.
Qed.

Lemma inter_dec_nil_r :
  forall {T} (dec : Deq T) l, inter_dec dec l [] = [].
Proof.
  induction l; simpl; auto.
Qed.
Hint Rewrite @inter_dec_nil_r : core.

Lemma inter_dec_sym :
  forall {T} (dec : Deq T) l1 l2,
    eqset
      (inter_dec dec l1 l2)
      (inter_dec dec l2 l1).
Proof.
  introv; introv.
  repeat (rewrite @in_inter_dec).
  rewrite and_comm; sp.
Qed.

(** equality for FCsets *)
Definition fcset_eq {T} (dec : Deq T) (e1 e2 : FCset) : Prop :=
  (forall a, in_fcset dec a e1 = true <-> in_fcset dec a e2 = true).

Lemma fcset_eq_refl :
  forall {T} (dec : Deq T) e, fcset_eq dec e e.
Proof.
  introv; introv; sp.
Qed.
Hint Resolve fcset_eq_refl : core.

Lemma fcset_eq_FCS_infinite :
  forall {T} (dec : Deq T) l1 l2,
    fcset_eq dec (FCS_infinite l1) (FCS_infinite l2)
    <-> eqset l1 l2.
Proof.
  introv.
  unfold fcset_eq; simpl; split; intro h.
  - introv.
    pose proof (h x) as q; clear h; repeat (dest_cases w); split; intro h; tcsp.
    + destruct q as [q1 q2].
      autodimp q2 hyp; tcsp.
    + destruct q as [q1 q2].
      autodimp q2 hyp; tcsp.
  - introv.
    pose proof (h a) as q; clear h.
    repeat (dest_cases w); split; intro h; ginv.
    + apply q in i; tcsp.
    + apply q in i; tcsp.
Qed.

Lemma implies_eqset_minus_dec :
  forall {T} (dec : Deq T) l1 l2 l3 l4,
    eqset l1 l3
    -> eqset l2 l4
    -> eqset (minus_dec dec l1 l2) (minus_dec dec l3 l4).
Proof.
  introv eqs1 eqs2; introv.
  allrw @in_minus_dec.
  rewrite (eqs1 x).
  rewrite (eqs2 x); tcsp.
Qed.

Lemma inter_dec_assoc :
  forall {T} (dec : Deq T) l1 l2 l3,
    inter_dec dec (inter_dec dec l1 l2) l3
    = inter_dec dec l1 (inter_dec dec l2 l3).
Proof.
  induction l1; introv; simpl; auto.
  repeat (repeat (dest_cases w); allrw in_app_iff; simpl);
    try (rewrite IHl1); auto;
      allrw @in_inter_dec; repnd; tcsp.
  destruct n; tcsp.
Qed.

Lemma fcset_app_assoc :
  forall {T} (dec : Deq T) e1 e2 e3,
    fcset_eq
      dec
      (fcset_app dec (fcset_app dec e1 e2) e3)
      (fcset_app dec e1 (fcset_app dec e2 e3)).
Proof.
  destruct e1, e2, e3; simpl; auto.

  { rewrite app_assoc; eauto with core. }

  { rewrite minus_dec_app_r.
    rewrite minus_dec_swap; eauto with core. }

  { rewrite minus_dec_swap; eauto with core. }

  { rewrite inter_minus_dec_swap; eauto with core. }

  { rewrite minus_dec_app_r.
    rewrite minus_dec_swap; eauto with core. }

  { rewrite fcset_eq_FCS_infinite.
    eapply eqset_trans;[|apply inter_dec_sym].
    repeat (rewrite inter_minus_dec_swap).
    apply implies_eqset_minus_dec; eauto 3 with core.
    apply inter_dec_sym. }

  { rewrite fcset_eq_FCS_infinite.
    eapply eqset_trans;[|apply inter_dec_sym].
    repeat (rewrite inter_minus_dec_swap).
    apply implies_eqset_minus_dec; eauto 3 with core.
    apply inter_dec_sym. }

  { rewrite fcset_eq_FCS_infinite.
    rewrite inter_dec_assoc; auto. }
Qed.

Lemma minus_dec_nil_r :
  forall {T} (dec : Deq T) l, minus_dec dec l [] = l.
Proof.
  induction l; simpl; congruence.
Qed.
Hint Rewrite @minus_dec_nil_r : core.

Lemma fcset_app_nil_r :
  forall {T} (dec : Deq T) e, fcset_app dec e (FCS_finite []) = e.
Proof.
  destruct e; simpl; autorewrite with core; auto.
Qed.
Hint Rewrite @fcset_app_nil_r : core.

Lemma fcset_app_all_left :
  forall {T} (dec : Deq T) e,
    fcset_app dec (FCS_infinite []) e = FCS_infinite [].
Proof.
  destruct e; simpl; auto.
Qed.
Hint Rewrite @fcset_app_all_left : core.

Lemma fcset_app_all_right :
  forall {T} (dec : Deq T) e,
    fcset_app dec e (FCS_infinite []) = FCS_infinite [].
Proof.
  destruct e; simpl; auto.
  rewrite inter_dec_nil_r; auto.
Qed.
Hint Rewrite @fcset_app_all_right : core.

Lemma fcset_subset_all_implies :
  forall {T} (dec : Deq T) V,
    fcset_subset dec (FCS_infinite []) V = true
    -> V = FCS_infinite [].
Proof.
  destruct V; introv ss; simpl in *; ginv.
  apply included_dec_nil_implies in ss; subst; auto.
Qed.

Lemma fcset_disj_prop :
  forall {T} (dec : Deq T) e1 e2 x,
    fcset_disj dec e1 e2 = true
    -> in_fcset dec x e1 = true
    -> in_fcset dec x e2 = false.
Proof.
  destruct e1, e2;
    simpl; introv d i; repeat (dest_cases w); GC;
    allrw @disj_dec_prop;
    allrw @included_dec_prop;
    try (complete (apply d in i0; tcsp)).
Qed.

Lemma fcset_subset_nil_implies :
  forall {T} (dec : Deq T) e,
    fcset_subset dec e (FCS_finite []) = true
    -> e = FCS_finite [].
Proof.
  introv h.
  destruct e; simpl in *; ginv.
  apply included_dec_nil_implies in h; subst; auto.
Qed.

Lemma fcset_app_eq_nil_implies :
  forall {T} (dec : Deq T) a b,
    fcset_app dec a b = FCS_finite []
    -> (a = FCS_finite [] /\ b = FCS_finite []).
Proof.
  introv.
  destruct a, b; simpl; introv i; ginv.
  induction l; simpl in *; ginv.
Qed.

Lemma fcset_disj_sym :
  forall {T} (dec : Deq T) (e1 e2 : FCset),
    fcset_disj dec e1 e2 = true
    -> fcset_disj dec e2 e1 = true.
Proof.
  destruct e1, e2;
    unfold fcset_disj;
    simpl;
    allrw @disj_dec_prop;
    allrw @included_dec_prop;
    introv i; tcsp.
  apply disjoint_sym; auto.
Qed.

Lemma fcset_disj_app_l :
  forall {T} (dec : Deq T) e1 e2 e,
    fcset_disj dec (fcset_app dec e1 e2) e = true
    <-> (fcset_disj dec e1 e = true /\ fcset_disj dec e2 e = true).
Proof.
  destruct e1, e2, e;
    simpl;
    repeat (rewrite @disj_dec_prop);
    repeat (rewrite @included_dec_prop);
    repeat (rewrite disjoint_app_l);
    repeat (rewrite subset_app_l); tcsp;
      split; intro h; repnd; dands; tcsp;
        try (complete (introv i j; apply h in j; apply in_minus_dec in j; sp));
        try (complete (introv i; apply h in i; apply in_minus_dec in i; sp));
        try (complete (introv i; apply h in i; apply in_inter_dec in i; sp));
        try (complete (introv i; apply in_minus_dec; dands; auto; intro j; apply h in j; auto));
        try (complete (introv i; apply in_minus_dec; dands; auto; intro j; apply h0 in j; auto));
        try (complete (introv i; apply in_inter_dec; applydup h in i; apply h0 in i; sp)).
Qed.
