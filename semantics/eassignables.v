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


Require Export fcset.



(* ========= About KAssignable ========= *)


(** is KAssignable in list *)
Definition in_KAssignable_dec (a : KAssignable) l :=
  in_dec KAssignable_dec a l.

(** lists of KAssignables are disjoint *)
Definition KAssignables_disj (l1 l2 : list KAssignable) : bool :=
  disj_dec KAssignable_dec l1 l2.

(** list l1 included in list l2 --- non-strict *)
Definition KAssignables_included (l1 l2 : list KAssignable) : bool :=
  included_dec KAssignable_dec l1 l2.

(* substraction (minus) for KAssagnables *)
Definition KAssignables_minus (l1 l2 : list KAssignable) :=
  minus_dec KAssignable_dec l1 l2.

(** intersection of 2 KAssignable lists *)
Definition KAssignables_inter (l1 l2 : list KAssignable) :=
  inter_dec KAssignable_dec l1 l2.


(* ========= About EAssignable ========= *)


(* To be able to remove assignables from eassignables, EA_all should hold
   a list of assignables as such: [EA_all l], corresponding to the collection
   of all variables except l.
 *)
(* EA_all [] represents V U V' *)
Definition EAssignables := @FCset KAssignable.

(** is KAssignable in EAssignables *)
Definition in_eassignables (a : KAssignable) (e : EAssignables) : bool :=
  in_fcset KAssignable_dec a e.

(** EAssignables e1 and e2 are disjoint *)
Definition eassignables_disj (e1 e2 : EAssignables) : bool :=
  fcset_disj KAssignable_dec e1 e2.

(** returns true if one EAssignable is subset of another *)
Definition eassignables_subset (e1 e2 : EAssignables) : bool :=
  fcset_subset KAssignable_dec e1 e2.

Definition EA_assignables (l : list KAssignable) := FCS_finite l.
Definition EA_all (l : list KAssignable) := FCS_infinite l.

(** append for EAssignables *)
Definition EAssignables_app (e1 e2 : EAssignables) : EAssignables :=
  fcset_app KAssignable_dec e1 e2.

(** intersection of EAssignables *)
Definition EAssignables_inter (e1 e2 : EAssignables) : EAssignables :=
  fcset_inter KAssignable_dec e1 e2.

Definition remove_assignables
           (e : EAssignables)
           (vs : list KAssignable) : EAssignables :=
  fcset_remove_list KAssignable_dec e vs.

Definition remove_eassignables (l1 l2 : EAssignables) : EAssignables :=
  fcset_remove KAssignable_dec l1 l2.



(*========= some KAssignables/EAssignables lemmas =========*)


(** a is in subtraction (minus) of two KAssignable lists,
than a is element of first list and it's not in second list *)
Lemma in_KAssignables_minus :
  forall a l1 l2,
    List.In a (KAssignables_minus l1 l2)
    <-> (List.In a l1 /\ ~ List.In a l2).
Proof.
  apply in_minus_dec.
Qed.

(** a is in intersection of two KAssignable lists,
then a is in both lists *)
Lemma in_KAssignables_inter :
  forall a l1 l2,
    List.In a (KAssignables_inter l1 l2)
    <-> (List.In a l1 /\ List.In a l2).
Proof.
  apply in_inter_dec.
Qed.

(**

  if a is not in intersection of two KAssignable lists,
  then a is not element of either of them

 *)
Lemma in_eassignables_app_false_implies :
  forall a e1 e2,
    in_eassignables a (EAssignables_app e1 e2) = false
    ->
    (
      in_eassignables a e1 = false
      /\
      in_eassignables a e2 = false
    ).
Proof.
  apply in_fcset_app_false_implies.
Qed.

(**

  a is in intersectopn of two EAssignables,
  iff a is element of one of them

 *)
Lemma in_eassignables_app_true_iff :
  forall a e1 e2,
    in_eassignables a (EAssignables_app e1 e2) = true
    <->
    (
      in_eassignables a e1 = true
      \/
      in_eassignables a e2 = true
    ).
Proof.
  apply in_fcset_app_true_iff.
Qed.

(** iff v is in EA_assignables l, then v is in list l *)
Lemma in_eassignables_assignables :
  forall v l,
    in_eassignables v (EA_assignables l) = true
    <-> List.In v l.
Proof.
  apply in_fcset_finite.
Qed.

(** if KAssignables form l1 are included in l2 than l1 is subset of l2 *)
Lemma KAssignables_included_prop :
  forall l1 l2,
    KAssignables_included l1 l2 = true
    <-> subset l1 l2.
Proof.
  apply included_dec_prop.
Qed.
Hint Rewrite KAssignables_included_prop : core.

(** returns true if EAssignables are subset of list of KAssignables *)
Definition eassignables_subset_assignables
           (e : EAssignables)
           (l : list KAssignable) : bool :=
  fcset_subset_list KAssignable_dec e l.

(** if EAssignables e is subset of list of KAssignables l,
as well as a is in e, then a is in lilst l *)
Lemma eassignables_subset_assignables_prop :
  forall e l a,
    eassignables_subset_assignables e l = true
    -> in_eassignables a e = true
    -> List.In a l.
Proof.
  apply fset_subset_list_prop.
Qed.

(** if two list of KAssignables l1 and l2 are disjoint, then l1 and l2 are disjoint *)
Lemma KAssignables_disj_prop :
  forall l1 l2,
    KAssignables_disj l1 l2 = true
    <-> disjoint l1 l2.
Proof.
  apply disj_dec_prop.
Qed.
Hint Rewrite KAssignables_disj_prop : core.

(** if EAssignables e1 is subset of EAssignables subset e2,
and a is in e1 then a is in e2 *)
Lemma eassignables_subset_prop :
  forall e1 e2 a,
    eassignables_subset e1 e2 = true
    -> in_eassignables a e1 = true
    -> in_eassignables a e2 = true.
Proof.
  apply fcset_subset_prop.
Qed.

(** conversion form variable to KAssigable *)
Definition KAssignable_x : KAssignable :=
  KAssignVar (variable "x").

(** we need this in order to prove eassignables_subset_iff lemma *)
Fixpoint KAssignable2str (a : KAssignable) : String.string :=
  match a with
  | KAssignVar (variable x) => x
  | KAssignDiff x => KAssignable2str x
  end.

Lemma fresh_kvariable : FreshFun KVariable.
Proof.
  unfold FreshFun.
  introv.

  exists (variable (String.append "x" (append_string_list (map KVariable2string l)))).
  remember ("x") as extra.
  assert (0 < String.length extra)%nat as len by (subst; simpl; auto).
  clear Heqextra.
  revert dependent extra.
  induction l; introv s; allsimpl; tcsp.
  rw string_append_assoc.
  introv k; repndors;[|apply IHl in k;auto;rw string_length_append; omega].

  match goal with
  | [ H : ?a = ?b |- _ ] =>
    assert (KVariable2string a = KVariable2string b) as xx by (rewrite <- H; auto)
  end.
  simpl in xx.
  unfold KAssignable2string in xx.

  assert (String.length a
          = String.length
              (String.append
                 (String.append extra a)
                 (append_string_list (map KVariable2string l)))) as e.
  { rewrite <- xx; auto. }
  allrw string_length_append.
  omega.
Defined.

(** we need this in order to prove eassignables_subset_iff lemma *)
Lemma fresh_string : FreshFun String.string.
Proof.
  unfold FreshFun.
  introv.

  exists (String.append "x" (append_string_list l)).
  remember ("x") as extra.
  assert (0 < String.length extra)%nat as len by (subst; simpl; auto).
  clear Heqextra.
  revert dependent extra.
  induction l; introv s; allsimpl; tcsp.
  rw string_append_assoc.
  introv k; repndors;[|apply IHl in k;auto;rw string_length_append; omega].

  assert (String.length a
          = String.length
              (String.append
                 (String.append extra a)
                 (append_string_list l))) as e by (rw <- k; auto).
  allrw string_length_append.
  omega.
Defined.

(** we need this in order to prove eassignables_subset_iff lemma *)
Lemma fresh_kassignable : FreshFun KAssignable.
Proof.
  unfold FreshFun.
  introv.

  exists (KAssignVar (variable (String.append "x" (append_string_list (map KAssignable2string l))))).
  remember ("x") as extra.
  assert (0 < String.length extra)%nat as len by (subst; simpl; auto).
  clear Heqextra.
  revert dependent extra.
  induction l; introv s; allsimpl; tcsp.
  rw string_append_assoc.
  introv k; repndors;[|apply IHl in k;auto;rw string_length_append; omega].

  match goal with
  | [ H : ?a = ?b |- _ ] =>
    assert (KAssignable2str a = KAssignable2str b) as xx by (rewrite <- H; auto)
  end.
  simpl in xx.
  unfold KAssignable2string in xx.

  assert (String.length a
          = String.length
              (String.append
                 (String.append extra a)
                 (append_string_list (map KAssignable2string l)))) as e.
  { unfold KAssignable2string.
    rewrite <- xx.
    clear xx k s extra IHl l.
    induction a; simpl; auto. }
  allrw string_length_append.
  omega.
Defined.

(** iff a is in EAssignables e1 from which EAssignables e2 are removed,
ihant a is in e1, and it's not in e2 *)
Lemma in_eassignables_remove_eassignables :
  forall a e1 e2,
    in_eassignables a (remove_eassignables e1 e2) = true
    <-> (in_eassignables a e1 = true /\ not (in_eassignables a e2 = true)).
Proof.
  apply in_fcset_remove.
Qed.

(** if list of KAssignables is in nil, then l is nil *)
Lemma KAssignables_included_nil_implies :
  forall l, KAssignables_included l [] = true -> l = [].
Proof.
  apply included_dec_nil_implies.
Qed.

(** if e is subset of append of two EAssignables,
then e is subset of both EAssignables *)
Lemma eassignables_subset_app_l_true_iff :
  forall e1 e2 e,
    eassignables_subset (EAssignables_app e1 e2) e = true
    <-> (eassignables_subset e1 e = true /\ eassignables_subset e2 e = true).
Proof.
  apply fcset_subset_app_l_true_iff.
  apply fresh_kassignable.
Qed.

(** if e is susbset of e1 and e is subset of e2, the e is subset of append of e1 and e2 *)
Lemma implies_eassignables_subset_app_r_true :
  forall e1 e2 e,
    (eassignables_subset e e1 = true \/ eassignables_subset e e2 = true)
    -> eassignables_subset e (EAssignables_app e1 e2) = true.
Proof.
  apply implies_fcset_subset_app_r_true.
  apply fresh_kassignable.
Qed.

(** if a is susbset of v then append of a and b is subset of append of v and b *)
Lemma eassignables_subset_app_right :
  forall a b v,
    eassignables_subset a v = true
    -> eassignables_subset (EAssignables_app a b) (EAssignables_app v b) = true.
Proof.
  apply fcset_subset_app_right.
Qed.

(** if a is in intersection of EAssignables e1 and e2, then a is e1 and a is in e2 *)
Lemma in_eassignables_inter_iff :
  forall a e1 e2,
    in_eassignables a (EAssignables_inter e1 e2) = true
    <-> (in_eassignables a e1 = true /\ in_eassignables a e2 = true).
Proof.
  apply in_fcset_inter_iff.
Qed.

(** if e is subset of EAssignables e1 and e is subset of EAssignables e2,
then e is subset of intersection of e1 and e2 *)
Lemma implies_eassignables_subset_inter_l_true :
  forall e1 e2 e,
    (eassignables_subset e1 e = true \/ eassignables_subset e2 e = true)
    -> eassignables_subset (EAssignables_inter e1 e2) e = true.
Proof.
  apply implies_fcset_subset_inter_l_true.
  apply fresh_kassignable.
Qed.

(** if EAssignables e1 is subset of EAssignables e2,
every a which is in e1, is in e2 *)
Lemma eassignables_subset_iff :
  forall e1 e2,
    eassignables_subset e1 e2 = true
    <-> (forall a, in_eassignables a e1 = true -> in_eassignables a e2 = true).
Proof.
  apply fcset_subset_iff.
  apply fresh_kassignable.
Qed.

(** reflexivity for subsets of EAssignables *)
Lemma eassignables_subset_refl :
  forall e, eassignables_subset e e = true.
Proof.
  apply fcset_subset_refl.
Qed.
Hint Resolve eassignables_subset_refl : core.

(** transitivity of subsets of EAssignables *)
Lemma eassignables_subset_trans :
  forall e1 e2 e3,
    eassignables_subset e1 e2 = true
    -> eassignables_subset e2 e3 = true
    -> eassignables_subset e1 e3 = true.
Proof.
  apply fcset_subset_trans.
Qed.

(** if x is removed from e, and then appended to it,
e is subset of that set  *)
Lemma eassignables_subset_app_remove :
  forall e x,
    eassignables_subset e (EAssignables_app (remove_eassignables e x) x) = true.
Proof.
  apply fcset_subset_app_remove.
Qed.

(** subtraction (minus) of l2 on append of l1 and l3
is same as subtraction of l3 from subtraction of l2 from l1 *)
Lemma KAssignables_minus_app_r :
  forall l1 l2 l3,
    KAssignables_minus l1 (l2 ++ l3)
    = KAssignables_minus (KAssignables_minus l1 l2) l3.
Proof.
  apply minus_dec_app_r.
Qed.

(** swap for subtraction (minus) of three lists *)
Lemma KAssignables_minus_swap :
  forall l1 l2 l3,
    KAssignables_minus (KAssignables_minus l1 l2) l3
    = KAssignables_minus (KAssignables_minus l1 l3) l2.
Proof.
  apply minus_dec_swap.
Qed.

(** if l1 is subset of l3, then subtraction (minus) of list l3
from intersection of lists l1 and l2 returns nil *)
Lemma KAssignables_minus_inter_cancel_ss :
  forall l1 l2 l3,
    subset l1 l3
    -> KAssignables_minus (KAssignables_inter l1 l2) l3 = [].
Proof.
  apply minus_inter_dec_cancel_ss.
Qed.

(** subtraction (minus) of list l1 of KAssignables from intersection of
that list with list l2 returns nil *)
Lemma KAssignables_minus_inter_cancel :
  forall l1 l2,
    KAssignables_minus (KAssignables_inter l1 l2) l1 = [].
Proof.
  apply minus_inter_dec_cancel.
Qed.

(** subtraction (minus) and intersection on list of KAssignables can be swapped *)
Lemma KAssignables_inter_minus_swap :
  forall l1 l2 l3,
    KAssignables_inter (KAssignables_minus l1 l2) l3
    = KAssignables_minus (KAssignables_inter l1 l3) l2.
Proof.
  apply inter_minus_dec_swap.
Qed.

(** intersection of list l of KAssignables with nil, returns nil *)
Lemma KAssignables_inter_nil_r :
  forall l, KAssignables_inter l [] = [].
Proof.
  apply inter_dec_nil_r.
Qed.
Hint Rewrite KAssignables_inter_nil_r : core.

(** symmentry of intersection of two lists of KAssignables *)
Lemma KAssignables_inter_sym :
  forall l1 l2,
    eqset
      (KAssignables_inter l1 l2)
      (KAssignables_inter l2 l1).
Proof.
  apply inter_dec_sym.
Qed.

(** equality for EAssignables *)
Definition eassignables_eq (e1 e2 : EAssignables) : Prop :=
  fcset_eq KAssignable_dec e1 e2.

(** reflexivity for equality of EAssignables *)
Lemma eassignables_eq_refl :
  forall e, eassignables_eq e e.
Proof.
  apply fcset_eq_refl.
Qed.
Hint Resolve eassignables_eq_refl : core.

(** iff EAssinables in FCS_infinite l1 (complement of list l1)
are equal to EAssignables in EA_lll l2 (complement of list l2)
list l1 and l2 are equal*)
Lemma eassignables_eq_FCS_infinite :
  forall l1 l2,
    eassignables_eq (FCS_infinite l1) (FCS_infinite l2)
    <-> eqset l1 l2.
Proof.
  apply fcset_eq_FCS_infinite.
Qed.

(** if list l1 is equal to l3, and l2 is equal to l4
list of KAssignables gained by subtraction (minus) of l2 form l2
is same as list of KAssignables gained by subtraction (minus) of l4 form l3 *)
Lemma implies_eqset_KAssignables_minus :
  forall l1 l2 l3 l4,
    eqset l1 l3
    -> eqset l2 l4
    -> eqset (KAssignables_minus l1 l2) (KAssignables_minus l3 l4).
Proof.
  apply implies_eqset_minus_dec.
Qed.

(** associativity of intersection of KAssignables *)
Lemma KAssignables_inter_assoc :
  forall l1 l2 l3,
    KAssignables_inter (KAssignables_inter l1 l2) l3
    = KAssignables_inter l1 (KAssignables_inter l2 l3).
Proof.
  apply inter_dec_assoc.
Qed.

(** associativity for EAassignables *)
Lemma EAssignables_app_assoc :
  forall e1 e2 e3,
    eassignables_eq
      (EAssignables_app (EAssignables_app e1 e2) e3)
      (EAssignables_app e1 (EAssignables_app e2 e3)).
Proof.
  apply fcset_app_assoc.
Qed.

(** list of KAssignables l minus nil returns list l *)
Lemma KAssignables_minus_nil_r :
  forall l, KAssignables_minus l [] = l.
Proof.
  apply minus_dec_nil_r.
Qed.
Hint Rewrite KAssignables_minus_nil_r : core.

(** nil appended to EAssigbales returns EAssignables *)
Lemma EAssignables_app_EA_assignables_nil_r :
  forall e, EAssignables_app e (EA_assignables []) = e.
Proof.
  apply fcset_app_nil_r.
Qed.
Hint Rewrite EAssignables_app_EA_assignables_nil_r : core.

Lemma EAssignables_app_all_left :
  forall e,
    EAssignables_app (EA_all []) e = EA_all [].
Proof.
  apply fcset_app_all_left.
Qed.
Hint Rewrite EAssignables_app_all_left : core.

Lemma EAssignables_app_all_right :
  forall e,
    EAssignables_app e (EA_all []) = EA_all [].
Proof.
  apply fcset_app_all_right.
Qed.
Hint Rewrite EAssignables_app_all_right : core.

Lemma eassignables_subset_all_implies :
  forall V,
    eassignables_subset (EA_all []) V = true
    -> V = EA_all [].
Proof.
  apply fcset_subset_all_implies.
Qed.

Lemma eassignables_disj_prop :
  forall e1 e2 x,
    eassignables_disj e1 e2 = true
    -> in_eassignables x e1 = true
    -> in_eassignables x e2 = false.
Proof.
  apply fcset_disj_prop.
Qed.

Lemma eassignables_subset_nil_implies :
  forall e,
    eassignables_subset e (EA_assignables []) = true
    -> e = EA_assignables [].
Proof.
  apply fcset_subset_nil_implies.
Qed.

Lemma EAssignables_app_eq_nil_implies :
  forall a b,
    EAssignables_app a b = EA_assignables []
    -> (a = EA_assignables [] /\ b = EA_assignables []).
Proof.
  apply fcset_app_eq_nil_implies.
Qed.

Lemma eassignables_disj_sym :
  forall e1 e2 : EAssignables,
    eassignables_disj e1 e2 = true
    -> eassignables_disj e2 e1 = true.
Proof.
  apply fcset_disj_sym.
Qed.

Lemma eassignables_disj_EAssignables_app_l :
  forall e1 e2 e,
    eassignables_disj (EAssignables_app e1 e2) e = true
    <-> (eassignables_disj e1 e = true /\ eassignables_disj e2 e = true).
Proof.
  apply fcset_disj_app_l.
Qed.
