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
Require Export tactics_util.


(** definition of state *)
Definition state := KAssignable -> R.

(** Dummy state *)
Definition DumState : state := fun v => DumR.

(** some properties about states *)

(** change KAssignable (variable or differential of variable)  a with r in state s *)
Definition upd_state (s : state) (a : KAssignable) (r : R) : state :=
  fun x =>
    if KAssignable_dec x a
    then r
    else s x.

(** after variable a in state s is update with value r, it's value in state s is r *)
Lemma upd_state_same :
  forall s a r, upd_state s a r a = r.
Proof.
  intros s a r.
  unfold upd_state.
  destruct (KAssignable_dec a a) as [n|n]; auto.
  destruct n; auto.
Qed.
Hint Rewrite upd_state_same.

(** special case of upd_state is defined for variables *)
Definition upd_state_var S v r :=
  upd_state S (KAssignVar v) r.

(** special case of upd_state_same is defined for variables *)
Lemma upd_state_var_same :
  forall s v r, upd_state_var s v r (KAssignVar v) = r.
Proof.
  intros s v r.
  unfold upd_state_var; autorewrite with core; auto.
Qed.
Hint Rewrite upd_state_var_same.

(** if we consider two different KAssignables a and b in one state,
and we update value of a, then value of b remains the same as before update *)
Lemma upd_state_diff :
  forall s a r b, a <> b -> upd_state s a r b = s b.
Proof.
  intros s a r b d.
  unfold upd_state.
  destruct (KAssignable_dec b a) as [n|n]; subst; auto.
  destruct d; auto.
Qed.

(** special case of upd_state_diff is defined for variables *)
Lemma upd_state_var_diff :
  forall s v r a, KAssignVar v <> a -> upd_state_var s v r a = s a.
Proof.
  intros s v r ac d.
  apply upd_state_diff; auto.
Qed.

Definition var_sub := list (KVariable * R).

(** update list of variables sub in state s *)
Fixpoint upd_list_state (s : state) (sub : var_sub) : state :=
  match sub with
  | [] => s
  | (v,r) :: sub => upd_state (upd_list_state s sub) (KAssignVar v) r
  end.

(** builds a var_sub from a state [s] w.r.t. a support [l] *)
Fixpoint state2var_sub (s : state) (l : list KVariable) : var_sub :=
  match l with
  | [] => []
  | v :: vs => (v, s (KAssignVar v)) :: state2var_sub s vs
  end.

(** updates [s1] with the values of [s2] at [l] *)
Definition upd_state_st (s1 : state) (s2 : state) (l : list KVariable) : state :=
  upd_list_state s1 (state2var_sub s2 l).

Lemma upd_state_st_nil :
  forall s1 s2, upd_state_st s1 s2 [] = s1.
Proof.
  tcsp.
Qed.
Hint Rewrite upd_state_st_nil : core.

(** states s1 and s2 are equal except that for variable x, s2 maps to r *)
Definition differ_state_except (s1 s2 : state) x (r : R) : Prop :=
  (forall y, x <> y -> s1 y = s2 y)
  /\
  s2 x = r.

Lemma differ_state_except_prop1 :
  forall v w x r y,
    differ_state_except v w x r
    -> y <> x
    -> v y = w y.
Proof.
  introv d1 d2.
  destruct d1 as [h1 h2].
  apply h1; auto.
Qed.

Lemma differ_state_except_prop2 :
  forall v w x r,
    differ_state_except v w x r
    -> w x = r.
Proof.
  introv d.
  destruct d as [h1 h2]; auto.
Qed.

(* this definition is used in definition of dynamic semantics of programs *)
(** states s1 and s2 are equal except for variables in vars *)
Definition equal_states_except (s1 s2 : state) (vs : list KAssignable) : Prop :=
  forall x,
    not (List.In x vs)
    -> s1 x = s2 x.

Lemma differ_state_except_implies_equal_states_except :
  forall v w x r,
    differ_state_except v w x r
    -> equal_states_except v w [x].
Proof.
  introv h i; simpl in *.
  destruct h as [h1 h2].
  apply h1; tcsp.
Qed.
