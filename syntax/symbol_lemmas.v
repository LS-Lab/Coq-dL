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


Require Export symbol.
Require Export list_util.
Require Export tactics_util.
Require Export reals_util.


(**

  In this file conversion between KAssignables, variables and strings is introduced, as well as symbol decidability.
  Also, this file introduces definition of state, and implements some lemmas about states.
  Beside that, this file includes some useful definitions which we used in order to define syntax and semantics of ddl.

*)



(** some useful conversions between KAssignables, variables and strings *)

(* Used in definition of interpretation of primed terms *)
(** extract variable form KAssignable *)
Fixpoint KAssignable2variable (a : KAssignable) : KVariable :=
  match a with
  | KAssignVar x => x
  | KAssignDiff a => KAssignable2variable a
  end.
Coercion KAssignable2variable : KAssignable >-> KVariable.

Coercion KAssignVar : KVariable >-> KAssignable.

(** converts KVariable to string *)
Definition KVariable2string (v : KVariable) : String.string :=
  match v with
  | variable name => name
  end.
Coercion KVariable2string : KVariable >-> String.string.

(** converts KAssignable to string *)
Definition KAssignable2string (a : KAssignable) : String.string := a.

(* Used in definition of interpretation of theta prime *)
(** extracts variables form KAssignable *)
Definition KVar_of_KAssignable (a : KAssignable) : list KVariable :=
  match a with
  | KAssignVar x => [x]
  | KAssignDiff _ => []
  end.



(** Decidability for symbols *)

(* used in definition of interpretation of teta prime *)
(** decidability for variables *)
Lemma KVariable_dec :
  forall a b : KVariable, {a = b} + {a <> b}.
Proof.
  destruct a as [x], b as [y]; prove_dec.
  destruct (string_dec x y); subst; prove_dec.
Defined.

(* decidability for channels *)
Lemma KChannel_dec :
  forall a b : KChannel, {a = b} + {a <> b}.
Proof.
  destruct a as [x], b as [y]; prove_dec.
  destruct (string_dec x y); subst; prove_dec.
Defined.

(** decidability for function symbols *)
Lemma FunctionSymbol_dec : forall (t u : FunctionSymbol), {t = u} + {t <> u}.
Proof.
  destruct t as [n1], u as [n2].
  destruct (string_dec n1 n2); subst; prove_dec.
Defined.

(** decidability for predicate symbols *)
Lemma PredicateSymbol_dec : forall (t u : PredicateSymbol), {t = u} + {t <> u}.
Proof.
  destruct t as [n1], u as [n2].
  destruct (string_dec n1 n2); subst; prove_dec.
Defined.

(** decidability for quantifier symbol *)
Lemma QuantifierSymbol_dec : forall (t u : QuantifierSymbol), {t = u} + {t <> u}.
Proof.
  destruct t as [n1], u as [n2].
  destruct (string_dec n1 n2); subst; prove_dec.
Defined.

(** decidability for constants *)
Lemma ProgramConstName_dec : forall (t u : ProgramConstName), {t = u} + {t <> u}.
Proof.
  destruct t as [n1], u as [n2].
  destruct (string_dec n1 n2); subst; prove_dec.
Defined.

(** decidability for constants *)
Lemma ODEConst_dec : forall (t u : ODEConst), {t = u} + {t <> u}.
Proof.
  destruct t as [n1], u as [n2].
  destruct (string_dec n1 n2); subst; prove_dec.
Defined.

(** decidability for KAssignables *)
Lemma KAssignable_dec : forall (t u : KAssignable), {t = u} + {t <> u}.
Proof.
  induction t as [v1|d1], u as [v2|d2]; prove_dec.
  { destruct (KVariable_dec v1 v2) as [d|d]; subst; prove_dec. }
  { destruct (IHd1 d2) as [d|d]; subst; prove_dec. }
Defined.

(** returns differential of some variable x *)
Definition DVar (x : KVariable) : KAssignable :=
  KAssignDiff (KAssignVar x).


Definition remove_var v l := remove_elt KVariable_dec v l.

Lemma not_in_remove_var :
  forall v l, ~ In v (remove_var v l).
Proof.
  introv; unfold remove_var; eauto with core.
Qed.
Hint Resolve not_in_remove_var : core.
