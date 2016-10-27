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

Require Export String.
Require Export Reals.
Require Export Coq.Lists.List.
Export List.ListNotations.

(**

  In this file symbols for variables, differentials, communication channels, program constants,
  functions, predicates and quantifiers are introduced.

  Note: This file is included in sexpressions.v as well as expressions_margs.v,
  but these definitions are not included in expressions.v.

*)

(** variable symbol *)
Inductive KVariable : Type :=
| variable (name : String.string) : KVariable.

(** communication channel *)
Inductive KChannel : Type :=
| channel (name : String.string) : KChannel.

(** program constant *)
Inductive ProgramConstName : Type :=
| program_constant_name (name : String.string) : ProgramConstName.

(** differential program constant *)
Inductive ODEConst : Type :=
| ode_constant (name : String.string) : ODEConst.

(** function symbol *)
Inductive FunctionSymbol : Type :=
| function_symbol (name : String.string) : FunctionSymbol.

(** predicate symbol *)
Inductive PredicateSymbol : Type :=
| predicate_symbol (name : String.string) : PredicateSymbol.

(** quantifier sybmol *)
Inductive QuantifierSymbol : Type :=
| quantifier_symbol (name : String.string) : QuantifierSymbol.

Definition Var  := KVariable.

(** x or x' *)
Inductive KAssignable : Type :=
| KAssignVar  (variable : KVariable)    : KAssignable
| KAssignDiff (assgn    : KAssignable)  : KAssignable.

Definition Assign := KAssignable.
Definition KD := KAssignDiff.
