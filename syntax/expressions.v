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
Require Export String.
Require Export Reals.
Require Export Coq.Lists.List.
Export List.ListNotations.
Require Vector.

(**

  This file implements ddl syntax for Terms, Formulas, Hybrid programs and ODEs.
  This file is similar to expressions.v but instead of having
  several expression sorts, here we have only one reals (expression
  sorts seem to only be used to build tuples for n-ary functions
  anyway).
  This implementation works with functions with multiple arguments.

 *)

(*This file is similar to sexpressions.v but instead of having only 1 parameter,
functions can now have a multiple parameters. *)

Inductive KTnum :=
| KTNnat  (n : nat) : KTnum
| KTNreal (r : R)   : KTnum.

(** Terms --- see Definition 1, Section 2.1 *)
Inductive Term : Type :=
| KTdot          (n : nat)             : Term        (* dot symbol for terms *)
| KTfuncOf       (f : FunctionSymbol)
                 (n : nat)
                 (a : Vector.t Term n) : Term        (* application of function symbol *)
| KTnumber       (r : KTnum)           : Term        (* number constant *)
| KTread         (var : KAssignable)   : Term        (* read variable x or diff. symbol x' *)
| KTneg          (child : Term)        : Term        (* negation       -x  *)
| KTplus         (left right : Term)   : Term        (* addition       x+y *)
| KTminus        (left right : Term)   : Term        (* subtraction    x-y *)
| KTtimes        (left right : Term)   : Term        (* multiplication x*y *)
| KTdifferential (child : Term)        : Term        (* differential   x'  *)
.

Coercion KTread : KAssignable >-> Term.

Definition nat2term (n : nat) : Term := KTnumber (KTNnat n).
Coercion nat2term : nat >-> Term.

(* A couple of dummy terms *)
Definition DTD : Term := KTdot 0.
Definition DTN : Term := 0.

(** Atomic ODE *)
Inductive AtomicODE : Type :=
| ODEconst (name : ODEConst) : AtomicODE (* constant *)
| ODEsing (xp : KAssignable) (e : Term) : AtomicODE (* x' = e *)
.

(** ODE *)
Inductive ODE : Type :=
| ODEatomic (child : AtomicODE)  : ODE
| ODEprod (left righ : ODE)      : ODE (* . , . *)
.

Coercion ODEatomic : AtomicODE >-> ODE.

(** Formulas --- see Definition 2, Section 2.1 *)
Inductive Formula : Type :=
| KFdot                             : Formula           (* dot symbol for formulas *)
| KFtrue                            : Formula           (* true   *)
| KFfalse                           : Formula           (* false  *)
| KFequal       (left right : Term) : Formula           (* x == y *)
| KFnotequal    (left right : Term) : Formula           (* x != y *)
| KFgreaterEqual(left right : Term) : Formula           (* x >= y *)
| KFgreater     (left right : Term) : Formula           (* x > y  *)
| KFlessEqual   (left right : Term) : Formula           (* x =< y *)
| KFless        (left right : Term) : Formula           (* x < y  *)
| KFpredOf      (f : PredicateSymbol)
                (n : nat)
                (a : Vector.t Term n)                : Formula          (* appliction of predicate symbol *)
(* predicational or quantifier symbol applied to argument formula child *)
| KFquantifier  (f : QuantifierSymbol) (a : Formula) : Formula
| KFnot         (child : Formula)                    : Formula           (* ~p *)
| KFand         (left right : Formula)               : Formula           (* p /\ q *)
| KFor          (left right : Formula)               : Formula           (* p \/ q *)
| KFimply       (left right : Formula)               : Formula           (* p -> q *)
| KFequiv       (left right : Formula)               : Formula           (* p <-> q *)
(* quantifiers *)
| KFforallVars  (vars : list KVariable) (child : Formula)    : Formula           (* Forall x,y,z. p *)
| KFexistsVars  (vars : list KVariable) (child : Formula)    : Formula           (* Exists x,y,z. p *)
(* modal formulas *)
| KFbox         (prog : Program) (child : Formula)           : Formula           (* [alpha] p *)
| KFdiamond     (prog : Program) (child : Formula)           : Formula           (* <alpha> p *)

(** Hybrid programs --- see Definition 3, Section 2.1 *)
with Program : Type :=
     | KPconstant     (name : ProgramConstName)                : Program           (* program constant e.g., alpha *)
     | KPassign       (x : KAssignable) (e : Term)             : Program           (* x := e or x' := e *)
     | KPassignAny    (x : KAssignable)                        : Program           (* x := * or x' := * *)
     | KPtest         (cond : Formula)                         : Program           (* ?cond *)
     | KPchoice       (left : Program)(right : Program)        : Program           (* alpha u beta *)
     | KPcompose      (left : Program)(right : Program)        : Program           (* alpha ; beta *)
     | KPloop         (child : Program)                        : Program           (* alpha* *)
     | KPodeSystem (ode : ODE) (constraint : Formula) : Program
.

(** In order to prove properties for Box and Diamond we have to combine definitions for Formulas and Programs *)
Scheme Formula_ind_2 := Induction for Formula Sort Prop
                        with Program_ind_2 := Induction for Program Sort Prop.

Combined Scheme Formula_Program_multind from Formula_ind_2, Program_ind_2.

Scheme Formula_rec_2 := Induction for Formula Sort Type
                        with Program_rec_2 := Induction for Program Sort Type.

(** expressions of dL *)
Inductive Expression : Type :=
| term    : Term    -> Expression (* terms    *)
| program : Program -> Expression (* programs *)
| formula : Formula -> Expression (* formulas *)
.
