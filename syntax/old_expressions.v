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

Require Export String.
Require Export Reals.
Require Export Coq.Lists.List.
Export List.ListNotations.
Require Export Reals.

(**

  This file implements ddl syntax for Terms, Formulas, Hybrid programs and ODEs.
  This is version which works with sorts (KSort).
  This implementation has restriction on KeYmaera core, such that functions can have only one argument.

*)

  (** sorts *)
  Inductive KSort :=
  | KUnit : KSort  (* unit type *)
  | KBool : KSort  (* booleans *)
  | KReal : KSort  (* real numbers *)
  | KProg : KSort  (* programs *)
  | KTuple  (left : KSort) (right : KSort) : KSort (* tuples *)
  | KObject (name : String.string) : KSort. (* user defined object (e.g., lane) *)

  (** variable symbol *)
  Inductive KVariable : (*KSort ->*) Type :=
  | variable (name : String.string) : KVariable(* KReal*).

  (** communication channel *)
  Inductive KChannel : (*KSort ->*) Type :=
  | channel (name : String.string) : KChannel (*KReal*).

  (** program symbol *)
  Definition ProgramConstName := String.string.

  (** function symbol *)
  Definition FunctionSymbol := String.string.

  (** function *)
  Inductive KFunction (domain : KSort) (codomain : KSort) : Type :=
  | function (name : FunctionSymbol) : KFunction domain codomain.

  (** differential symbol *)
  Record KDifferentialSymbol : Type :=
    differentialSymbol
      {
        differentialSymbol_variable :> KVariable
      }.

  (** x or x' *)
  Inductive KAssignable : Type :=
  | KAssignVar     (variable : KVariable)                    : KAssignable
  | KAssignDiffSym (differentialSymbol: KDifferentialSymbol) : KAssignable.

  (** Terms --- see Definition 1, Section 2.1 *)
  (*
     [sd] is the sort of the dot terms occurring (if any) in the term
     Here we assume that all dot terms in a term/formula/program are supposed to
     have the same type.  The idea is that the uniform substitution
       f(.) -> . + h(.)
     where h takes a pair is not supposed to be well-formed because all dots
     should have the same sort as the sort of f's domain.
     Therefore, . + h(.) shouldn't be a well-formed term.
   *)
  Inductive Term (sd : KSort) : KSort -> Type :=
  | KTdot                                                         : Term sd sd        (* dot symbol for terms *)
  | KTnothing                                                     : Term sd KUnit        (* unit term *)
  | KTanything                                                    : Term sd KReal        (* all (reals) term *)
  | KTfuncOf      (d s : KSort)
                  (f : KFunction d s)
                  (a : Term sd d)                                 : Term sd s            (* application of function symbol *)
  | KTnumber      (r : R)                                         : Term sd KReal        (* number constant *)
  | KTread        (var : KAssignable)                             : Term sd KReal        (* read variable x or diff. symbol x' *)
  | KTneg         (child : Term sd KReal)                         : Term sd KReal        (* negation       -x *)
  | KTplus        (left : Term sd KReal)(right : Term sd KReal)   : Term sd KReal        (* addition       x+y *)
  | KTminus       (left : Term sd KReal)(right : Term sd KReal)   : Term sd KReal        (* subtraction    x-y *)
  | KTtimes       (left : Term sd KReal)(right : Term sd KReal)   : Term sd KReal        (* multiplication x*y *)
  | KTdivide      (left : Term sd KReal)(right : Term sd KReal)   : Term sd KReal        (* division       x/y *)
  | KTpower       (left : Term sd KReal)(right : Term sd KReal)   : Term sd KReal        (* power          x^y *)
  | KTdifferential(child : Term sd KReal)                         : Term sd KReal        (* differential   x'  *)
  | KTpair        (s r : KSort)
                  (left : Term sd s)
                  (right : Term sd r)                             : Term sd (KTuple s r)  (* pair          (x,y) *)

  (** Formula --- see Definition 2, Section 2.1 *)
  with Formula (sd : KSort) : Type :=
  | KFdot                                                           : Formula sd           (* dot symbol for formulas *)
  | KFtrue                                                           : Formula sd           (* true *)
  | KFfalse                                                          : Formula sd           (* false *)
  | KFequal       (s : KSort) (left : Term sd s) (right : Term sd s) : Formula sd           (* x == y *)
  | KFnotequal    (s : KSort) (left : Term sd s) (right : Term sd s) : Formula sd           (* x != y *)
  | KFgreaterEqual(left : Term sd KReal)(right : Term sd KReal)      : Formula sd           (* x >= y *)
  | KFgreater     (left : Term sd KReal)(right : Term sd KReal)      : Formula sd           (* x > y  *)
  | KFlessEqual   (left : Term sd KReal)(right : Term sd KReal)      : Formula sd           (* x =< y *)
  | KFless        (left : Term sd KReal)(right : Term sd KReal)      : Formula sd           (* x < y  *)
  | KFpredOf      (d : KSort)
                  (f : KFunction d KBool)
                  (a : Term sd d)                                    : Formula sd           (* appliction of predicate symbol *)
    (* predicational or quantifier symbol applied to argument formula child *)
  | KFpredicationalOf(f : KFunction KBool KBool)(a : Formula sd)  : Formula sd
  | KFnot         (child : Formula sd)                            : Formula sd           (* ~p *)
  | KFand         (left : Formula sd)(right : Formula sd)            : Formula sd           (* p /\ q *)
  | KFor          (left : Formula sd)(right : Formula sd)            : Formula sd           (* p \/ q *)
  | KFimply       (left : Formula sd)(right : Formula sd)            : Formula sd           (* p -> q *)
  | KFequiv       (left : Formula sd)(right : Formula sd)            : Formula sd           (* p <-> q *)
    (* quantifiers *)
  | KFforallVars  (vars : list KVariable) (child : Formula sd)    : Formula sd           (* Forall x,y,z. p *)
  | KFexistsVars  (vars : list KVariable) (child : Formula sd)    : Formula sd           (* Exists x,y,z. p *)
    (* modal formulas *)
  | KFbox         (prog : Program sd) (child : Formula sd)           : Formula sd           (* [alpha] p *)
  | KFdiamond     (prog : Program sd) (child : Formula sd)           : Formula sd           (* <alpha> p *)
    (* differential formula (p)' *)
  | KFdifferentialFormula (child : Formula sd)                     : Formula sd           (* (p)' *)

  (** Hybrid program --- see Definition 3, Section 2.1 *)
  with Program (sd : KSort) : Type :=
  | KPconstant     (name : ProgramConstName)                      : Program sd           (* program constant e.g., alpha *)
  | KPassign       (x : KAssignable) (s : KSort) (e : Term sd s)  : Program sd           (* x := e or x' := e *)
  | KPassignAny    (x : KAssignable)                              : Program sd           (* x := * or x' := * *)
  | KPtest         (cond : Formula sd)                            : Program sd           (* ?cond *)
  | KPchoice       (left : Program sd)(right : Program sd)        : Program sd           (* alpha u beta *)
  | KPcompose      (left : Program sd)(right : Program sd)        : Program sd           (* alpha ; beta *)
  | KPparallel     (Cl : list KChannel)(Cr : list KChannel)
                   (left : Program sd)(right : Program sd)        : Program sd           (* alpha Cl_||_Cr beta *)
  | KPloop         (child : Program sd)                           : Program sd           (* alpha* *)
    (* communication *)
  | KPsend         (c : KChannel) (s : KSort) (e : Term sd s)     : Program sd           (* c!e *)
  | KPreceive      (c : KChannel) (vars : list KVariable)         : Program sd           (* c?X *)
  | KPbroadcast    (c : KChannel)
                   (s : KSort)
                   (e : Term sd s)
                   (vars : list KVariable)                        : Program sd     (* B^c(e,X) *)
  (* todo games *)
  | KPodeSystem (ode : DifferentialProgram sd)(constraint : Formula sd) : Program sd

  (** differential programs *)
  with DifferentialProgram (sd : KSort) : Type :=
  | differentialProgramConst (name : String.string)                                : DifferentialProgram sd (* constant *)
  | atomicODE (xp : KDifferentialSymbol) (s : KSort) (e : Term sd s)                  : DifferentialProgram sd (* x' = e *)
  | differentialProduct (left : DifferentialProgram sd) (right : DifferentialProgram sd) : DifferentialProgram sd (* . , . *)
  (* todo: left associative form of differential product (i.e.: (. , .) , .) -> (. , (. , .)) *)
  .

  (** expressions of dL *)
  Inductive Expression (sd : KSort) : KSort -> Type :=
  | term    (s : KSort) : Term sd s  -> Expression sd s     (* terms *)
  | program             : Program sd -> Expression sd KProg (* programs *)
  | formula             : Formula sd -> Expression sd KBool (* formulas *)
  .

