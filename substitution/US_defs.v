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


Require Export US.


(**

  This file defines substitution of DotTerm, as well as substitution of DotFormula.

*)


(* update interpretation I to be r for dot terms *)
Definition upd_interpretation_dot
           (I : interpretation)
           (r : R) : interpretation :=
  fun s : Symbol =>
    match s with
    | SymbolFunction f n => I (SymbolFunction f n)
    | SymbolDotTerm n => r

    | SymbolPredicate p n => I (SymbolPredicate p n)
    | SymbolQuantifier C => I (SymbolQuantifier C)
    | SymbolDotForm => I SymbolDotForm

    | SymbolODE c => I (SymbolODE c)

    | SymbolProgramConst a => I (SymbolProgramConst a)
    end.

(* update interpretation I to be v(m) for dot(m) *)
Definition upd_interpretation_dots
           (I : interpretation)
           {n : nat}
           (v : Vector.t R n) : interpretation :=
  fun s : Symbol =>
    match s with
    | SymbolFunction f m => I (SymbolFunction f m)
    | SymbolDotTerm m => vec_nth v m (I (SymbolDotTerm m))

    | SymbolPredicate p m => I (SymbolPredicate p m)
    | SymbolQuantifier C => I (SymbolQuantifier C)
    | SymbolDotForm => I SymbolDotForm

    | SymbolODE C => I (SymbolODE C)

    | SymbolProgramConst a => I (SymbolProgramConst a)
    end.

(* update interpretation I to be r at *)
Definition upd_interpretation_dot_form
           (I : interpretation)
           (r : FormulaSem) : interpretation :=
  fun s : Symbol =>
    match s with
    | SymbolFunction f m => I (SymbolFunction f m)
    | SymbolDotTerm m => I (SymbolDotTerm m)

    | SymbolPredicate p m => I (SymbolPredicate p m)
    | SymbolQuantifier C => I (SymbolQuantifier C)
    | SymbolDotForm => r

    | SymbolODE C => I (SymbolODE C)

    | SymbolProgramConst a => I (SymbolProgramConst a)
    end.
