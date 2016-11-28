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


Require Export expressions.
Require Export symbol_lemmas.
Require Export Derive.
Require Export vec_util.


(**

   Some useful definitions we used in order to define interpretation
   of primed terms.

 *)

(*Used in definition of interpretation of primed terms.*)
(**  Returns the list of variables occurring in the term. **)
Fixpoint term_variables (f : Term) : list KVariable :=
  match f with
  | KTdot _ => []
  | KTfuncOf f _ args => vec_flatten (Vector.map term_variables args)
  | KTnumber r   => []
  | KTread   x   => KVar_of_KAssignable x
  | KTneg    l   =>  term_variables l
  | KTplus   l r => term_variables l ++ term_variables r
  | KTminus  l r => term_variables l ++ term_variables r
  | KTtimes  l r => term_variables l ++ term_variables r
  | KTdifferential theta => term_variables theta
  end.

(*used in definition of interpretation of teta prime*)
(** For a given term returns list of variables without duplicates **)
Definition term_variables_nodup (f : Term) : list KVariable :=
  remove_duplicates KVariable_dec (term_variables f).
