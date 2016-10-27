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

Require Export terms_util.

(** Free variables of terms --- see Definition 9, Section 2.3 *)
Fixpoint free_vars_term
         (t : Term) : list KAssignable :=
  match t with
  | KTdot _        => []
(*  | KTanything   => [EA_all]*)
  | KTfuncOf f _ args => vec_flatten (Vector.map free_vars_term args)
  | KTnumber r     => []
  | KTread x       => [x]
  | KTneg    l     => free_vars_term l
  | KTplus   l r
  | KTminus  l r
  | KTtimes  l r
  | KTdivide l r
  | KTpower  l r   => free_vars_term l ++ free_vars_term r
  | KTdifferential theta =>
    free_vars_term theta ++ map KD (free_vars_term theta)
  end.

Definition free_vars_vec_term {n} (v : Vector.t Term n) : list KAssignable :=
  vec_flatten (Vector.map free_vars_term v).
