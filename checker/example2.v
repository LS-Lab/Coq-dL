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


Require Export checker.


(* v≥0∧A>0 → [{v'=A∧true}] v≥0 *)

Definition Example2 : Formula :=
  KFimply
    (KFand
       (KFgreaterEqual termv term0)
       (KFgreaterEqual termA term0)
    )
    (KFbox
       (KPodeSystem (ODEsing varv termA) KFtrue)
       (KFgreaterEqual termv term0)
    ).
