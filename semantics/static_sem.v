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
Require Export semantics_util.
Require Export fcset.
Require Export eassignables.
Require Export free_vars_term.


(**

  This file implements static semantics of ddl.
  In this file definitions of FV, BV and MBV are implemented.
  This file implements definition of signature.

*)


(* ========= Not generalized yet ========= *)


(** conversion of KAssignable to EAssignables *)
Definition assign2ext (v : KAssignable) : EAssignables :=
  FCS_finite [v].

(** conversion of KVariable list to EAssignables *)
Definition vars2ext (l : list KVariable) : EAssignables :=
  FCS_finite (map KAssignVar l).

(** for a differential symbols x', VandD returns {x;x'} *)
Definition VandD (ds : Assign) : EAssignables :=
  FCS_finite [KD ds; ds].


(* based on Rose's implementation *)
Definition bound_vars_atomic_ode (ode : AtomicODE) : EAssignables :=
  match ode with
  | ODEconst name => FCS_infinite []
  | ODEsing ds t => VandD ds
  end.

Fixpoint bound_vars_ode (ode : ODE) : EAssignables :=
  match ode with
(*  | ODEem => FCS_finite []*)
  | ODEatomic c => bound_vars_atomic_ode c
  | ODEprod l r => EAssignables_app (bound_vars_ode l) (bound_vars_ode r)
  end.

(** Bound variables of formula --- see Definition 7, Section 2.3 *)
Fixpoint bound_vars_formula
         (fi : Formula) : EAssignables :=
  match fi with
    | KFdot
    | KFtrue
    | KFfalse            => FCS_finite []

    | KFgreaterEqual l r
    | KFgreater      l r
    | KFlessEqual    l r
    | KFless         l r
    | KFequal        l r
    | KFnotequal     l r => FCS_finite []

    | KFpredOf     f _ a => FCS_finite []

    | KFquantifier   f a => FCS_infinite []

    | KFnot          l   => bound_vars_formula l

    | KFand          l r
    | KFor           l r
    | KFimply        l r
    | KFequiv        l r => EAssignables_app (bound_vars_formula l) (bound_vars_formula r)

    | KFexistsVars   x F
    | KFforallVars   x F => EAssignables_app (vars2ext x) (bound_vars_formula F)

    | KFdiamond alpha  F
    | KFbox     alpha  F => EAssignables_app (bound_vars_program alpha) (bound_vars_formula F)
end

(** Bound variables of hybrid programs --- see Definition 7, Section 2.3 *)
with bound_vars_program
       (p : Program) : EAssignables :=
       match p with
       | KPconstant a => FCS_infinite []
       | KPassign a theta => FCS_finite [a]
       | KPassignAny a => FCS_finite [a]
       | KPtest fi => FCS_finite []
       | KPchoice  a b => EAssignables_app (bound_vars_program a) (bound_vars_program b)
       | KPcompose a b => EAssignables_app (bound_vars_program a) (bound_vars_program b)
       | KPloop a => bound_vars_program a

       | KPodeSystem ode psi => bound_vars_ode ode
       end.

(*
(** definition of prime of assignable *)
Definition prime_kassignable (a : KAssignable) : KAssignable :=
  match a with
  | KAssignVar v => DVar v
  | _ => a
  end.
*)

(*
(** prime of extended assignable *)
Definition prime_eassignable (a : EAssignables) : EAssignables :=
  match a with
  | FCS_finite (KAssignVar v) => FCS_finite (DVar v)
  | _ => a
  end.
*)

(** for a given term, returns list of its primes **)
Definition free_vars_term_prime (t : Term) : list KAssignable :=
  map KD (free_vars_term t).

(*
Fixpoint In_list_ext (e : EAssignable) (l: list EAssignable) : bool :=
  match l with
  | [] => false
  | h::t =>  if eassign_eq e h then true else In_list_ext e t
  end.
*)


(** Must-bound variable --- see Definition 8, Section 2.3 *)
Fixpoint must_bound_vars_program
         (p : Program) : EAssignables  :=
  match p with
  | KPconstant a => FCS_finite []

  | KPassign a theta    => bound_vars_program (KPassign a theta)
  | KPassignAny a       => bound_vars_program (KPassignAny a)
  | KPtest fi           => bound_vars_program (KPtest fi)

  | KPchoice  a b => EAssignables_inter (must_bound_vars_program a) (must_bound_vars_program b)
  | KPcompose a b => EAssignables_app (must_bound_vars_program a) (must_bound_vars_program b)
  | KPloop alpha => FCS_finite []

  | KPodeSystem ode psi => bound_vars_program (KPodeSystem ode psi)
  end.


(** substraction of KVariable form EAssignables *)
Definition remove_vars
           (e : EAssignables)
           (vs : list KVariable) : EAssignables :=
  remove_assignables e (map KAssignVar vs).

(** Free variables of atomic ODEs *)
Definition free_vars_atomic_ode (ode : AtomicODE) : EAssignables :=
  match ode with
  | ODEconst name => FCS_infinite []
  | ODEsing ds t =>
    EAssignables_app (assign2ext ds) (FCS_finite (free_vars_term t))
  end.

Fixpoint free_vars_ode (ode : ODE) : EAssignables :=
  match ode with
(*  | ODEem => FCS_finite []*)
  | ODEatomic c => free_vars_atomic_ode c
  | ODEprod l r => EAssignables_app (free_vars_ode l) (free_vars_ode r)
  end.

(** Free variables of formula --- see Definition 9, Section 2.3 *)
Fixpoint free_vars_formula
         (fi : Formula) : EAssignables :=
  match fi with
  | KFdot   => FCS_infinite []

  | KFtrue
  | KFfalse => FCS_finite []

  | KFgreaterEqual l r
  | KFgreater      l r
  | KFlessEqual    l r
  | KFless         l r
  | KFequal        l r
  | KFnotequal     l r => FCS_finite (free_vars_term l ++ free_vars_term r)

  | KFpredOf       f n args => FCS_finite (vec_flatten (Vector.map free_vars_term args))

  | KFquantifier   f a => FCS_infinite []

  | KFnot          l   => free_vars_formula l

  | KFand          l r
  | KFor           l r
  | KFimply        l r
  | KFequiv        l r => EAssignables_app (free_vars_formula l) (free_vars_formula r)

  | KFexistsVars x F
  | KFforallVars x F => remove_vars (free_vars_formula F) x

  | KFdiamond alpha F
  | KFbox    alpha F =>
    EAssignables_app
      (free_vars_program alpha)
      (remove_eassignables (free_vars_formula F) (must_bound_vars_program alpha))
  end

(** free variables of hybrid program --- see Definition 9, Section 2.3 *)
with free_vars_program
       (p : Program) : EAssignables :=
       match p with
       | KPconstant a => FCS_infinite []
       | KPassign a theta => FCS_finite (free_vars_term theta)
       | KPassignAny a => FCS_finite []
       | KPtest F => (free_vars_formula F)
       | KPchoice  a b => EAssignables_app (free_vars_program a) (free_vars_program b)
       | KPcompose a b =>
         EAssignables_app
           (free_vars_program a)
           (remove_eassignables (free_vars_program b) (must_bound_vars_program a))
       | KPloop a => free_vars_program a

       | KPodeSystem ode psi => EAssignables_app (free_vars_ode ode) (free_vars_formula psi)
       end.



(** Term signature --- see Section 2.3 *)
Fixpoint term_signature
           (t : Term) : list Symbol :=
    match t with
    | KTdot n => [SymbolDotTerm n]
(*    | KTanything => []*)
    | KTfuncOf f n args =>  SymbolFunction f n :: vec_flatten (Vector.map term_signature args)
    | KTnumber r   => []
    | KTread   x   => []
    | KTneg    l   => term_signature l
    | KTplus   l r
    | KTminus  l r
    | KTtimes  l r => term_signature l ++ term_signature r
    | KTdifferential theta => term_signature theta
    end.

(** signature for atomic ODEs  *)
Definition atomic_ode_signature (ode : AtomicODE) : list Symbol :=
  match ode with
  | ODEconst c => [SymbolODE c] (* c should probably be in the signature... *)
  | ODEsing ds t => term_signature t
  end.

Fixpoint ode_signature (ode : ODE) : list Symbol :=
  match ode with
(*  | ODEem => []*)
  | ODEatomic c => atomic_ode_signature c
  | ODEprod l r => ode_signature l ++ ode_signature r
  end.

(** Formula signature --- see Section 2.3 *)
Fixpoint formula_signature
         (fi : Formula) :  list Symbol :=
  match fi with
    | KFdot => [SymbolDotForm]

    | KFtrue
    | KFfalse => []

    | KFgreaterEqual l r
    | KFgreater      l r
    | KFlessEqual    l r
    | KFless         l r
    | KFequal        l r
    | KFnotequal     l r => term_signature l ++ term_signature r

    | KFpredOf     f n args => SymbolPredicate f n :: vec_flatten (Vector.map term_signature args)
    | KFquantifier f a => SymbolQuantifier f :: formula_signature a

    | KFnot   l   => formula_signature l

    | KFand   l r
    | KFor    l r
    | KFimply l r
    | KFequiv l r => formula_signature l ++ formula_signature r

    | KFexistsVars x F
    | KFforallVars x F => formula_signature F

    | KFdiamond alpha F
    | KFbox     alpha F => program_signature alpha ++ formula_signature F
end

(** Hybrid program signature --- see Section 2.3 *)
with program_signature
       (p : Program) : list Symbol :=
       match p with
       | KPconstant a => [SymbolProgramConst a]
       | KPassign a theta => term_signature theta
       | KPassignAny a => []
       | KPtest F => formula_signature F
       | KPchoice  a b => program_signature a ++ program_signature b
       | KPcompose a b => program_signature a ++ program_signature b
       | KPloop a => program_signature a
       | KPodeSystem ode psi => ode_signature ode ++ formula_signature psi
end.
