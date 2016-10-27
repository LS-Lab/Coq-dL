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

Require Export static_sem.
(*Require Export Coq.Sets.Ensembles. *)
Require Export tactics2.
(*Require Export decidability.*)
Require Import List.
Require Export terms_util2.


(**

  This file implements US rule.
  Definition of admissibility can be found in this file also.

 *)


Definition atomicOde2terms (ode : AtomicODE) : list Term :=
  match ode with
  | ODEconst c => []
  | ODEsing ds t => [t]
  end.

Fixpoint ode2terms (ode : ODE) : list Term :=
  match ode with
(*  | ODEem => []*)
  | ODEatomic a => atomicOde2terms a
  | ODEprod o1 o2 => ode2terms o1 ++ ode2terms o2
  end.

Definition free_vars_terms (l : list Term) : list KAssignable :=
  flat_map free_vars_term l.


(** Uniform substitution --- see Section 3 *)
Inductive UniformSubstitutionEntry :=
| USE_function :
    FunctionSymbol
    -> nat
    -> Term
    -> UniformSubstitutionEntry
| USE_pred :
    PredicateSymbol
    -> nat
    -> Formula
    -> UniformSubstitutionEntry
| USE_quant :
    QuantifierSymbol
    -> Formula
    -> UniformSubstitutionEntry
| USE_constant :
    ProgramConstName
    -> Program
    -> UniformSubstitutionEntry
| USE_ode :
    ODEConst
    -> ODE
    -> UniformSubstitutionEntry.

(** Uniform substitution --- see Section 3 *)
Definition UniformSubstitution := list UniformSubstitutionEntry.

Definition free_vars_uniform_substitution_entry
           (e : UniformSubstitutionEntry) : EAssignables :=
  match e with
  | USE_function f n T => FCS_finite (free_vars_term T)
  | USE_pred     f n F => free_vars_formula F
  | USE_quant    f F   => FCS_finite [] (*free_vars_formula F*)
  | USE_constant a P   => FCS_finite [] (*free_vars_program P*)
  | USE_ode      c o   => FCS_finite [] (*free_vars_ode o*)
  end.


(*
(** returns True if two US entries are equal *)
Fixpoint us_eq (e1 e2 : UniformSubstitutionEntry) : bool :=
  match e1, e2 with
  | USE_function f1 n1 T1, USE_function f2 n2 T2 =>
    if FunctionSymbol_dec f1 f2 then
      if deq_nat n1 n2 then
        if term_dec T1 T2 then true
        else false
      else false
    else false

  | USE_pred p1 n1 F1, USE_pred p2 n2 F2 =>
    if PredicateSymbol_dec p1 p2 then
      if deq_nat n1 n2 then
        if formula_dec F1 F2 then true
        else false
      else false
    else false

  | USE_quant q1 F1, USE_quant q2 F2 =>
    if QuantifierSymbol_dec q1 q2 then
      if formula_dec F1 F2 then true
      else false
    else false

  | USE_constant a1 P1, USE_constant a2 P2 =>
    if ProgramConstName_dec a1 a2 then
      if program_dec P1 P2 then true
      else false
    else false

  |_ , _ => false
  end.
*)

(*
(** returns True if US entry e is part of US s *)
Fixpoint us_in (e : UniformSubstitutionEntry) (s: UniformSubstitution): bool :=
  match s with
  | [] => false
  | h::t => if us_eq h e
            then true
            else false
  end.
*)

(* old definition
Definition free_vars_uniform_substitution
           (s : UniformSubstitution) : list  EAssignable :=
  fun x =>
    exists e,
      us_in e s
      /\ eassign_in (free_vars_uniform_substitution_entry e) x.
 *)

(** free variables in US (duplicates can occur) *)
Fixpoint free_vars_uniform_substitution_with_duplicates
         (s : UniformSubstitution) : EAssignables :=
  match s with
  | [] => EA_assignables []
  | h :: t =>
    EAssignables_app
      (free_vars_uniform_substitution_entry h)
      (free_vars_uniform_substitution_with_duplicates t)
  end.

(*
(*remove duplicates from the previous one -- Why? *)
Fixpoint free_vars_uniform_substitution_no_duplicates
         (l : EAssignables) : EAssignables :=
  match l with
  | [] => []
  | h :: t =>
    if eassign_in h t
    then free_vars_uniform_substitution_no_duplicates t
    else h ::  free_vars_uniform_substitution_no_duplicates t
  end.
*)

(** Free variables introduced by the uniform substitution --- see Definition 10, Section 3 *)
Definition free_vars_uniform_substitution
           (s : UniformSubstitution) : EAssignables :=
(*  free_vars_uniform_substitution_no_duplicates*)
  (free_vars_uniform_substitution_with_duplicates s).


(** returns True if two US symbols are equal *)
Fixpoint symbols_dec (h e: Symbol) : bool :=
  match h, e with
  | SymbolFunction f1 n1, SymbolFunction f2 n2 =>
    if FunctionSymbol_dec f1 f2 then
      if deq_nat n1 n2 then true
      else false
    else false

  | SymbolPredicate f1 n1, SymbolPredicate f2 n2 =>
    if PredicateSymbol_dec f1 f2 then
      if deq_nat n1 n2 then true
      else false
    else false

  | SymbolQuantifier f1, SymbolQuantifier f2 =>
    if QuantifierSymbol_dec f1 f2
    then true
    else false

  | SymbolProgramConst a1, SymbolProgramConst a2 =>
    if ProgramConstName_dec a1 a2
    then true
    else false

  | _ , _  => false
  end.

(** decidability of US symbols *)
Lemma Symbol_dec :
  forall a b : Symbol, {a = b} + {a <> b}.
Proof.
  destruct a, b; simpl; prove_dec.
  { destruct (FunctionSymbol_dec f f0); subst; prove_dec.
    destruct (deq_nat n n0); subst; prove_dec. }
  { destruct (deq_nat n n0); subst; prove_dec. }
  { destruct (PredicateSymbol_dec f f0); subst; prove_dec.
    destruct (deq_nat n n0); subst; prove_dec. }
  { destruct (QuantifierSymbol_dec f f0); subst; prove_dec. }
  { destruct (ODEConst_dec c c0); subst; prove_dec. }
  { destruct (ProgramConstName_dec a a0); subst; prove_dec. }
Defined.

(**  returns TRue if symbol is in list *)
Fixpoint in_signature_bool (e : Symbol)(l: list Symbol): bool :=
  match l with
  | [] => false
  | h :: t =>
    if Symbol_dec h e
    then true
    else in_signature_bool e t
  end.

(** decidability of signatures *)
Definition in_signature_dec (e : Symbol) (l: list Symbol)
  : {List.In e l} + {not (List.In e l)}
  := in_dec Symbol_dec e l.

(** returns True if symbol is in list *)
Definition in_signature (e : Symbol) (l: list Symbol) : bool
  := if in_signature_dec e l then true else false.

(** return True if US entry is in term *)
Definition uniform_substitution_entry_in_term (e : UniformSubstitutionEntry) (theta : Term) : bool :=
  match e with
  | USE_function f n T => in_signature (SymbolFunction f n)   (term_signature theta)
  | USE_pred     f n F => in_signature (SymbolPredicate f n)  (term_signature theta)
  | USE_quant    f F   => in_signature (SymbolQuantifier f)   (term_signature theta)
  | USE_constant a P   => in_signature (SymbolProgramConst a) (term_signature theta)
  | USE_ode      c o   => in_signature (SymbolODE c)          (term_signature theta)
  end.

(** return True if US entry is in formula *)
Definition uniform_substitution_entry_in_formula (e : UniformSubstitutionEntry) (fi : Formula) : bool :=
  match e with
  | USE_function f n T => in_signature (SymbolFunction f n)   (formula_signature fi)
  | USE_pred     f n F => in_signature (SymbolPredicate f n)  (formula_signature fi)
  | USE_quant    f F   => in_signature (SymbolQuantifier f)   (formula_signature fi)
  | USE_constant a P   => in_signature (SymbolProgramConst a) (formula_signature fi)
  | USE_ode      c o   => in_signature (SymbolODE c)          (formula_signature fi)
  end.

(** returns true if US entry is in program *)
Definition uniform_substitution_entry_in_program (e : UniformSubstitutionEntry) (pr : Program) : bool :=
  match e with
  | USE_function f n T => in_signature (SymbolFunction f n)   (program_signature pr)
  | USE_pred     f n F => in_signature (SymbolPredicate f n)  (program_signature pr)
  | USE_quant    f F   => in_signature (SymbolQuantifier f)   (program_signature pr)
  | USE_constant a P   => in_signature (SymbolProgramConst a) (program_signature pr)
  | USE_ode      c o   => in_signature (SymbolODE c)          (program_signature pr)
  end.

Lemma in_term_signature_implies :
  forall s t,
    In s (term_signature t)
    ->
    (
      (exists n, s = SymbolDotTerm n)
      \/
      (exists f n, s = SymbolFunction f n)
    ).
Proof.
  term_ind t Case; introv i; simpl in *; tcsp; repndors; subst; tcsp;
    try (complete (apply in_app_iff in i; repndors;[autodimp IHt1 hyp|autodimp IHt2 hyp])).
  { Case "KTdot".
    left; eexists; dands; eauto. }
  { Case "KTfuncOf".
    right; eexists; eexists; eauto. }
  { Case "KTfuncOf".
    apply in_vec_flatten in i; exrepnd.
    apply in_vec_map in i1; exrepnd; subst.
    apply IHargs in i0; auto. }
Qed.

Lemma uniform_substitution_entry_in_term_eq :
  forall e t,
    uniform_substitution_entry_in_term e t
    = match e with
      | USE_function f n T => in_signature (SymbolFunction f n) (term_signature t)
      | _ => false
      end.
Proof.
  introv; destruct e; simpl; unfold in_signature; dest_cases w;
    try (complete (apply in_term_signature_implies in i; repndors; exrepnd; ginv)).
Qed.


(** Restriction of uniform substitution on terms --- see Definition 10, Section 3 *)
Fixpoint uniform_substitution_restriction_term
         (s : UniformSubstitution)
         (T : Term) : UniformSubstitution :=
  match s with
  | [] => []
  | e :: t =>
    if uniform_substitution_entry_in_term e T
    then e :: uniform_substitution_restriction_term t T
    else uniform_substitution_restriction_term t T
  end.


(** Restriction of uniform substitution on formulas --- see Definition 10, Section 3 *)
Fixpoint uniform_substitution_restriction_formula
         (s : UniformSubstitution)
         (F : Formula) : UniformSubstitution :=
  match s with
  | [] => []
  | e :: t =>
    if uniform_substitution_entry_in_formula e F
    then e :: uniform_substitution_restriction_formula t F
    else uniform_substitution_restriction_formula t F
  end.

(** Restriction of uniform substitution on programs --- see Definition 10, Section 3 *)
Fixpoint uniform_substitution_restriction_program
         (s : UniformSubstitution)
         (P : Program) : UniformSubstitution :=
  match s with
  | [] => []
  | e :: t =>
    if uniform_substitution_entry_in_program e P
    then e :: uniform_substitution_restriction_program t P
    else uniform_substitution_restriction_program t P
  end.


(** free variables of US restricted by term t *)
Definition free_vars_sub_restrict_term (s : UniformSubstitution) (t : Term) : EAssignables :=
  free_vars_uniform_substitution
    (uniform_substitution_restriction_term s t).

(** free variables of US restricted by formula f *)
Definition free_vars_sub_restrict_formula (s : UniformSubstitution) (f : Formula) : EAssignables :=
  free_vars_uniform_substitution
    (uniform_substitution_restriction_formula s f).

(** free variables restricted by program *)
Definition free_vars_sub_restrict_program (s : UniformSubstitution) (p : Program) : EAssignables :=
  free_vars_uniform_substitution
    (uniform_substitution_restriction_program s p).

(** U admissible for terms --- see Definition 10, Section 3 *)
Definition U_admissible_term
           (U : EAssignables)
           (t : Term)
           (s : UniformSubstitution) : bool :=
  eassignables_disj U (free_vars_sub_restrict_term s t).

Definition terms_signature (l : list Term) : list Symbol :=
  flat_map term_signature l.

Definition uniform_substitution_entry_in_terms
         (e : UniformSubstitutionEntry)
         (l : list Term) : bool :=
  match e with
  | USE_function f n T => in_signature (SymbolFunction f n)   (terms_signature l)
  | USE_pred     f n F => in_signature (SymbolPredicate f n)  (terms_signature l)
  | USE_quant    f F   => in_signature (SymbolQuantifier f)   (terms_signature l)
  | USE_constant a P   => in_signature (SymbolProgramConst a) (terms_signature l)
  | USE_ode      c o   => in_signature (SymbolODE c)          (terms_signature l)
  end.

Lemma in_terms_signature_implies :
  forall s t,
    In s (terms_signature t)
    ->
    (
      (exists n, s = SymbolDotTerm n)
      \/
      (exists f n, s = SymbolFunction f n)
    ).
Proof.
  introv i.
  unfold terms_signature in i.
  rewrite in_flat_map in i; exrepnd.
  apply in_term_signature_implies in i0; auto.
Qed.

Lemma uniform_substitution_entry_in_terms_eq :
  forall e t,
    uniform_substitution_entry_in_terms e t
    = match e with
      | USE_function f n T => in_signature (SymbolFunction f n) (terms_signature t)
      | _ => false
      end.
Proof.
  introv; destruct e; simpl; unfold in_signature; dest_cases w;
    try (complete (apply in_terms_signature_implies in i; repndors; exrepnd; ginv)).
Qed.

Fixpoint uniform_substitution_restriction_terms
         (s : UniformSubstitution)
         (l : list Term) : UniformSubstitution :=
  match s with
  | [] => []
  | e :: t =>
    if uniform_substitution_entry_in_terms e l
    then e :: uniform_substitution_restriction_terms t l
    else uniform_substitution_restriction_terms t l
  end.

Definition free_vars_sub_restrict_terms
           (s : UniformSubstitution)
           (l : list Term) : EAssignables :=
  free_vars_uniform_substitution
    (uniform_substitution_restriction_terms s l).

Definition U_admissible_terms
           (U : EAssignables)
           (l : list Term)
           (s : UniformSubstitution) : bool :=
  eassignables_disj U (free_vars_sub_restrict_terms s l).

Definition U_admissible_term_t
           (U : EAssignables)
           (t u : Term) : bool :=
  eassignables_disj U (EA_assignables (free_vars_term u)).

(** U admissible for formulas --- see Definition 10, Section 3 *)
Definition U_admissible_formula
           (U : EAssignables)
           (fi : Formula)
           (sigma : UniformSubstitution) : bool :=
  eassignables_disj U (free_vars_sub_restrict_formula sigma fi).

(** U admissible for programs --- see Definition 10, Section 3 *)
Definition U_admissible_program
           (U : EAssignables)
           (pr : Program)
           (sigma : UniformSubstitution) : bool :=
  eassignables_disj U (free_vars_sub_restrict_program sigma pr).



(*bound_variables_in_terms doesn't exist in the paper
Definition addmisible_term {s: KSort} (theta : Term s) (sigma : Term s-> Term s) : Prop :=
  forall x,
    In  _ (bound_variables_in_terms theta) x->
       not ( In _ ( free_variables_in_terms (sigma theta))  x).
 *)

(****************************************************************************************)

Definition omap {T U} (a : option T) (f : T -> U) : option U :=
  match a with
  | Some x => Some (f x)
  | None => None
  end.

Definition bind {T U} (a : option T) (f : T -> option U) : option U :=
  match a with
  | Some x => f x
  | None => None
  end.

Definition ret {T} (a : T) : option T := Some a.

Definition on_test {T} (b : bool) (t : option T) :=
  if b then t else None.

Notation "a >>= f" := (bind a f) (at level 100).
Notation "a >=> f" := (omap a f) (at level 100).


Fixpoint vec2bool {n} (v : Vector.t bool n) : bool :=
  match v with
  | Vector.nil => false
  | Vector.cons b m w => b || vec2bool w
  end.

Lemma vec2bool_map_true_implies :
  forall {A} b {n : nat} (v : Vector.t A n) (F : A -> bool),
    vec2bool (Vector.map F v) = true
    -> exists m, (m < n)%nat /\ F (vec_nth v m b) = true.
Proof.
  induction n; introv.

  { apply (@Vector.case0
             A
             (fun v =>
                vec2bool (Vector.map F v) = true
                -> exists m, (m < 0)%nat /\ F (vec_nth v m b) = true));
      simpl; clear v.
    intro xx; inversion xx. }

  { apply (Vector.caseS' v); introv; clear v.
    simpl.
    intro hyp.
    apply orb_true_iff in hyp; repndors.
    { exists 0%nat; dands; auto; omega. }
    apply IHn in hyp; exrepnd.
    exists (S m); dands; auto; omega. }
Qed.

Lemma implies_subset_vec_flatten_map_r :
  forall {A B} a {n} (v : Vector.t A n) (F : A -> list B) l m,
    (m < n)%nat
    -> subset l (F (vec_nth v m a))
    -> subset l (vec_flatten (Vector.map F v)).
Proof.
  induction n; introv ltmn; try omega.
  apply (Vector.caseS' v); introv; clear v.
  simpl.
  intro ss.
  destruct m.
  { apply implies_subset_app_r; auto. }
  { apply implies_subset_app_r; right; eapply IHn;[|eauto]; omega. }
Qed.

Fixpoint containsDot (t : Term) : bool :=
  match t with
  | KTdot _ => true
  | KTfuncOf _ _ args => vec2bool (Vector.map containsDot args)
  | KTnumber r   => false
  | KTread   x   => false
  | KTneg    l   => containsDot l
  | KTplus   l r => containsDot l || containsDot r
  | KTminus  l r => containsDot l || containsDot r
  | KTtimes  l r => containsDot l || containsDot r
  | KTdivide l r => containsDot l || containsDot r
  | KTpower  l r => containsDot l || containsDot r
  | KTdifferential theta => containsDot theta
  end.

Fixpoint containsDotN (n : nat) (t : Term) : bool :=
  match t with
  | KTdot m => if deq_nat n m then true else false
  | KTfuncOf _ _ args => vec2bool (Vector.map (containsDotN n) args)
  | KTnumber r   => false
  | KTread   x   => false
  | KTneg    l   => containsDotN n l
  | KTplus   l r => containsDotN n l || containsDotN n r
  | KTminus  l r => containsDotN n l || containsDotN n r
  | KTtimes  l r => containsDotN n l || containsDotN n r
  | KTdivide l r => containsDotN n l || containsDotN n r
  | KTpower  l r => containsDotN n l || containsDotN n r
  | KTdifferential t => containsDotN n t
  end.

Definition free_vars_term_restrict_term (u : Term) (t : Term) : list KAssignable :=
  if containsDot t
  then free_vars_term u
  else [].

Definition free_vars_vec_term_restrict_term
           {n} (v : Vector.t Term n) (t : Term) : list KAssignable :=
  if containsDot t
  then free_vars_vec_term v
  else [].

(* TODO: use that one instead: *)
Definition free_vars_vec_term_restrict_term0
           {n} (v : Vector.t Term n) (t : Term) : list KAssignable :=
  vec_flatten
    (vec_mapn
       (fun u m => if containsDotN (n - S m) t then free_vars_term u else [])
       v).

(** replaces dot by u in t *)
Fixpoint substitution_dot_term (t : Term) (u : Term) : option Term :=
  match t with
  | KTdot n => ret u
  | KTfuncOf f n args =>
    (vec_opt2opt_vec (Vector.map (fun a => substitution_dot_term a u) args))
      >=> KTfuncOf f n
  | KTnumber r => ret (KTnumber r)
  | KTread x => ret (KTread x)
  | KTneg t => (substitution_dot_term t u) >=> KTneg
  | KTplus   l r => (substitution_dot_term l u) >>= (fun a => (substitution_dot_term r u) >=> KTplus a)
  | KTminus  l r => (substitution_dot_term l u) >>= (fun a => (substitution_dot_term r u) >=> KTminus a)
  | KTtimes  l r => (substitution_dot_term l u) >>= (fun a => (substitution_dot_term r u) >=> KTtimes a)
  | KTdivide l r => (substitution_dot_term l u) >>= (fun a => (substitution_dot_term r u) >=> KTdivide a)
  | KTpower  l r => (substitution_dot_term l u) >>= (fun a => (substitution_dot_term r u) >=> KTpower a)
  | KTdifferential t =>
    on_test
      (nullb (free_vars_term_restrict_term u t))
      ((substitution_dot_term t u) >=> KTdifferential)
  end.

(** replaces dot(n) by u[n] in t *)
Fixpoint substitution_dots_term (t : Term) {m} (u : Vector.t Term m) : option Term :=
  match t with
  | KTdot n => ret (vec_nth u n (KTdot n))
  | KTfuncOf f n args =>
    (vec_opt2opt_vec (Vector.map (fun a => substitution_dots_term a u) args))
      >=> KTfuncOf f n
  | KTnumber r => ret (KTnumber r)
  | KTread x => ret (KTread x)
  | KTneg t => (substitution_dots_term t u) >=> KTneg
  | KTplus   l r => (substitution_dots_term l u) >>= (fun a => (substitution_dots_term r u) >=> KTplus a)
  | KTminus  l r => (substitution_dots_term l u) >>= (fun a => (substitution_dots_term r u) >=> KTminus a)
  | KTtimes  l r => (substitution_dots_term l u) >>= (fun a => (substitution_dots_term r u) >=> KTtimes a)
  | KTdivide l r => (substitution_dots_term l u) >>= (fun a => (substitution_dots_term r u) >=> KTdivide a)
  | KTpower  l r => (substitution_dots_term l u) >>= (fun a => (substitution_dots_term r u) >=> KTpower a)
  | KTdifferential t =>
    on_test
      (nullb (free_vars_vec_term_restrict_term u t))
      ((substitution_dots_term t u) >=> KTdifferential)
  end.

(*
Fixpoint substitution_dot_diff (dp : DifferentialProgram) (dp1: DifferentialProgram) : DifferentialProgram :=
  match dp with
  | differentialProgramConst a => dp1
  | atomicODE xp t => atomicODE xp (substitution_dot_term t dp1)
  | differentialProduct l r => DifferentialProgram (substitution_dot_diff l dp1) (substitution_dot_diff r dp1)
end.
*)

(** converts list of variables to list of KAssignables **)
Definition vars2assign (l : list KVariable) : list KAssignable :=
  map KAssignVar l.


(** Substitution of dot term in DifferentialProgram program primitives *)
Definition substitution_dot_term_in_atomic_ode
           (ode : AtomicODE)
           (t   : Term) : option AtomicODE :=
  match ode with
  | ODEconst n => ret (ODEconst n)
  | ODEsing ds theta => (substitution_dot_term theta t) >=> ODEsing ds
  end.

(** Substitution of dot term in DifferentialProgram program *)
Fixpoint substitution_dot_term_in_ode
         (ode : ODE)
         (u   : Term) : option ODE :=
  match ode with
(*  | ODEem => ret ODEem*)
  | ODEatomic c =>
    (substitution_dot_term_in_atomic_ode c u)
      >=> ODEatomic
  | ODEprod l r =>
    (substitution_dot_term_in_ode l u)
      >>= (fun a => (substitution_dot_term_in_ode r u)
                      >=> ODEprod a)
  end.

(** Substitution of dot term in formula --- see Section 3 *)
Fixpoint substitution_dot_term_in_formula (fi : Formula) (u : Term) : option Formula :=
  match fi with
  | KFdot   => ret KFdot
  | KFtrue  => ret KFtrue
  | KFfalse => ret KFfalse

  | KFequal        l r => (substitution_dot_term l u) >>= (fun a => (substitution_dot_term r u) >=> KFequal a)
  | KFnotequal     l r => (substitution_dot_term l u) >>= (fun a => (substitution_dot_term r u) >=> KFnotequal a)
  | KFgreaterEqual l r => (substitution_dot_term l u) >>= (fun a => (substitution_dot_term r u) >=> KFgreaterEqual a)
  | KFgreater      l r => (substitution_dot_term l u) >>= (fun a => (substitution_dot_term r u) >=> KFgreater a)
  | KFlessEqual    l r => (substitution_dot_term l u) >>= (fun a => (substitution_dot_term r u) >=> KFlessEqual a)
  | KFless         l r => (substitution_dot_term l u) >>= (fun a => (substitution_dot_term r u) >=> KFless a)

  | KFpredOf     f n args =>
    (vec_opt2opt_vec (Vector.map (fun a => substitution_dot_term a u) args))
      >=> KFpredOf f n
  | KFquantifier f a =>
    on_test
      (nullb (free_vars_term u))
      (substitution_dot_term_in_formula a u) >=> KFquantifier f

  | KFnot   l   => (substitution_dot_term_in_formula l u) >=> KFnot
  | KFand   l r => (substitution_dot_term_in_formula l u) >>= (fun a => (substitution_dot_term_in_formula r u) >=> KFand a)
  | KFor    l r => (substitution_dot_term_in_formula l u) >>= (fun a => (substitution_dot_term_in_formula r u) >=> KFor a)
  | KFimply l r => (substitution_dot_term_in_formula l u) >>= (fun a => (substitution_dot_term_in_formula r u) >=> KFimply a)
  | KFequiv l r => (substitution_dot_term_in_formula l u) >>= (fun a => (substitution_dot_term_in_formula r u) >=> KFequiv a)

  | KFforallVars vars f =>
    on_test
      (KAssignables_disj (vars2assign vars) (free_vars_term u))
      (substitution_dot_term_in_formula f u) >=> KFforallVars vars

  | KFexistsVars vars f =>
    on_test
      (KAssignables_disj (vars2assign vars) (free_vars_term u))
      (substitution_dot_term_in_formula f u) >=> KFexistsVars vars

  | KFbox     p f =>
    (substitution_dot_term_in_program p u)
      >>= (fun a =>
             on_test
               (eassignables_disj (bound_vars_program a) (EA_assignables (free_vars_term u)))
               (substitution_dot_term_in_formula f u) >=> KFbox a)

  | KFdiamond p f =>
    (substitution_dot_term_in_program p u)
      >>= (fun a =>
             on_test
               (eassignables_disj (bound_vars_program a) (EA_assignables (free_vars_term u)))
               (substitution_dot_term_in_formula f u) >=> KFdiamond a)

  | KFdifferentialFormula l => (substitution_dot_term_in_formula l u) >=> KFdifferentialFormula
  end

(** Substitution of dot term in program --- see Section 3 *)
with substitution_dot_term_in_program (pr : Program) (v : Term) : option Program :=
       match pr with
       | KPconstant a  => ret (KPconstant a)
       | KPassign  x t => (substitution_dot_term t v) >=> KPassign x
       | KPassignAny x => ret (KPassignAny x)

       | KPtest f => (substitution_dot_term_in_formula f v) >=> KPtest

       | KPchoice  l r => (substitution_dot_term_in_program l v) >>= (fun a => (substitution_dot_term_in_program r v) >=> KPchoice a)
       | KPcompose l r =>
         (substitution_dot_term_in_program l v)
           >>= (fun a =>
                  on_test
                    (eassignables_disj (bound_vars_program a) (EA_assignables (free_vars_term v)))
                    (substitution_dot_term_in_program r v) >=> KPcompose a)

       | KPparallel cl cr l r => (substitution_dot_term_in_program l v) >>= (fun a => (substitution_dot_term_in_program r v) >=>  KPparallel cl cr a)

       | KPloop p =>
         (substitution_dot_term_in_program p v)
           >>= (fun a =>
                  on_test
                    (eassignables_disj (bound_vars_program a) (EA_assignables (free_vars_term v)))
                    (ret (KPloop a)))

       | KPsend c t  => (substitution_dot_term t v) >=> KPsend c
       | KPreceive c var => ret (KPreceive c var)
       | KPbroadcast c t var => (substitution_dot_term t v) >=> (fun a => KPbroadcast c a var)

       | KPodeSystem ode f =>
         on_test
           (eassignables_disj
              (bound_vars_ode ode)
              (EA_assignables (free_vars_term v)))
           ((substitution_dot_term_in_ode ode v)
              >>= (fun O =>
                     ((substitution_dot_term_in_formula f v)
                        >=> KPodeSystem O)))
       end.


(** Substitution of dot term in atomic ODEs *)
Definition substitution_dots_term_in_atomic_ode
           (ode : AtomicODE)
           {m}
           (t   : Vector.t Term m) : option AtomicODE :=
  match ode with
  | ODEconst n => ret (ODEconst n)
  | ODEsing ds theta => (substitution_dots_term theta t) >=> ODEsing ds
  end.

(** Substitution of dot term in ODEs *)
Fixpoint substitution_dots_term_in_ode
         (ode : ODE)
         {m}
         (u   : Vector.t Term m) : option ODE :=
  match ode with
(*  | ODEem => ret ODEem*)
  | ODEatomic c =>
    (substitution_dots_term_in_atomic_ode c u)
      >=> ODEatomic
  | ODEprod l r =>
    (substitution_dots_term_in_ode l u)
      >>= (fun a => (substitution_dots_term_in_ode r u)
                      >=> ODEprod a)
  end.

(** Substitution of dot term in formula --- see Section 3 *)
Fixpoint substitution_dots_term_in_formula
         (fi : Formula)
         {m}
         (u : Vector.t Term m) : option Formula :=
  match fi with
  | KFdot   => ret KFdot
  | KFtrue  => ret KFtrue
  | KFfalse => ret KFfalse

  | KFequal        l r => (substitution_dots_term l u) >>= (fun a => (substitution_dots_term r u) >=> KFequal a)
  | KFnotequal     l r => (substitution_dots_term l u) >>= (fun a => (substitution_dots_term r u) >=> KFnotequal a)
  | KFgreaterEqual l r => (substitution_dots_term l u) >>= (fun a => (substitution_dots_term r u) >=> KFgreaterEqual a)
  | KFgreater      l r => (substitution_dots_term l u) >>= (fun a => (substitution_dots_term r u) >=> KFgreater a)
  | KFlessEqual    l r => (substitution_dots_term l u) >>= (fun a => (substitution_dots_term r u) >=> KFlessEqual a)
  | KFless         l r => (substitution_dots_term l u) >>= (fun a => (substitution_dots_term r u) >=> KFless a)

  | KFpredOf     f n args =>
    (vec_opt2opt_vec (Vector.map (fun a => substitution_dots_term a u) args))
      >=> KFpredOf f n
  | KFquantifier f a =>
    on_test
      (nullb (free_vars_vec_term u))
      (substitution_dots_term_in_formula a u) >=> KFquantifier f

  | KFnot   l   => (substitution_dots_term_in_formula l u) >=> KFnot
  | KFand   l r => (substitution_dots_term_in_formula l u) >>= (fun a => (substitution_dots_term_in_formula r u) >=> KFand a)
  | KFor    l r => (substitution_dots_term_in_formula l u) >>= (fun a => (substitution_dots_term_in_formula r u) >=> KFor a)
  | KFimply l r => (substitution_dots_term_in_formula l u) >>= (fun a => (substitution_dots_term_in_formula r u) >=> KFimply a)
  | KFequiv l r => (substitution_dots_term_in_formula l u) >>= (fun a => (substitution_dots_term_in_formula r u) >=> KFequiv a)

  | KFforallVars vars f =>
    on_test
      (KAssignables_disj (vars2assign vars) (free_vars_vec_term u))
      (substitution_dots_term_in_formula f u) >=> KFforallVars vars

  | KFexistsVars vars f =>
    on_test
      (KAssignables_disj (vars2assign vars) (free_vars_vec_term u))
      (substitution_dots_term_in_formula f u) >=> KFexistsVars vars

  | KFbox     p f =>
    (substitution_dots_term_in_program p u)
      >>= (fun a =>
             on_test
               (eassignables_disj (bound_vars_program a) (EA_assignables (free_vars_vec_term u)))
               (substitution_dots_term_in_formula f u) >=> KFbox a)

  | KFdiamond p f =>
    (substitution_dots_term_in_program p u)
      >>= (fun a =>
             on_test
               (eassignables_disj (bound_vars_program a) (EA_assignables (free_vars_vec_term u)))
               (substitution_dots_term_in_formula f u) >=> KFdiamond a)

  | KFdifferentialFormula l => (substitution_dots_term_in_formula l u) >=> KFdifferentialFormula
  end

(** Substitution of dot term in program --- see Section 3 *)
with substitution_dots_term_in_program
       (pr : Program)
       {m}
       (v : Vector.t Term m) : option Program :=
       match pr with
       | KPconstant a  => ret (KPconstant a)
       | KPassign  x t => (substitution_dots_term t v) >=> KPassign x
       | KPassignAny x => ret (KPassignAny x)

       | KPtest f => (substitution_dots_term_in_formula f v) >=> KPtest

       | KPchoice  l r => (substitution_dots_term_in_program l v) >>= (fun a => (substitution_dots_term_in_program r v) >=> KPchoice a)
       | KPcompose l r =>
         (substitution_dots_term_in_program l v)
           >>= (fun a =>
                  on_test
                    (eassignables_disj (bound_vars_program a) (EA_assignables (free_vars_vec_term v)))
                    (substitution_dots_term_in_program r v) >=> KPcompose a)

       | KPparallel cl cr l r => (substitution_dots_term_in_program l v) >>= (fun a => (substitution_dots_term_in_program r v) >=>  KPparallel cl cr a)

       | KPloop p =>
         (substitution_dots_term_in_program p v)
           >>= (fun a =>
                  on_test
                    (eassignables_disj (bound_vars_program a) (EA_assignables (free_vars_vec_term v)))
                    (ret (KPloop a)))

       | KPsend c t  => (substitution_dots_term t v) >=> KPsend c
       | KPreceive c var => ret (KPreceive c var)
       | KPbroadcast c t var => (substitution_dots_term t v) >=> (fun a => KPbroadcast c a var)

       | KPodeSystem ode f =>
         on_test
           (eassignables_disj
              (bound_vars_ode ode)
              (EA_assignables (free_vars_vec_term v)))
           ((substitution_dots_term_in_ode ode v)
              >>= (fun O =>
                     ((substitution_dots_term_in_formula f v)
                        >=> KPodeSystem O)))
       end.

(** Substitution of dot formula in formula --- see Section 3 *)
Fixpoint substitution_dot_formula_in_formula (fi : Formula) (u : Formula) : option Formula :=
  match fi with
  | KFdot   => ret u
  | KFtrue  => ret KFtrue
  | KFfalse => ret KFfalse

  | KFequal        l r => ret (KFequal        l r)
  | KFnotequal     l r => ret (KFnotequal     l r)
  | KFgreaterEqual l r => ret (KFgreaterEqual l r)
  | KFgreater      l r => ret (KFgreater      l r)
  | KFlessEqual    l r => ret (KFlessEqual    l r)
  | KFless         l r => ret (KFless         l r)

  | KFpredOf     f n a => ret (KFpredOf f n a)
  | KFquantifier f a =>
    (*on_test
      (eassignables_disj (EA_all []) (free_vars_formula u))*)
      ((substitution_dot_formula_in_formula a u) >=> KFquantifier f)

  | KFnot   l   => (substitution_dot_formula_in_formula l u) >=> KFnot
  | KFand   l r => (substitution_dot_formula_in_formula l u) >>= (fun a => (substitution_dot_formula_in_formula r u) >=> KFand   a)
  | KFor    l r => (substitution_dot_formula_in_formula l u) >>= (fun a => (substitution_dot_formula_in_formula r u) >=> KFor    a)
  | KFimply l r => (substitution_dot_formula_in_formula l u) >>= (fun a => (substitution_dot_formula_in_formula r u) >=> KFimply a)
  | KFequiv l r => (substitution_dot_formula_in_formula l u) >>= (fun a => (substitution_dot_formula_in_formula r u) >=> KFequiv a)

  | KFforallVars x f =>
    (*on_test
      (eassignables_disj (vars2ext x) (free_vars_formula u))*)
      ((substitution_dot_formula_in_formula f u) >=> KFforallVars x)

  | KFexistsVars x f =>
    (*on_test
      (eassignables_disj (vars2ext x) (free_vars_formula u))*)
      ((substitution_dot_formula_in_formula f u) >=> KFexistsVars x)

  | KFbox     p f =>
    (substitution_dot_formula_in_program p u)
      >>= (fun a =>
             (*on_test
               (eassignables_disj (bound_vars_program a) (free_vars_formula u))*)
               (substitution_dot_formula_in_formula f u) >=> KFbox a)

  | KFdiamond p f =>
    (substitution_dot_formula_in_program p u)
      >>= (fun a =>
             (*on_test
               (eassignables_disj (bound_vars_program a) (free_vars_formula u))*)
               (substitution_dot_formula_in_formula f u) >=> KFdiamond a)

  | KFdifferentialFormula l => (substitution_dot_formula_in_formula l u) >=> KFdifferentialFormula
  end

(** Substitution of dot formula in program --- see Section 3 *)
with substitution_dot_formula_in_program (pr : Program) (v : Formula) : option Program :=
       match pr with
       | KPconstant a  => ret (KPconstant a)
       | KPassign  x t => ret (KPassign x t)
       | KPassignAny x => ret (KPassignAny x)

       | KPtest f => (substitution_dot_formula_in_formula f v) >=> KPtest

       | KPchoice  l r => (substitution_dot_formula_in_program l v) >>= (fun a => (substitution_dot_formula_in_program r v) >=> KPchoice  a)
       | KPcompose l r =>
         (substitution_dot_formula_in_program l v)
           >>= (fun a =>
                  (*on_test
                    (eassignables_disj (bound_vars_program a) (free_vars_formula v))*)
                    (substitution_dot_formula_in_program r v) >=> KPcompose a)

       | KPparallel cl cr l r => (substitution_dot_formula_in_program l v) >>= (fun a => (substitution_dot_formula_in_program r v) >=> KPparallel cl cr a)

       | KPloop p =>
         (substitution_dot_formula_in_program p v)
           >>= (fun a =>
                  (*on_test
                    (eassignables_disj (bound_vars_program a) (free_vars_formula v))*)
                    (ret (KPloop a)))

       | KPsend c t => ret (KPsend c t)
       | KPreceive c var => ret (KPreceive c var)
       | KPbroadcast c t var => ret (KPbroadcast c t var)

       | KPodeSystem ode f =>
         (*on_test
           (eassignables_disj (bound_vars_ode ode) (free_vars_formula v))*)
           ((substitution_dot_formula_in_formula f v)
              >=> KPodeSystem ode)
       end.


(***************************************************************************)
Definition find_function_in_uniform_substitution_entry
           (e : UniformSubstitutionEntry)
           (f : FunctionSymbol)
           (n : nat): option Term :=
  match e with
  | USE_function f' n' t =>
    if FunctionSymbol_dec f f' then
      if deq_nat n n' then Some t
      else None
    else None
  | _ => None
  end.



Definition find_predicate_in_uniform_substitution_entry
           (e : UniformSubstitutionEntry)
           (f : PredicateSymbol)
           (n : nat): option Formula :=
  match e with
  | USE_pred f' n' t =>
    if PredicateSymbol_dec f f' then
      if deq_nat n n' then Some t
      else None
    else None
  | _ => None
  end.


Definition find_quantifier_in_uniform_substitution_entry
           (e : UniformSubstitutionEntry)
           (f : QuantifierSymbol) : option Formula :=
  match e with
  | USE_quant f' t =>
    if QuantifierSymbol_dec f f'
    then Some t
    else None
  | _ => None
  end.

Definition find_const_in_uniform_substitution_entry
           (e : UniformSubstitutionEntry)
           (c : ProgramConstName) : option Program :=
  match e with
  | USE_constant c' t  =>
    if ProgramConstName_dec c c'
    then Some t
    else None
  | _ => None
  end.

Definition find_ode_in_uniform_substitution_entry
           (e : UniformSubstitutionEntry)
           (c : ODEConst) : option ODE :=
  match e with
  | USE_ode c' t  =>
    if ODEConst_dec c c'
    then Some t
    else None
  | _ => None
  end.

Fixpoint find_function_in_uniform_substitution
         (s : UniformSubstitution)
         (f : FunctionSymbol)
         (n : nat) : option Term :=
  match s with
  | [] => None
  | e :: entries =>
    match find_function_in_uniform_substitution_entry e f n with
    | Some t => Some t
    | None => find_function_in_uniform_substitution entries f n
    end
  end.



Fixpoint find_predicate_in_uniform_substitution
         (s : UniformSubstitution)
         (f : PredicateSymbol)
         (n : nat) : option Formula :=
  match s with
  | [] => None
  | e :: entries =>
    match find_predicate_in_uniform_substitution_entry e f n with
    | Some t => Some t
    | None => find_predicate_in_uniform_substitution entries f n
    end
  end.



Fixpoint find_quantifier_in_uniform_substitution
         (s : UniformSubstitution)
         (f : QuantifierSymbol) : option Formula :=
  match s with
  | [] => None
  | e :: entries =>
    match find_quantifier_in_uniform_substitution_entry e f with
    | Some t => Some t
    | None => find_quantifier_in_uniform_substitution entries f
    end
  end.


Fixpoint find_const_in_uniform_substitution
         (s : UniformSubstitution)
         (f : ProgramConstName) : option Program :=
  match s with
  | [] => None
  | e :: entries =>
    match find_const_in_uniform_substitution_entry e f with
    | Some t => Some t
    | None => find_const_in_uniform_substitution entries f
    end
  end.

Fixpoint find_ode_in_uniform_substitution
         (s : UniformSubstitution)
         (c : ODEConst) : option ODE :=
  match s with
  | [] => None
  | e :: entries =>
    match find_ode_in_uniform_substitution_entry e c with
    | Some t => Some t
    | None => find_ode_in_uniform_substitution entries c
    end
  end.

(***********************************************************************************)

Fixpoint vec_const_n {A} (n m : nat) (f : nat -> A) : Vector.t A n :=
  match n with
  | 0 => Vector.nil A
  | S k => Vector.cons A (f m) k (vec_const_n k (S m) f)
  end.

Definition vec_const {A} (n : nat) (f : nat -> A) : Vector.t A n :=
  vec_const_n n 0 f.

Definition lookup_func (s : UniformSubstitution) (f : FunctionSymbol) (n : nat) :=
  match find_function_in_uniform_substitution s f n with
  | Some t => t
  | None => KTfuncOf f n (vec_const n KTdot)
  end.

(** Uniform substitution rule for terms --- see Figure 1, Section 3 *)
Fixpoint uniform_substitution_term
         (t : Term)
         (sigma : UniformSubstitution) : option Term :=
  match t with
  | KTdot n => ret (KTdot n)

  | KTfuncOf f n args =>
    (vec_opt2opt_vec (Vector.map (fun a => uniform_substitution_term a sigma) args))
      (* TODO: replace dot(n) by the nth element of that vector *)
      (*(uniform_substitution_term theta sigma)*)
      >>=
      (substitution_dots_term (lookup_func sigma f n))

  | KTnumber r => ret (KTnumber r)

  | KTread  x => ret (KTread x)

  | KTneg l =>
    (uniform_substitution_term l sigma) >=> KTneg

  | KTplus l r =>
    (uniform_substitution_term l sigma)
      >>= (fun a => (uniform_substitution_term r sigma) >=> KTplus a)

  | KTminus l r =>
    (uniform_substitution_term l sigma)
      >>= (fun a => (uniform_substitution_term r sigma) >=> KTminus a)

  | KTtimes l r =>
    (uniform_substitution_term l sigma)
      >>= (fun a => (uniform_substitution_term r sigma) >=> KTtimes a)

  | KTdivide l r =>
    (uniform_substitution_term l sigma)
      >>= (fun a => (uniform_substitution_term r sigma) >=> KTdivide a)

  | KTpower l r =>
    (uniform_substitution_term l sigma)
      >>= (fun a => (uniform_substitution_term r sigma) >=> KTpower a)

  | KTdifferential theta =>
    on_test
      (U_admissible_term (EA_all []) theta sigma)
      ((uniform_substitution_term theta sigma)
         >=> KTdifferential)
  end.

Definition lookup_pred (s : UniformSubstitution) (p : PredicateSymbol) (n : nat) :=
  match find_predicate_in_uniform_substitution s p n with
  | Some f => f
  | None => KFpredOf p n (vec_const n KTdot)
  end.

Definition lookup_quant (s : UniformSubstitution) (C : QuantifierSymbol) :=
  match find_quantifier_in_uniform_substitution s C with
  | Some f => f
  | None => KFquantifier C KFdot
  end.

Definition lookup_const (s : UniformSubstitution) (a : ProgramConstName) :=
  match find_const_in_uniform_substitution s a with
  | Some p => p
  | None => KPconstant a
  end.

Definition lookup_ode (s : UniformSubstitution) (c : ODEConst) :=
  match find_ode_in_uniform_substitution s c with
  | Some p => p
  | None => ODEconst c
  end.

Definition uniform_substitution_atomic_ode
           (ode : AtomicODE)
           (s   : UniformSubstitution) : option ODE :=
  match ode with
  | ODEconst c => ret (lookup_ode s c) (* ret (ODEconst n) *)
  | ODEsing ds t =>
    (uniform_substitution_term t s)
      >=> (fun u => ODEatomic (ODEsing ds u))
  end.

Fixpoint uniform_substitution_ode
         (ode : ODE)
         (s   : UniformSubstitution) : option ODE :=
  match ode with
(*  | ODEem => ret ODEem*)
  | ODEatomic c => uniform_substitution_atomic_ode c s
  | ODEprod l r =>
    (uniform_substitution_ode l s)
      >>= (fun a => (uniform_substitution_ode r s)
                      >=> ODEprod a)
  end.

(** Uniform substitution rule for formulas --- see Figure 1, Section 3 *)
Fixpoint uniform_substitution_formula
         (fi : Formula)
         (sigma  : UniformSubstitution) : option Formula :=
  match fi with
  | KFdot => ret KFdot

  | KFtrue => ret KFtrue

  | KFfalse => ret KFfalse

  | KFgreaterEqual l r =>
    (uniform_substitution_term l sigma)
      >>= (fun a => (uniform_substitution_term r sigma) >=> KFgreaterEqual a)

  | KFgreater l r =>
    (uniform_substitution_term l sigma)
      >>= (fun a => (uniform_substitution_term r sigma) >=> KFgreater a)

  | KFlessEqual l r =>
    (uniform_substitution_term l sigma)
      >>= (fun a => (uniform_substitution_term r sigma) >=> KFlessEqual a)

  | KFless l r =>
    (uniform_substitution_term l sigma)
      >>= (fun a => (uniform_substitution_term r sigma) >=> KFless a)

  | KFequal l r =>
    (uniform_substitution_term l sigma)
      >>= (fun a => (uniform_substitution_term r sigma) >=>  KFequal a)

  | KFnotequal l r =>
    (uniform_substitution_term l sigma)
      >>= (fun a => (uniform_substitution_term r sigma) >=> KFnotequal a)

  | KFpredOf p n args =>
    (vec_opt2opt_vec (Vector.map (fun a => uniform_substitution_term a sigma) args))
      (*(uniform_substitution_term theta sigma)*)
      >>= (substitution_dots_term_in_formula (lookup_pred sigma p n))

  | KFquantifier C fi =>
    on_test
      (U_admissible_formula (EA_all []) fi sigma)
      ((uniform_substitution_formula fi sigma)
         >>= (substitution_dot_formula_in_formula (lookup_quant sigma C)))

  | KFnot l =>
    (uniform_substitution_formula l sigma) >=> KFnot

  | KFand l r =>
    (uniform_substitution_formula l sigma)
      >>= (fun a => (uniform_substitution_formula r sigma) >=> KFand a)

  | KFor l r =>
    (uniform_substitution_formula l sigma)
      >>= (fun a => (uniform_substitution_formula r sigma) >=> KFor a)

  | KFimply l r =>
    (uniform_substitution_formula l sigma)
      >>= (fun a => (uniform_substitution_formula r sigma) >=> KFimply a)

  | KFequiv l r =>
    (uniform_substitution_formula l sigma)
      >>= (fun a => (uniform_substitution_formula r sigma) >=> KFequiv a)

  | KFexistsVars vars F =>
    on_test (U_admissible_formula (vars2ext vars) F sigma)
            ((uniform_substitution_formula F sigma) >=> KFexistsVars vars)

  | KFforallVars vars F =>
    on_test (U_admissible_formula (vars2ext vars) F sigma)
            ((uniform_substitution_formula F sigma) >=> KFforallVars vars)

  | KFdiamond a F =>
    (uniform_substitution_program a sigma)
      >>= (fun p =>
              on_test (U_admissible_formula (bound_vars_program p) F sigma)
                      ((uniform_substitution_formula F sigma)
                         >=> KFdiamond p))

  | KFbox a F =>
    (uniform_substitution_program a sigma)
      >>= (fun p =>
              on_test (U_admissible_formula (bound_vars_program p) F sigma)
                      ((uniform_substitution_formula F sigma)
                         >=> KFbox p))

  | KFdifferentialFormula F => ret (KFdifferentialFormula F)
  end

(** Uniform substitution rule for hybrid programs --- see Figure 1, Section 3 *)
with uniform_substitution_program
       (p : Program)
       (sigma : UniformSubstitution ) : option Program :=
       match p with
       | KPconstant a => ret (lookup_const sigma a)

       | KPassign x theta =>
         (uniform_substitution_term theta sigma)
           >=> KPassign x

       | KPassignAny x => ret (KPassignAny x)

       | KPtest fi => (uniform_substitution_formula fi sigma) >=> KPtest

       | KPchoice a b =>
         (uniform_substitution_program a sigma)
           >>= (fun p => (uniform_substitution_program b sigma) >=> KPchoice p)

       | KPcompose a b =>
         (uniform_substitution_program a sigma)
           >>= (fun p =>
                  on_test (U_admissible_program (bound_vars_program p) b sigma)
                          ((uniform_substitution_program b sigma) >=> KPcompose p))

       | KPparallel ch1 ch2 p1 p2 => ret (KPparallel ch1 ch2 p1 p2)

       | KPloop p =>
         (uniform_substitution_program p sigma)
           >>= (fun a =>
                  on_test
                    (U_admissible_program (bound_vars_program a) p sigma)
                    (ret (KPloop a)))

       | KPsend ch e => ret (KPsend ch e)

       | KPreceive ch vs => ret (KPreceive ch vs)

       | KPbroadcast ch e vs => ret (KPbroadcast ch e vs)

       | KPodeSystem ode psi =>
         on_test
           (U_admissible_terms (bound_vars_ode ode) (ode2terms ode) sigma
            && U_admissible_formula (bound_vars_ode ode) psi sigma)
           ((uniform_substitution_formula psi sigma)
              >>= (fun F =>
                     (uniform_substitution_ode ode sigma)
                       >=> (fun O => KPodeSystem O F)))

         (*match ode with
         (*paper states admissible for theta, psi!!!*)
         | ODEsing xp theta =>
           on_test
             (U_admissible_term (VandD xp) theta sigma
              && U_admissible_formula (VandD xp) psi sigma)
             ((uniform_substitution_formula psi sigma)
                >>= (fun F =>
                       (uniform_substitution_term theta sigma)
                         >=> (fun t => KPodeSystem (ODEsing xp t) F)))

         |_ => ret (KPodeSystem ode psi)
         end*)
       end.
