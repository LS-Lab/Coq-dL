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


Require Export list_util.
Require Export vec_util.
Require Export reals_util.
Require Export symbol_lemmas.
Require Export Derive.
Require Export deriv_util.
Require Export state.


(**

  This file contains some lemmas about smooth functions with multiple arguments.
  Beside that, this file introduces definitions for semantics of Terms, Formulas and
  Programs, as well as definition of interpretation.
  This file works with functions with multiple arguments

*)


(** definition of symbols which works with functions with multiple arguments *)
Inductive Symbol :=
(* terms *)
| SymbolFunction (f : FunctionSymbol) (n : nat) : Symbol
| SymbolDotTerm (n : nat) : Symbol

(* formulas *)
| SymbolPredicate (f : PredicateSymbol) (n : nat) : Symbol
| SymbolQuantifier (f : QuantifierSymbol) : Symbol
| SymbolDotForm : Symbol

(* ODEs *)
(* provides the bound variables & dynamic semantics of ODE constants *)
| SymbolODE (c : ODEConst) : Symbol

(* programs *)
| SymbolProgramConst (a : ProgramConstName) : Symbol.

(*
Record listn (T : Type) (n : nat) :=
  mk_listn
  {
    listn_l : list T;
    listn_cond : Datatypes.length listn_l = n
  }.
*)

(** function is n derivable if it's n derivable in every point *)
Definition ex_derive_all_n (f : R -> R) :=
  forall n pt, ex_derive_n f n pt.

(** partial derivative of variables in state (st stands for state here) *)
Fixpoint partial_derive
         (f : state -> R)
         (l : list Assign)
  : state -> R
  :=
    match l with
    | [] => f
    | v :: l =>
      fun (st : state) =>
        Derive
          (fun X : R =>
             partial_derive
               f
               l
               (upd_state st v X))
          (st v)
    end.

Require Export FunctionalExtensionality.

Lemma upd_state_var_ext :
  forall s v,
    upd_state_var s v (s (KAssignVar v)) = s.
Proof.
  introv.
  apply functional_extensionality; introv.
  unfold upd_state_var, upd_state; dest_cases w.
Qed.

Lemma upd_state_ext :
  forall s v,
    upd_state s v (s v) = s.
Proof.
  introv.
  apply functional_extensionality; introv.
  unfold upd_state_var, upd_state; dest_cases w.
Qed.

Lemma upd_state_var_twice :
  forall s v z w,
    upd_state_var (upd_state_var s v z) v w
    = upd_state_var s v w.
Proof.
  introv.
  apply functional_extensionality; introv.
  unfold upd_state_var, upd_state.
  dest_cases w.
Qed.
Hint Rewrite upd_state_var_twice.

Lemma upd_state_twice :
  forall s v z w,
    upd_state (upd_state s v z) v w
    = upd_state s v w.
Proof.
  introv.
  apply functional_extensionality; introv.
  unfold upd_state.
  dest_cases w.
Qed.
Hint Rewrite upd_state_twice.

Lemma partial_derive_st_as_Derive_n :
  forall (l : list Assign) f v s,
    (forall x, List.In x l -> x = v)
    -> partial_derive f l s
       = Derive_n
           (fun r => f (upd_state s v r))
           (List.length l)
           (s v).
Proof.
  induction l; introv imp; simpl in *.
  { rewrite upd_state_ext; auto. }
  { dLin_hyp h; subst.
    apply Derive_ext; introv.
    rewrite (IHl f v); auto.
    autorewrite with core.
    apply Derive_n_ext; introv.
    autorewrite with core; auto. }
Qed.

Definition ex_partial_derive_st_l
           (f  : state -> R)
           (st : state)
           (l  : list Assign)
           (v  : Assign) :=
  ex_derive_R
    (fun X => partial_derive f l (upd_state st v X))
    (st v).

(** This says that the (n+1)th partial derivative of f exists *)
Definition ex_nth_partial_derive_st (n : nat) (f : state -> R) :=
  forall (st : state) (l : list Assign) (v : Assign),
    List.length l = n
    -> ex_partial_derive_st_l f st l v.

Definition ex_all_partial_derive_st (f : state -> R) :=
  forall n, ex_nth_partial_derive_st n f.

Lemma partial_derive_st_ext :
  forall f g l st,
    (forall s, f s = g s)
    -> partial_derive f l st
       = partial_derive g l st.
Proof.
  induction l; introv imp; simpl; auto.
  apply Derive_ext; introv.
  apply IHl; auto.
Qed.

Lemma ex_all_partial_derive_st_ext :
  forall F G,
    (forall s, F s = G s)
    -> ex_all_partial_derive_st F
    -> ex_all_partial_derive_st G.
Proof.
  introv imp d len; simpl.
  eapply ex_derive_ext;[|apply (d n);exact len].
  simpl; introv.
  apply partial_derive_st_ext; auto.
Qed.

(*
Definition partial_derive_st_upd :
  forall f l s s',
    partial_derive f l s
    = partial_derive (fun s' => f (upd_state_st s s' l)) l s'.
Proof.
  induction l; introv; simpl; autorewrite with core; auto.
Abort.*)

Definition ex_partial_derive
           (f : state -> R)
           (v : Assign)
           (l : list Assign) : Prop :=
  forall pt s,
    ex_derive_R
      (fun X =>
         partial_derive
           f
           l
           (upd_state s v X))
      pt.

(** This is a variant of [ex_all_partial_derive_st] where the point can be anything.
    We prove below in [ex_partial_derive_st_pt_eq_all] that both
    definitions are equivalent.
 *)
Definition ex_partial_derive_st_pt (f : state -> R) : Prop :=
  forall v l, ex_partial_derive f v l.

Lemma ex_partial_derive_st_pt_eq_all :
  forall (f : state -> R),
    ex_partial_derive_st_pt f <-> ex_all_partial_derive_st f.
Proof.
  introv; split; intro h.

  { introv len; subst.
    unfold ex_partial_derive_st_l; simpl; apply h. }

  { repeat introv; simpl in *.
    pose proof (h (List.length l) (upd_state s v pt) l v eq_refl) as h.
    unfold ex_partial_derive_st_l in h; simpl in h.
    autorewrite with core in h.
    eapply ex_derive_ext;[|exact h]; clear h; simpl; introv.
    autorewrite with core; auto. }
Qed.

Definition Vector := Vector.t.

(*

   This is essentially stating that [f] is smooth.
   It derives [f]'s arguments through the interpretation function [G].

   Does that even make sense?

   Try to prove [ex_derive_func 2 plus_vector],
   where plus_vector is defined from Rplus.
   (see below)

   T is really Term, but what do we really care what the type is?

 *)
Definition ex_partial_derive_st_func {m : nat} (f : Vector R m -> R) :=
  forall (T  : Type)
         (d  : T) (* forall non-empty T *)
         (ts : Vector T m)
         (G  : state -> T -> R),
    (forall t, Vector.In t ts -> ex_all_partial_derive_st (fun s => G s t))
    -> ex_all_partial_derive_st (fun s => f (Vector.map (G s) ts)).

(*

  Here's a slightly stronger version where the arguments have to only be
  derivable on sublists.

  We show below in [smooth_fun_T_eq] that it is equivalent
  to the vectorial version [smooth_fun]

 *)
Definition smooth_fun_T {m : nat} (f : Vector R m -> R) :=
  forall (T  : Type)
         (d  : T) (* forall non-empty T *)
         (ts : Vector T m)
         (G  : state -> T -> R)
         (v  : Assign)
         (l  : list Assign),
    (forall t w l',
        Vector.In t ts
        -> sublist (w :: l') (v :: l)
        -> ex_partial_derive (fun s => G s t) w l')
    -> ex_partial_derive (fun s => f (Vector.map (G s) ts)) v l.

(*
   A stronger variant of ex_partial_derive_st_func.
   Here we ask for the arguments to be derivable on the same
   states and variables.
   Is that enough?  Probably not because I can't prove it for plus in
   dynamic_semantics_prop.v! (Lemma ex_partial_derive_st_func_l_plus_vector)
 *)
Definition ex_partial_derive_st_func_l {m : nat} (f : Vector R m -> R) :=
  forall (T  : Type)
         (d  : T) (* forall non-empty T *)
         (ts : Vector T m)
         (G  : state -> T -> R)
         (st : state)
         (l  : list Assign)
         (v  : Assign),
    (forall t, Vector.In t ts -> ex_partial_derive_st_l (fun s => G s t) st l v)
    -> ex_partial_derive_st_l (fun s => f (Vector.map (G s) ts)) st l v.


Definition revApp {A B} (s : A) (f : A -> B) : B := f s.

(*

  This is an alternative definition of ex_partial_derive_st_func
  that is not parametrized over a non-empty type and an interpretation-like
  function (the G in ex_partial_derive_st_func)
  but instead directly provides a vector of interpretations.
  We show below in ex_partial_derive_vec_st_func_eq that the two definitions
  are equivalent (obviously! :P).

 *)
Definition ex_partial_derive_vec_st_func {m : nat} (f : Vector R m -> R) :=
  forall (Is : Vector (state -> R) m),
    (forall i, Vector.In i Is -> ex_all_partial_derive_st i)
    -> ex_all_partial_derive_st (fun s => f (Vector.map (revApp s) Is)).

Definition smooth_fun {m : nat} (f : Vector.t R m -> R) :=
  forall (Is : Vector.t (state -> R) m) (v : Assign) (l : list Assign),
    (forall i w l',
        Vector.In i Is
        -> sublist (w :: l') (v :: l)
        -> ex_partial_derive i w l')
    -> ex_partial_derive (fun s => f (Vector.map (revApp s) Is)) v l.

Lemma ex_partial_derive_vec_st_func_eq :
  forall {m} (f : Vector.t R m -> R),
    ex_partial_derive_vec_st_func f <-> ex_partial_derive_st_func f.
Proof.
  introv; split; introv exd.

  { introv d cond.
    unfold ex_partial_derive_vec_st_func in exd.

    pose proof (exd (Vector.map (fun a s => G s a) ts)) as q; clear exd.
    autodimp q hyp.
    { introv j; apply in_vec_map in j; exrepnd; subst; auto. }
    eapply ex_all_partial_derive_st_ext in q;
      [|introv;rewrite vec_map_map; unfold compose; reflexivity].
    auto.
  }

  { introv cond.
    unfold ex_partial_derive_st_func in exd.
    apply (exd (state -> R) (fun _ => 0) Is (fun s i => i s)); auto.
  }
Qed.

Lemma ex_partial_derive_ext :
  forall f g v l,
    (forall s, f s = g s)
    -> ex_partial_derive f v l
    -> ex_partial_derive g v l.
Proof.
  introv e pd; introv; simpl in *.
  eapply ex_derive_ext;[|apply pd]; simpl; introv.
  apply partial_derive_st_ext; auto.
Qed.

Lemma smooth_fun_T_eq :
  forall {m} (f : Vector.t R m -> R),
    smooth_fun f <-> smooth_fun_T f.
Proof.
  introv; split; introv exd.

  { introv d cond; introv; simpl in *.

    pose proof (exd (Vector.map (fun a s => G s a) ts) v l) as q; clear exd.
    autodimp q hyp.
    { introv j; apply in_vec_map in j; exrepnd; subst; auto. }
    eapply ex_derive_ext;[|apply (q pt s)]; simpl; introv; clear q.
    apply partial_derive_st_ext; introv.
    rewrite vec_map_map; unfold compose; auto.
  }

  { introv cond; introv; simpl in *.
    apply (exd (state -> R) (fun _ => 0) Is (fun s i => i s)); auto.
  }
Qed.

Definition plus_vector : Vector.t R 2%nat -> R :=
  fun v : Vector.t R 2%nat =>
    match v with
    | Vector.cons x 1 (Vector.cons y 0 Vector.nil) => Rplus x y
    | _ => R0
    end.

(* see ex_partial_derive_st_func_test_plus in dynamic_semantics_props, which is proved *)
Lemma ex_partial_derive_st_func_test : ex_partial_derive_st_func plus_vector.
Proof.
  introv d; introv.
  unfold plus_vector; simpl.
  apply (Vector.caseS' ts).
  introv; simpl.
  apply (Vector.caseS' t).
  introv; simpl.

  clear ts t.
  apply (@Vector.case0
                T
                (fun t0 =>
                   (forall t : T,
                       Vector.In t (Vector.cons T h 1 (Vector.cons T h0 0 t0)) ->
                       ex_all_partial_derive_st (fun s : state => G s t)) ->
                   ex_all_partial_derive_st
                     (fun s : state =>
                        match Vector.map (G s) t0 return R with
                        | @Vector.nil _ => G s h + G s h0
                        | @Vector.cons _ _ _ _ => 0
                        end))).
  simpl.
  clear t0.
  introv ih.
  rename h into x.
  rename h0 into y.

  pose proof (ih x) as h1.
  pose proof (ih y) as h2.
  clear ih.
  autodimp h1 hyp;[constructor|].
  autodimp h2 hyp;[repeat constructor|].

(*
  unfold ex_partial_derive_st in *.
  unfold ex_nth_partial_derive_st in *.
  introv H1.
  unfold ex_derive_R in *.
  unfold ex_derive in *.
  (* I need instance of type T (I can not rewrite, apply of pose proof)*)
 *)
Abort.

(** interpretation of function with multiple arguments *)
Record interpretation_function (n : nat) :=
  MkInterpFun
    {
      interp_fun_f : Vector.t R n -> R;
      interp_fun_cond : smooth_fun_T interp_fun_f
    }.

(** definition of semantics for Terms *)
Definition TermSem := state -> R.

(** definition of semantics for Formulas *)
Definition FormulaSem := state -> Prop.

(** definition of semantics for Formulas which return False and True, respectively *)
Definition FalseFormulaSem : FormulaSem := fun _ => False.
Definition TrueFormulaSem  : FormulaSem := fun _ => True.

(** definition of semantics for Programs **)
Definition ProgramSem := state -> state -> Prop.

(** definition of semantics for Programs which return False and True, respectively *)
Definition FalseProgramSem : ProgramSem := fun _ _ => False.
Definition TrueProgramSem  : ProgramSem := fun _ _ => True.

(** definition of semantics for Differential Programs *)
Definition ODESem := state -> state.
(*Definition ODESem := R -> (R -> state) -> Prop.*)
(*Definition ODEConstSem := state -> state.*)
(*Definition ODEConstSem := (R -> state) -> R -> state.*)
(* Could we do that instead:

Definition ODESem := forall r : R, (preal_upto r -> state) -> Prop.
Definition ODEConstSem := forall (r : R), (preal_upto r -> state) -> preal_upto r -> state.*)


(*
  [R -> state] is a stateflow.
  Do we have to limit the stateflow in time?  Right now we do with the argument [R].
 *)

Definition interpQuantExt (F : FormulaSem -> FormulaSem) :=
  forall f g v w,
    (forall a, v a = w a)
    -> (forall s, f s <-> g s)
    -> (F f v <-> F g w).

(** interpretation of quantifier *)
Record interpretation_quantifier :=
  MkInterpQuant
    {
      interp_quant_f : FormulaSem -> FormulaSem;
      interp_quant_ext : interpQuantExt interp_quant_f
    }.

Definition interpOdeExt (l : list Assign) (F : ODESem) :=
  forall (v w : state) a,
    (forall a, v a = w a)
    -> F v a = F w a.

Record interpretation_ode :=
  MkInterpODE
    {
      interp_ode_bv   : list Assign;
      interp_ode_dm   : ODESem;
      interp_ode_cond : interpOdeExt interp_ode_bv interp_ode_dm
    }.

(** definition of interpretation *)
Definition interpretation :=
  forall f : Symbol,
    match f return Type with
    | SymbolFunction _ n => interpretation_function n
    | SymbolDotTerm n => R

    | SymbolPredicate _  n => Vector.t R n -> Prop
    | SymbolQuantifier _ => interpretation_quantifier
    | SymbolDotForm => FormulaSem

    | SymbolODE _ => interpretation_ode

    | SymbolProgramConst _ => ProgramSem
    end.

Ltac constant_derivable :=
  let eps := fresh "eps" in
  let h   := fresh "h" in
  let d   := fresh "d" in
  let q   := fresh "q" in
  let z   := fresh "z" in
  try (unfold derivable_pt, derivable_pt_abs, derivable_pt_lim);
    autorewrite with core;
    exists R0;
    intros eps h;
    exists R1pos;
    intros d q z;
    autorewrite with core;
    rewrite zero_div_is_zero; auto;
    rewrite Rabs_R0; auto.

Lemma deriv_constant :
  forall c, derivable (fun X => c).
Proof.
  intros c; intros x.
  reg.
Qed.

Lemma ex_all_partial_derive_st_implies_l_pt :
  forall (f : state -> R) v l,
    ex_all_partial_derive_st f
    -> ex_partial_derive f v l.
Proof.
  introv h; introv; simpl in *.
  apply ex_partial_derive_st_pt_eq_all in h.
  apply h.
Qed.
