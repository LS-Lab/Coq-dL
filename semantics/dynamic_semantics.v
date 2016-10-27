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
Require Export semantics_util.
Require Export terms_util.
Require Export deriv_util.
Require Export state.
Require Export free_vars_term.


(**

  This file implements dynamic semantics of Terms, Formulas and Programs.
  This file also introduces posreal definition, which we need for definition of
  dynamic semantics of programs. Posreal stand for positive real (i.e. returns
  all real numbers which are greater or equal than zero).
  This file is same as dynamic_semantics.v, except that this file works with
  functions with multiple arguments.

 *)


Definition term_assignables_nodup (t : Term) : list Assign :=
  remove_duplicates KAssignable_dec (free_vars_term t).


Definition KTnum2R (n : KTnum) : R :=
  match n with
  | KTNnat n => INR n
  | KTNreal r => r
  end.


(** Semantics of terms --- see Definition 4, Section 2.2 *)
Fixpoint dynamic_semantics_term
         (I : interpretation)
         (s : state)
         (t : Term) {struct t}
  : R
  :=
    match t with
    | KTdot n => I (SymbolDotTerm n)

    | KTfuncOf f n args =>
      interp_fun_f
        _
        (I (SymbolFunction f _))
        (Vector.map (dynamic_semantics_term I s) args)

    | KTnumber r => KTnum2R r

    | KTread x => s x

    | KTplus l r =>
      dynamic_semantics_term I s l + dynamic_semantics_term I s r

    | KTneg l =>
      - dynamic_semantics_term I s l

    | KTminus l r =>
      dynamic_semantics_term I s l - dynamic_semantics_term I s r

    | KTtimes l r =>
      dynamic_semantics_term I s l * dynamic_semantics_term I s r

    | KTdivide l r => R0

    | KTpower l r => R0

    (* Why do we only derive over variables and not over prime variables? *)
    | KTdifferential theta =>
      big_sum
        (term_assignables_nodup theta)
        (fun x : Assign =>
           (s (KD x)
            *
            Derive
              (fun X => dynamic_semantics_term I (upd_state s x X) theta)
              (s x))%R)
    end.

(* this definition is used in definition of dynamic semantics of programs *)
Inductive program_close (ps : ProgramSem) : state -> state -> Prop :=
| program_close_refl : forall v, program_close ps v v
| program_close_trans :
    forall v s w,
      program_close ps v s
      -> ps s w
      -> program_close ps v w.
Hint Constructors program_close.

Definition ODESemProp := R -> (R -> state) -> Prop.

Definition onA {T} (a : Assign) (f : Assign -> T) (d : T) :=
  match a with
  | KAssignDiff x => f x
  | _ => d
  end.

Definition dynamic_semantics_atomic_ode_fun
           (I : interpretation)
           (ode : AtomicODE) : ODESem :=
  match ode with
  | ODEconst c =>
    fun (s : state) (a : Assign) => interp_ode_dm (I (SymbolODE c)) s a
  | ODEsing ds theta =>
    fun (s : state) (a : Assign) =>
      if KAssignable_dec (KD ds) a
      then dynamic_semantics_term I s theta
      else R0
  end.

Fixpoint dynamic_semantics_ode_fun
         (I   : interpretation)
         (ode : ODE) : ODESem :=
  match ode with
(*  | ODEem => fun s a => R0*)
  | ODEatomic c => dynamic_semantics_atomic_ode_fun I c
  | ODEprod L R =>
    fun s a =>
      (dynamic_semantics_ode_fun I L s a
       + dynamic_semantics_ode_fun I R s a)%R
  end.

Definition atomic_ode_assign
           (I   : interpretation)
           (ode : AtomicODE) : list Assign :=
  match ode with
  | ODEconst c => interp_ode_bv (I (SymbolODE c))
  | ODEsing ds theta => [ds]
  end.

Fixpoint ode_assign
         (I   : interpretation)
         (ode : ODE) : list Assign :=
  match ode with
(*  | ODEem => []*)
  | ODEatomic c => atomic_ode_assign I c
  | ODEprod l r => ode_assign I l ++ ode_assign I r
  end.

Definition dynamic_semantics_ode
         (I   : interpretation)
         (ode : ODE)
         (r   : R)
         (phi : R -> state) : Prop :=
  forall (zeta : preal_upto r)
         (v : Assign)
         (i : List.In v (ode_assign I ode)),
    ex_derive_R (fun t => phi t v) zeta
    /\ phi zeta (KD v) = Derive (fun t => phi t v) zeta
    /\ dynamic_semantics_term I (phi zeta) (KD v)
       = dynamic_semantics_ode_fun I ode (phi zeta) (KD v).

Definition ode_footprint_vars
           (I   : interpretation)
           (ode : ODE) : list Assign :=
  ode_assign I ode.

Definition ode_footprint_diff
           (I   : interpretation)
           (ode : ODE) : list Assign :=
  map KD (ode_assign I ode).

Definition ode_footprint
           (I   : interpretation)
           (ode : ODE) : list Assign :=
  ode_footprint_vars I ode ++ ode_footprint_diff I ode.

Definition wf_ode (I : interpretation) (ode : ODE) : bool :=
  norepeatsb KAssignable_dec (ode_assign I ode).

(**
  A formula is well-formed if its ODEs have no repeats,
  and similarly for programs.
  This is in the context of an interpretation that provides the
  bound variables of a constant ODE.
 *)
Fixpoint wf_formula (I : interpretation) (F : Formula) : bool :=
  match F with
  | KFdot   => true
  | KFtrue  => true
  | KFfalse => true

  | KFgreaterEqual l r => true
  | KFgreater      l r => true
  | KFlessEqual    l r => true
  | KFless         l r => true
  | KFequal        l r => true
  | KFnotequal     l r => true

  | KFpredOf f n args => true

  | KFquantifier f a => wf_formula I a

  | KFnot   l   => wf_formula I l
  | KFand   l r => wf_formula I l && wf_formula I r
  | KFor    l r => wf_formula I l && wf_formula I r
  | KFimply l r => wf_formula I l && wf_formula I r
  | KFequiv l r => wf_formula I l && wf_formula I r

  | KFexistsVars vars F => wf_formula I F
  | KFforallVars vars F => wf_formula I F

  | KFdiamond P F => wf_program I P && wf_formula I F
  | KFbox     P F => wf_program I P && wf_formula I F

  | KFdifferentialFormula F => wf_formula I F
  end

with wf_program (I : interpretation) (P : Program) : bool :=
       match P with
       | KPconstant a => true

       | KPassign a theta => true

       | KPassignAny a => true

       | KPtest f => wf_formula I f

       | KPchoice  a b => wf_program I a && wf_program I b
       | KPcompose a b => wf_program I a && wf_program I b

       | KPloop p => wf_program I p

       | KPparallel ch1 ch2 p1 p2 => wf_program I p1 && wf_program I p2
       | KPsend ch e => true
       | KPreceive ch vs => true
       | KPbroadcast ch e vs => true

       | KPodeSystem ode F => wf_ode I ode && wf_formula I F
       end.

(** Semantics of formula --- see Definition 5, Section 2.2 *)
Fixpoint dynamic_semantics_formula
         (I  : interpretation)
         (fi : Formula)
  : FormulaSem
  :=
    match fi with
    | KFdot => I SymbolDotForm
    | KFtrue => TrueFormulaSem
    | KFfalse => FalseFormulaSem
    | KFgreaterEqual l r =>
      fun S =>
        Rge (dynamic_semantics_term I S l)
            (dynamic_semantics_term I S r)
    | KFgreater l r =>
      fun S =>
        Rgt (dynamic_semantics_term I S l)
            (dynamic_semantics_term I S r)
    | KFlessEqual l r =>
      fun S =>
        Rle (dynamic_semantics_term I S l)
            (dynamic_semantics_term I S r)
    | KFless l r =>
      fun S =>
        Rlt (dynamic_semantics_term I S l)
            (dynamic_semantics_term I S r)

    | KFequal l r =>
      fun S =>
        dynamic_semantics_term I S l
        = dynamic_semantics_term I S r

    | KFnotequal l r =>
      fun S =>
        dynamic_semantics_term I S l
        <> dynamic_semantics_term I S r

    | KFpredOf f n args =>
      fun S =>
        I (SymbolPredicate f n)
          (Vector.map (dynamic_semantics_term I S) args)

    | KFquantifier f a =>
      interp_quant_f
        (I (SymbolQuantifier f))
        (dynamic_semantics_formula I a)

    | KFnot l =>
        fun S => not (dynamic_semantics_formula I l S)
    | KFand l r =>
      fun S =>
        and (dynamic_semantics_formula I l S)
            (dynamic_semantics_formula I r S)
    | KFor l r =>
      fun S =>
        or (dynamic_semantics_formula I l S)
           (dynamic_semantics_formula I r S)
    | KFimply l r =>
      fun S =>
        dynamic_semantics_formula I l S
        -> dynamic_semantics_formula I r S
    | KFequiv l r =>
      fun S =>
        dynamic_semantics_formula I l S
        <-> dynamic_semantics_formula I r S
     | KFexistsVars vars F =>
      fun S =>
        exists rs,
          List.length rs = List.length vars
          /\ dynamic_semantics_formula I F (upd_list_state S (combine vars rs))

     | KFforallVars vars F =>
       fun S =>
         forall rs,
           List.length rs = List.length vars
           -> dynamic_semantics_formula I F (upd_list_state S (combine vars rs))

     | KFdiamond alpha F =>
       fun S =>
         exists w,
           dynamic_semantics_formula I F w
           /\ dynamic_semantics_program I alpha S w

     | KFbox alpha F =>
       fun S =>
         forall w,
           dynamic_semantics_program I alpha S w
           -> dynamic_semantics_formula I F w

     | KFdifferentialFormula F => FalseFormulaSem (* !!!!! *)
    end

(** Semantics of hybrid programs --- see Definition 6, Section 2.2 *)
with dynamic_semantics_program
         (I : interpretation)
         (p : Program)
     : ProgramSem :=
         match p with
         | KPconstant a => I (SymbolProgramConst a)

         | KPassign a theta =>
           fun v w => differ_state_except v w a (dynamic_semantics_term I v theta)

         | KPassignAny a => (*FalseProgramSem (* TODO *)*)
           fun v w => exists r, differ_state_except v w a r

         | KPtest fi => fun v w => v = w /\ dynamic_semantics_formula I fi v

         | KPchoice alpha beta =>
           fun v w =>
             dynamic_semantics_program I alpha v w
             \/
             dynamic_semantics_program I beta v w

         | KPcompose alpha beta =>
           fun v w =>
             exists s,
               dynamic_semantics_program I alpha v s
               /\ dynamic_semantics_program I beta s w

         | KPloop p =>
           fun v w => program_close (dynamic_semantics_program I p) v w

         | KPparallel ch1 ch2 p1 p2 => FalseProgramSem (* TODO *)
         | KPsend ch e => FalseProgramSem (* TODO *)
         | KPreceive ch vs => FalseProgramSem (* TODO *)
         | KPbroadcast ch e vs => FalseProgramSem (* TODO *)

         | KPodeSystem ode psi =>
           fun v w =>
             exists (r : preal),
             exists (phi : R -> state),
               equal_states_except v (phi R0) (ode_footprint_diff I ode) (*[KAssignDiff ds]*)
               /\ w = phi r (* Marcus, why did you leave that one out? *)
               /\ dynamic_semantics_ode I ode r phi
               /\ forall (zeta : preal_upto r),
                   dynamic_semantics_formula I psi (phi zeta)
                   /\ equal_states_except
                        (phi R0)
                        (phi zeta)
                        (ode_footprint I ode (* \cup ~write_set(ode) *)) (* later write_set(\alpha) *)

           (*
           match ode with
           | atomicODE ds t =>
             fun v w =>
               exists (r : preal),
               exists (phi : R -> state), (* [0,r] -> state *)
                 equal_states_except v (phi 0) [KAssignDiff ds]
                 (* -> dynamic_semantics_formula psi I w*)
                 (* TODO: make that equality more extensional *)
                 /\ w = phi r
                 /\
                 (forall (zeta : preal_upto r),
                     ex_derive_R (fun t => phi t (KAssignVar ds)) zeta
                     /\ phi zeta (KAssignDiff ds)
                        = Derive (fun t => phi t (KAssignVar ds)) zeta
                     /\ (* here we're supposed to build the differential equality
                           (x' = theta) from the (x' = theta and phi) *)
                     dynamic_semantics_term I (phi zeta) (KTread (KAssignDiff ds))
                     = dynamic_semantics_term I (phi zeta) t
                     /\ dynamic_semantics_formula I psi (phi zeta)
                     /\ equal_states_except (phi 0) (phi zeta) [KAssignDiff ds, KAssignVar ds]
                 )

           | _ => FalseProgramSem (* TOOD *)
           end*)

         end.


(** See Section 2.2 *)
Definition Df_formula_valid_in_I
           (F : Formula)
           (I : interpretation) :=
  forall v : state, dynamic_semantics_formula I F v.

(** See Section 2.2 *)
Definition Df_formula_valid (F : Formula) :=
  forall (I : interpretation), Df_formula_valid_in_I F I.


Lemma ode_footprint_diff_ODEsing :
  forall I ds t,
    ode_footprint_diff I (ODEsing ds t)
    = [KD ds].
Proof.
  introv.
  unfold ode_footprint_diff; simpl; auto.
Qed.
Hint Rewrite ode_footprint_diff_ODEsing : core.

Lemma ode_footprint_vars_ODEsing :
  forall I ds t,
    ode_footprint_vars I (ODEsing ds t)
    = [ds].
Proof.
  introv.
  unfold ode_footprint_vars; simpl; auto.
Qed.
Hint Rewrite ode_footprint_vars_ODEsing : core.

Lemma eqset_ode_footprint_prod :
  forall I ode1 ode2,
    eqset (ode_footprint I (ODEprod ode1 ode2))
          (ode_footprint I ode1 ++ ode_footprint I ode2).
Proof.
  repeat introv.
  unfold ode_footprint, ode_footprint_diff, ode_footprint_vars; simpl.
  allrw map_app.
  allrw in_app_iff.
  split; intro h; tcsp.
Qed.

Lemma eqset_ode_footprint_diff_prod :
  forall I ode1 ode2,
    eqset (ode_footprint_diff I (ODEprod ode1 ode2))
          (ode_footprint_diff I ode1 ++ ode_footprint_diff I ode2).
Proof.
  repeat introv.
  unfold ode_footprint_diff; simpl.
  allrw map_app.
  allrw in_app_iff.
  split; intro h; tcsp.
Qed.

Lemma dynamic_semantics_ode_comm :
  forall I ode1 ode2 r phi,
    dynamic_semantics_ode I (ODEprod ode1 ode2) r phi
    -> dynamic_semantics_ode I (ODEprod ode2 ode1) r phi.
Proof.
  introv sem i; simpl in i.
  pose proof (sem zeta v) as q; simpl in q.
  allrw in_app_iff; autodimp q hyp; tcsp.
  repnd; dands; auto; simpl in *.
  rewrite q.
  rewrite Rplus_comm; auto.
Qed.

(*
Lemma KAssignDiff_as_dvar :
  forall (ds : KDifferentialSymbol),
    KAssignDiff ds = DVar ds.
Proof.
  destruct ds; simpl; auto.
Qed.
Hint Rewrite KAssignDiff_as_dvar : core.
*)

Lemma dynamic_semantics_ode_system_1 :
  forall I ds t psi v w,
    dynamic_semantics_program I (KPodeSystem (ODEsing ds t) psi) v w
    <->
    exists (r : preal),
    exists (phi : R -> state), (* [0,r] -> state *)
      equal_states_except v (phi R0) [KD ds]
      (* -> dynamic_semantics_formula psi I w*)
      (* TODO: make that equality more extensional *)
      /\ w = phi r
      /\
      (forall (zeta : preal_upto r),
          ex_derive_R (fun t => phi t ds) zeta
          /\ phi zeta (KD ds) = Derive (fun t => phi t ds) zeta
          /\ (* here we're supposed to build the differential equality
                           (x' = theta) from the (x' = theta and phi) *)
          dynamic_semantics_term I (phi zeta) (KD ds)
          = dynamic_semantics_term I (phi zeta) t
          /\ dynamic_semantics_formula I psi (phi zeta)
          /\ equal_states_except (phi R0) (phi zeta) [KD ds, ds]).
Proof.
  introv; simpl.
  autorewrite with core.
  split; introv h; exrepnd; exists r phi; dands; auto; simpl in *.

  { introv; pose proof (h3 zeta ds) as q; repnd.
    autodimp q hyp; simpl in *;[tcsp|].
    dest_cases w; GC.
    repnd; dands; auto; pose proof (h1 zeta) as z; repnd; auto.
    introv i; apply z; simpl in *; intro xx; destruct i; repndors; tcsp. }

  { introv i; repndors; subst; tcsp; simpl in *.
    repndors; tcsp; subst.
    dest_cases w; GC.
    pose proof (h1 zeta) as q; repnd; dands; auto. }

  { introv; pose proof (h1 zeta) as q; repnd; dands; auto.
    introv i; apply q; simpl in *; intro xx; destruct i; repndors; tcsp. }
Qed.
