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

Require Export Coquelicot.Coquelicot.
Require Export US_lemmas.


(**

  This file implements soundness of US rule, ddl axioms and  proofs  rules,
  as well as differential equation axioms and differential axioms.

*)


Lemma program_close_trans_rev :
  forall (ps : ProgramSem) (v s w : state),
    ps v s
    -> program_close ps s w
    -> program_close ps v w.
Proof.
  introv h1 h2.
  induction h2; auto.
  { eapply program_close_trans;[|exact h1]; auto. }
  { autodimp IHh2 hyp.
    eapply program_close_trans;[exact IHh2|]; auto. }
Qed.

Lemma program_close_trans_imply_rev :
  forall (ps : ProgramSem) (v w : state),
    program_close ps v w
    ->
    (
      v = w
      \/
      exists s, ps v s /\ program_close ps s w
    ).
Proof.
  introv h; induction h; tcsp.
  repndors; exrepnd; subst; tcsp;
    right; eexists; dands; eauto.
Qed.


Definition bound_vars_term0 (theta : Term) : EAssignables := EA_assignables [].

(*

(* TOFIX? *)

(** This is an alternative definition of [bound_vars_term] that
    takes into account that uniform substitutions have to be closed
    on the operators occurring in differential terms to perform
    the substitution on such terms --- see Figure 1, Section 3 *)
Fixpoint bound_vars_term (t : Term) : EAssignables :=
  match t with
  | KTdot _           => EA_assignables []
  | KTfuncOf _ _ args => vec_flatten (Vector.map bound_vars_term args)
  | KTnumber _        => EA_assignables []
  | KTread _          => EA_assignables []
  | KTneg t           => bound_vars_term t
  | KTplus   t1 t2    => EAssignables_app (bound_vars_term t1) (bound_vars_term t2)
  | KTminus  t1 t2    => EAssignables_app (bound_vars_term t1) (bound_vars_term t2)
  | KTtimes  t1 t2    => EAssignables_app (bound_vars_term t1) (bound_vars_term t2)
  | KTdivide t1 t2    => EAssignables_app (bound_vars_term t1) (bound_vars_term t2)
  | KTpower  t1 t2    => EAssignables_app (bound_vars_term t1) (bound_vars_term t2)
  | KTdifferential _  => EA_all []
  end.

(** See Definition 10, Section 3 *)
Definition admissible_term
           (theta : Term)
           (sigma : UniformSubstitution) : bool :=
  U_admissible_term (bound_vars_term theta) theta  sigma.

(** See Definition 10, Section 3 *)
Definition admissible_formula
           (fi : Formula)
           (sigma : UniformSubstitution) : bool :=
  U_admissible_formula (bound_vars_formula fi) fi sigma.

(** See Definition 10, Section 3 *)
Definition admissible_program
           (pr : Program)
           (sigma : UniformSubstitution) : bool :=
  U_admissible_program (bound_vars_program pr) pr  sigma.

(* I don't think this is true *)
Lemma uniform_substitution_term_defined_if_admissible :
  forall t s,
    admissible_term t s = true
    -> {u : Term & uniform_substitution_term t s = Some u}.
Proof.
  term_ind t Case; introv adm;
    allrw fold_free_vars_sub_restrict_term;
    unfold admissible_term, U_admissible_term in adm;
    simpl in *; tcsp;
      try (complete (eexists; reflexivity)).

  { Case "KTfuncOf".
    pose proof (eassignables_subset_funcof s f t) as q.
    eapply eassignables_disj_subset in adm;[|exact q]; clear q.
    pose proof (IHt s adm) as h; exrepnd.
    rewrite h0; simpl.
    unfold lookup_func.
    remember (find_function_in_uniform_substitution s f) as ff;
      symmetry in Heqff; destruct ff; simpl;[|eexists; eauto].
Abort.

(* I don't think this is true *)
Lemma uniform_substitution_formula_defined_if_admissible :
  (forall f s,
      admissible_formula f s = true
      -> {g : Formula & uniform_substitution_formula f s = Some g})
  *
  (forall p s,
      admissible_program p s = true
      -> {g : Program & uniform_substitution_program p s = Some g}).
Proof.
  form_prog_rec Case; introv adm; simpl in *; tcsp;
    try (complete (eexists; reflexivity)).

  { Case "KFequal".
    dest_sub w; ginv.
Abort.
*)

(** A rule is the pair of a list of premisses and a conclusion,
  such that the premisses are supposed to imply the conclusion. *)
Record rule :=
  MkRule
    {
      premisses : list Formula;
      conclusion : Formula
    }.

Definition rule_true (r : rule) :=
  (forall f, List.In f (premisses r) -> Df_formula_valid f)
  -> Df_formula_valid (conclusion r).

Definition rule_locally_sound (r : rule) :=
  forall I,
    (forall f, List.In f (premisses r) -> Df_formula_valid_in_I f I)
    -> Df_formula_valid_in_I (conclusion r) I.

Lemma rule_locally_sound_implies_true :
  forall r, rule_locally_sound r -> rule_true r.
Proof.
  introv loc hyps; introv.
  apply loc; introv i.
  apply hyps; auto.
Qed.

Definition uniform_substitution_formula_opt_true
           (f : Formula)
           (s : UniformSubstitution) : Formula :=
  match uniform_substitution_formula f s with
  | Some g => g
  | None => KFtrue
  end.

Definition uniform_substitution_formula_opt_false
           (f : Formula)
           (s : UniformSubstitution) : Formula :=
  match uniform_substitution_formula f s with
  | Some g => g
  | None => KFfalse
  end.


(** Here we prove that the formula True (KFtrue) is valid *)
Lemma true_is_valid : Df_formula_valid KFtrue.
Proof.
  repeat introv; simpl; tcsp.
Qed.
Hint Immediate true_is_valid : core.

Definition const_vec (n : nat) (r : R) : Vector.t R n -> R := fun _ => r.

Lemma ex_partial_derive_st_func_sub_const_vec :
  forall (n : nat) (r : R), smooth_fun_T (const_vec n r).
Proof.
  introv d; introv cond.
  unfold const_vec.
  apply ex_partial_derive_st_l_pt_const.
Qed.

Definition interp_fun_const_n (n : nat) (r : R) : interpretation_function n :=
  MkInterpFun
    n
    (const_vec n r)
    (ex_partial_derive_st_func_sub_const_vec n r).

Definition DumODESem : ODESem := fun _ => DumState.

Lemma interpOdeExt_DumODESem : interpOdeExt [] DumODESem.
Proof.
  introv cond; introv; reflexivity.
Qed.

Definition dum_interpretation_ode : interpretation_ode :=
  MkInterpODE
    []
    DumODESem
    interpOdeExt_DumODESem.

Definition DumInterp : interpretation :=
  fun s =>
    match s with
    | SymbolFunction f n   => interp_fun_const_n n R0
    | SymbolDotTerm _      => R0
    | SymbolPredicate _ _  => fun _ => False
    | SymbolQuantifier _   => interp_quant_false
    | SymbolDotForm        => fun _ => False
    | SymbolODE _          => dum_interpretation_ode
    | SymbolProgramConst _ => FalseProgramSem
    end.

Lemma free_vars_sub_restrict_formula_subset_free_vars_uniform_substitution :
  forall s f,
    eassignables_subset
      (free_vars_sub_restrict_formula s f)
      (free_vars_uniform_substitution s) = true.
Proof.
  induction s; introv; simpl; auto.
  unfold free_vars_sub_restrict_formula; simpl.
  dest_cases w; simpl; auto.

  { apply eassignables_subset_app_left_right; auto.
    apply IHs. }

  { apply implies_eassignables_subset_app_r_true.
    right; apply IHs. }
Qed.


(** This proves that the formula False (KFfalse) is not valid *)
Lemma false_is_not_valid : ~ Df_formula_valid KFfalse.
Proof.
  introv h; simpl in h.
  pose proof (h DumInterp DumState) as q; clear h; simpl in q.
  inversion q.
Qed.


(** Uniform Substitution (US) rule --- see Theorem 10, Section 3.2 *)
Definition US_rule (f : Formula) (s : UniformSubstitution) : rule :=
  MkRule
    [f]
    (uniform_substitution_formula_opt_true f s).


(** Soundness of the uniform substitution rule --- see Theorem 11, Section 3.2 *)
Lemma US_sound :
  forall f s, rule_true (US_rule f s).
Proof.
  introv h; simpl in *.
  pose proof (h f) as q; clear h; autodimp q hyp.
  unfold uniform_substitution_formula_opt_true.
  dest_sub w; simpl;[|apply true_is_valid]; symmetry in Heqw.
  repeat introv.
  pose proof (us_lemma_formula f s I v) as h.
  unfold on_uniform_substitution_formula in h.
  rewrite Heqw in h.
  apply h; clear h.
  apply q.
Qed.

(* See Theorem 11 *)
Lemma US_sound_rule :
  forall (r : rule) (s : UniformSubstitution),
    free_vars_uniform_substitution s = EA_assignables []
    -> rule_locally_sound r
    -> rule_locally_sound
         (MkRule
            (map (fun f => uniform_substitution_formula_opt_false f s) (premisses r))
            (uniform_substitution_formula_opt_true (conclusion r) s)).
Proof.
  introv fvars loc hyps; simpl in *.
  unfold uniform_substitution_formula_opt_true.
  dest_sub w; simpl; symmetry in Heqw;[].
  introv.

  pose proof (us_lemma_formula (conclusion r) s I v) as h.
  unfold on_uniform_substitution_formula in h.
  rewrite Heqw in h.
  apply h; clear h.
  apply loc; clear loc.
  introv i.

  pose proof (hyps (uniform_substitution_formula_opt_false f0 s)) as q; clear hyps.
  rewrite in_map_iff in q.
  autodimp q hyp.
  { exists f0; dands; auto. }
  introv.
  pose proof (q v0) as h; clear q.
  unfold uniform_substitution_formula_opt_false in h.
  dest_sub z;[|inversion h];[]; symmetry in Heqz.

  pose proof (us_lemma_formula f0 s I v0) as q.
  unfold on_uniform_substitution_formula in q.
  rewrite Heqz in q; apply q in h; clear q.

  eapply substitution_adjoint_admissible_formula0;[|exact h].
  introv j.

  pose proof (free_vars_sub_restrict_formula_subset_free_vars_uniform_substitution s f0) as ss.
  eapply eassignables_subset_prop in ss;[|exact j].
  rewrite fvars in ss; simpl in ss; ginv.
Qed.


(** A few constants: *)
Definition varx    : KVariable           := variable "x".
Definition vary    : KVariable           := variable "y".
Definition vart    : KVariable           := variable "t".
Definition vars    : KVariable           := variable "s".

Definition predp   : PredicateSymbol     := predicate_symbol "p".
Definition predh   : PredicateSymbol     := predicate_symbol "h".
Definition predq   : PredicateSymbol     := predicate_symbol "q".
Definition predr   : PredicateSymbol     := predicate_symbol "r".
Definition consta  : ProgramConstName    := program_constant_name "a".
Definition constb  : ProgramConstName    := program_constant_name "b".
Definition funcf   : FunctionSymbol      := function_symbol "f".
Definition funcg   : FunctionSymbol      := function_symbol "g".
Definition funch   : FunctionSymbol      := function_symbol "h".
Definition funcfa  : FunctionSymbol      := function_symbol "fa".
Definition funcfb  : FunctionSymbol      := function_symbol "fb".

Definition assignx : KAssignable      := KAssignVar varx.
Definition assigny : KAssignable      := KAssignVar vary.
Definition assignt : KAssignable      := KAssignVar vart.
Definition assigns : KAssignable      := KAssignVar vars.
Definition assignxp: KAssignable      := KD assignx.
Definition assignyp: KAssignable      := KD assigny.
Definition pconsta : Program          := KPconstant consta.
Definition pconstb : Program          := KPconstant constb.
Definition tvarx   : Term             := KTread assignx.
Definition tvary   : Term             := KTread assigny.
Definition tvart   : Term             := KTread assignt.
Definition tvars   : Term             := KTread assigns.
Definition tvarxp  : Term             := KTread assignxp.

Definition term0   : Term             := 0.
Definition DumT    : Term             := 0.

Definition odec    : ODEConst         := ode_constant "c".
Definition oconstc : ODEConst         := ode_constant "c".

Definition DumT1   : Vector.t Term 1  := Vector.cons Term DumT 0 (Vector.nil Term).
Definition VT0     : Vector.t Term 0  := Vector.nil Term.

(* It would be better if we had 0-ary functions/predicates because
   we wouldn't need to have arguments here *)
Definition fpredp  : Formula          := KFpredOf predp 0 VT0.
Definition fpredq  : Formula          := KFpredOf predq 0 VT0.
Definition tfuncf  : Term             := KTfuncOf funcf 0 VT0.

Definition VT1 (t : Term) : Vector.t Term 1 := Vector.cons _ t _ (Vector.nil _).

Definition VT2 (t u : Term) : Vector.t Term 2 :=
  Vector.cons _ t _ (Vector.cons _ u _ (Vector.nil _)).

Definition VR1 (r : R) : Vector.t R 1 := Vector.cons R r 0 (Vector.nil R).

Definition Pof1 (ps : PredicateSymbol) (t : Term)   : Formula := KFpredOf ps 1 (VT1 t).
Definition Pof2 (ps : PredicateSymbol) (t u : Term) : Formula := KFpredOf ps 2 (VT2 t u).

Definition Fof1 (fs : FunctionSymbol) (t : Term)   : Term := KTfuncOf fs 1 (VT1 t).
Definition Fof2 (fs : FunctionSymbol) (t u : Term) : Term := KTfuncOf fs 2 (VT2 t u).

Definition PofN (ps : PredicateSymbol) {n} (v : Vector.t Term n) : Formula := KFpredOf ps n v.
Definition FofN (fs : FunctionSymbol)  {n} (v : Vector.t Term n) : Term    := KTfuncOf fs n v.


Definition strN (s : String.string) (n : nat) : String.string :=
  String.append s (String.String (Ascii.ascii_of_nat n) String.EmptyString).

Definition varN (v : KVariable) (n : nat) : KVariable :=
  match v with
  | variable s => variable (strN s n)
  end.

(* makes a vector of [n] different variables *)
Definition VVN (v : KVariable) (n : nat) : Vector.t KVariable n :=
  vec_const n (varN v).

Definition varn2t v n : Term := KTread (KAssignVar (varN v n)).
Definition var2t v : Term := KTread (KAssignVar v).

(* makes a vector of [n] different variables as terms *)
Definition VTN (v : KVariable) (n : nat) : Vector.t Term n :=
  vec_const n (fun n => varn2t v n).

(* ps(v1,...,vn) *)
Definition PofVN (ps : PredicateSymbol) (v : KVariable) (n : nat) : Formula := PofN ps (VTN v n).

(* fs(v1,...,vn) *)
Definition FofVN (fs : FunctionSymbol)  (v : KVariable) (n : nat) : Term    := FofN fs (VTN v n).


Lemma fold_VT1 : forall t, Vector.cons _ t _ (Vector.nil _) = VT1 t.
Proof. auto. Qed.

Lemma fold_VR1 : forall t, Vector.cons _ t _ (Vector.nil _) = VR1 t.
Proof. auto. Qed.

Lemma fold_VT2 :
  forall t u, Vector.cons _ t _ (Vector.cons _ u _ (Vector.nil _)) = VT2 t u.
Proof. auto. Qed.



Definition varv    : KVariable           := variable "v".
Definition assignv : KAssignable         := KAssignVar varv.
Definition termv   : Term                := KTread assignv.

Definition funcA   : FunctionSymbol      := function_symbol "A".
Definition termA   : Term                := KTfuncOf funcA 0 VT0.

Definition oded    : ODEConst         := ode_constant "d".
Definition oconstd : ODEConst         := ode_constant "d".

Definition qsP : QuantifierSymbol := quantifier_symbol "P".
Definition qsQ : QuantifierSymbol := quantifier_symbol "Q".
Definition qsC : QuantifierSymbol := quantifier_symbol "C".

Definition quantP : Formula := KFquantifier qsP KFtrue.
Definition quantQ : Formula := KFquantifier qsQ KFtrue.
Definition quantC : Formula := KFquantifier qsC KFtrue.

Definition qP (f : Formula) : Formula := KFquantifier qsP f.
Definition qQ (f : Formula) : Formula := KFquantifier qsQ f.
Definition qC (f : Formula) : Formula := KFquantifier qsC f.


Lemma PofVN2_eq :
  forall p v, PofVN p v 2 = Pof2 p (varn2t v 0) (varn2t v 1).
Proof.
  auto.
Qed.

Lemma PofVN2_eq_varn :
  forall p v, PofVN p v 2 = Pof2 p (var2t (varN v 0)) (var2t (varN v 1)).
Proof.
  auto.
Qed.

Lemma PofVN1_eq :
  forall p v, PofVN p v 1 = Pof1 p (varn2t v 0).
Proof.
  auto.
Qed.

Lemma PofVN1_eq_varn :
  forall p v, PofVN p v 1 = Pof1 p (var2t (varN v 0)).
Proof.
  auto.
Qed.


Lemma ex_partial_derive_st_func_sub_ex_derive1 :
  forall F pt,
    smooth_fun_T F
    -> ex_derive (fun t : R => F (VR1 t)) pt.
Proof.
  introv cond.
  pose proof (cond
                nat
                0
                (Vector.cons _ 0 _ (Vector.nil _))
                (fun s n => s assignx)
                assignx
                []) as q; simpl in q.
  autodimp q hyp.

  { introv i ss; clear i.
    apply sublist_cons_r in ss; repndors; ginv; exrepnd; ginv;
      try (complete (apply sublist_nil_r in ss; ginv)).
    apply sublist_nil_r in ss0; subst.
    unfold ex_partial_derive; simpl; introv.
    eapply ex_derive_ext;[intro;symmetry;autorewrite with core;reflexivity|].
    apply ex_derive_id. }

  { pose proof (q pt DumState) as h; clear q; simpl in h.
    eapply ex_derive_ext;[|exact h]; clear h.
    simpl; introv.
    autorewrite with core; auto. }
Qed.
Hint Resolve ex_partial_derive_st_func_sub_ex_derive1 : core.



Definition qsH  : QuantifierSymbol := quantifier_symbol "H".
Definition qsP1 : QuantifierSymbol := quantifier_symbol "P1".
Definition qsP2 : QuantifierSymbol := quantifier_symbol "P2".
Definition qsQ1 : QuantifierSymbol := quantifier_symbol "Q1".
Definition qsQ2 : QuantifierSymbol := quantifier_symbol "Q2".

Definition quantH  : Formula := KFquantifier qsH  KFtrue.
Definition quantP1 : Formula := KFquantifier qsP1 KFtrue.
Definition quantP2 : Formula := KFquantifier qsP2 KFtrue.
Definition quantQ1 : Formula := KFquantifier qsQ1 KFtrue.
Definition quantQ2 : Formula := KFquantifier qsQ2 KFtrue.
