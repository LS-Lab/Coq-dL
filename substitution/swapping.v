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

Require Export soundness.


(**

   This file implements renaming of variables using swapping.

   More might be able to reuse some stuff from here:
     - https://github.com/vrahli/NuprlInCoq/blob/master/terms/swap.v
     - https://github.com/vrahli/NuprlInCoq/blob/master/terms/swap_props.v
 *)

Record swapping :=
  MkSwapping
    {
      swap_left : KVariable;
      swap_right : KVariable
    }.


(**

   swapping operation on variables
   [swap a b v] applies the swapping (a,b) to the assignable v.

 *)
Definition swap (sw : swapping) (v : KVariable) : KVariable :=
  if KVariable_dec v (swap_left sw) then swap_right sw
  else if KVariable_dec v (swap_right sw) then swap_left sw
       else v.

(**

  [swap_assgn] generalizes [swap] to assignables.

 *)

Fixpoint swap_assgn (sw : swapping) (a : Assign) : Assign :=
  match a with
  | KAssignVar v => KAssignVar (swap sw v)
  | KAssignDiff d => KAssignDiff (swap_assgn sw d)
  end.


(**

  [swap_vars] generalizes [swap] to a list of variables.

 *)

Definition swap_vars (sw : swapping) (l : list Var) : list Var :=
  map (swap sw) l.


(**

  [swap_assgns] generalizes [swap_assgn] to a list of variables.

 *)

Definition swap_assgns (sw : swapping) (l : list Assign) : list Assign :=
  map (swap_assgn sw) l.


(**

  Swapping on terms: it applies the swapping (a,b) to term [t]

 *)
Fixpoint swap_term (sw : swapping) (t : Term) : Term :=
  match t with
  | KTdot n            => KTdot n
  | KTfuncOf f n args  => KTfuncOf f n (Vector.map (swap_term sw) args)
  | KTnumber r         => KTnumber r
  | KTread asgn        => KTread (swap_assgn sw asgn)
  | KTneg t            => KTneg    (swap_term sw t)
  | KTplus   l r       => KTplus   (swap_term sw l) (swap_term sw r)
  | KTminus  l r       => KTminus  (swap_term sw l) (swap_term sw r)
  | KTtimes  l r       => KTtimes  (swap_term sw l) (swap_term sw r)
  | KTdifferential t   => KTdifferential (swap_term sw t)
  end.


(**

 Swaping on AtomicODE

 *)
Definition swap_atomic_ode (sw : swapping) (o : AtomicODE) : AtomicODE :=
  match o with
  | ODEconst c   => ODEconst c (* undefined in Rose's implementation *)
  | ODEsing xp t => ODEsing  (swap_assgn sw xp) (swap_term sw t)
  end.

(**

 Swaping on ODE

 *)
Fixpoint swap_ode (sw : swapping) (o : ODE) : ODE :=
  match o with
  | ODEatomic c => ODEatomic (swap_atomic_ode sw c)
  | ODEprod l r => ODEprod (swap_ode sw l) (swap_ode sw r)
  end.


(**

 Swaping on Formulas

 *)
Fixpoint swap_formula  (sw : swapping) (F : Formula) : Formula :=
  match F with
  | KFdot                   => KFdot
  | KFtrue                  => KFtrue
  | KFfalse                 => KFfalse

  | KFequal        l r      => KFequal        (swap_term sw l) (swap_term sw r)
  | KFnotequal     l r      => KFnotequal     (swap_term sw l) (swap_term sw r)
  | KFgreaterEqual l r      => KFgreaterEqual (swap_term sw l) (swap_term sw r)
  | KFgreater      l r      => KFgreater      (swap_term sw l) (swap_term sw r)
  | KFlessEqual    l r      => KFlessEqual    (swap_term sw l) (swap_term sw r)
  | KFless         l r      => KFless         (swap_term sw l) (swap_term sw r)

  | KFpredOf p n args       => KFpredOf p n (Vector.map (swap_term sw) args)

  | KFquantifier q t        => KFquantifier q (swap_formula sw t)

  | KFnot   f               => KFnot   (swap_formula sw f)
  | KFand   l r             => KFand   (swap_formula sw l) (swap_formula sw r)
  | KFor    l r             => KFor    (swap_formula sw l) (swap_formula sw r)
  | KFimply l r             => KFimply (swap_formula sw l) (swap_formula sw r)
  | KFequiv l r             => KFequiv (swap_formula sw l) (swap_formula sw r)

  | KFforallVars lv f       => KFforallVars (swap_vars sw lv) (swap_formula sw f)
  | KFexistsVars lv f       => KFexistsVars (swap_vars sw lv) (swap_formula sw f)

  | KFbox     p f           => KFbox     (swap_program sw p) (swap_formula sw f)
  | KFdiamond p f           => KFdiamond (swap_program sw p) (swap_formula sw f)
  end

(**

 Swaping on Programs

 *)
  with swap_program  (sw : swapping) (P : Program) : Program :=
         match P with
         | KPconstant c           => KPconstant c
         | KPassign x t           => KPassign (swap_assgn sw x) (swap_term sw t)
         | KPassignAny x          => KPassignAny (swap_assgn sw x)
         | KPtest f               => KPtest (swap_formula sw f)

         | KPchoice l r           => KPchoice (swap_program sw l) (swap_program sw r)

         | KPcompose l r          => KPcompose (swap_program sw l) (swap_program sw r)

         | KPloop p               => KPloop (swap_program sw p)

         | KPodeSystem ode f     => KPodeSystem (swap_ode sw ode) (swap_formula sw f)
         end.


Definition swap_state (sw : swapping) (s : state) : state :=
  fun a => s (swap_assgn sw a).

Lemma swap_twice :
  forall sw v,
    swap sw (swap sw v) = v.
Proof.
  introv.
  unfold swap; repeat dest_cases w.
Qed.
Hint Rewrite swap_twice : core.

Lemma swap_assgn_twice :
  forall sw a,
    swap_assgn sw (swap_assgn sw a) = a.
Proof.
  induction a; simpl; autorewrite with core; auto.
  rewrite IHa; auto.
Qed.
Hint Rewrite swap_assgn_twice : core.

Lemma swap_state_twice :
  forall sw v, swap_state sw (swap_state sw v) = v.
Proof.
  introv; apply functional_extensionality; introv.
  unfold swap_state; autorewrite with core; auto.
Qed.

Lemma map_vec_flatten :
  forall {n A B} (v : Vector.t (list A) n) (g : A -> B),
    map g (vec_flatten v)
    = vec_flatten (Vector.map (map g) v).
Proof.
  induction n; introv.

  { apply Vector.case0 with (v := v); simpl; auto. }

  apply (Vector.caseS' v); introv; clear v; simpl.
  rewrite map_app, IHn; auto.
Qed.

Lemma term_variables_swap_term_eq :
  forall t sw,
    term_variables (swap_term sw t)
    = map (swap sw) (term_variables t).
Proof.
  term_ind t Case; introv; simpl; auto;
    try (complete (rewrite IHt; auto));
    try (complete (rewrite IHt1, IHt2; rewrite map_app; auto)).

  { Case "KTfuncOf".
    rewrite map_vec_flatten.
    repeat (rewrite vec_map_map; unfold compose).
    f_equal.
    apply eq_vec_map; introv i; tcsp. }

  { Case "KTread".
    destruct var; simpl; auto. }
Qed.

Lemma free_vars_term_swap_term_eq :
  forall t sw,
    free_vars_term (swap_term sw t)
    = map (swap_assgn sw) (free_vars_term t).
Proof.
  term_ind t Case; introv; simpl; auto;
    try (complete (rewrite IHt; auto));
    try (complete (rewrite IHt1, IHt2; rewrite map_app; auto)).

  { Case "KTfuncOf".
    rewrite map_vec_flatten.
    repeat (rewrite vec_map_map; unfold compose).
    f_equal.
    apply eq_vec_map; introv i; tcsp. }

  { Case "KTdifferential".
    rewrite map_app.
    f_equal; auto.
    rewrite IHt.
    unfold KD.
    allrw map_map; unfold compose; simpl; auto. }
Qed.

Lemma eq_swap_implies_eq :
  forall sw v1 v2,
    swap sw v1 = swap sw v2 -> v1 = v2.
Proof.
  introv h.
  destruct sw.
  unfold swap in *; simpl.
  repeat (dest_cases w; simpl in *; try subst; tcsp).
Qed.

Lemma eq_swap_assgn_implies_eq :
  forall sw v1 v2,
    swap_assgn sw v1 = swap_assgn sw v2 -> v1 = v2.
Proof.
  induction v1; destruct v2; simpl; introv h; ginv; f_equal.
  { apply (eq_swap_implies_eq sw); inversion h; auto. }
  { apply IHv1; inversion h; auto. }
Qed.

Lemma swap_state_upd_state_KAssignVar :
  forall sw v x t,
    swap_state sw (upd_state v (KAssignVar (swap sw x)) t)
    = upd_state (swap_state sw v) (KAssignVar x) t.
Proof.
  introv.
  apply functional_extensionality; introv.
  unfold swap_state.
  unfold upd_state, swap_assgn; simpl.
  destruct x0 as [var|diff]; repeat (dest_cases w).
  destruct n; f_equal; apply (eq_swap_implies_eq sw).
  inversion e; auto.
Qed.

Lemma map_remove_duplicates_if_inj :
  forall {A B} (l : list A) (f : A -> B) decA decB,
    (forall a b, f a = f b -> a = b)
    -> map f (remove_duplicates decA l)
       = remove_duplicates decB (map f l).
Proof.
  induction l; introv imp; simpl in *; auto.
  repeat (dest_cases w); simpl in *; auto.

  { rewrite in_map_iff in n; destruct n; eexists; dands; eauto. }

  { rewrite in_map_iff in i; exrepnd.
    apply imp in i1; subst; tcsp. }

  { rewrite (IHl _ decA decB); auto. }
Qed.

Lemma term_variables_nodup_swap_term_eq :
  forall t sw,
    term_variables_nodup (swap_term sw t)
    = map (swap sw) (term_variables_nodup t).
Proof.
  introv.
  unfold term_variables_nodup.
  rewrite term_variables_swap_term_eq.
  symmetry.
  apply map_remove_duplicates_if_inj.
  introv.
  apply eq_swap_implies_eq.
Qed.

Lemma big_sum_map_ext :
  forall {T}
         (l : list T)
         (f1 f2 : T -> R)
         (f : T -> T)
         (dec : Deq T),
    (forall a b, f a = f b -> a = b)
    -> (forall v : T, In v l -> f1 (f v) = f2 v)
    -> big_sum (remove_duplicates dec (map f l)) f1
       = big_sum (remove_duplicates dec l) f2.
Proof.
  induction l; introv inj imp; simpl; auto.
  repeat (dest_cases w; simpl in *).

  { rewrite in_map_iff in i; exrepnd.
    apply inj in i1; subst; tcsp. }

  { rewrite in_map_iff in n; destruct n; exists a; dands; auto. }

  { f_equal; auto. }
Qed.

Lemma swap_state_as_apply_diff_swap :
  forall v sw x,
    swap_state sw v (KD x)
    = v (KD (swap_assgn sw x)).
Proof.
  introv.
  unfold swap_state; simpl; auto.
Qed.

Lemma swap_state_as_apply_swap_assgn :
  forall v sw x,
    swap_state sw v x
    = v (swap_assgn sw x).
Proof.
  introv.
  unfold swap_state; simpl; auto.
Qed.

Lemma swap_state_swap_assgn :
  forall sw v a,
    swap_state sw v (swap_assgn sw a)
    = v a.
Proof.
  introv.
  unfold swap_state.
  rewrite swap_assgn_twice; auto.
Qed.

Lemma swap_state_inj :
  forall sw v w,
    swap_state sw v = swap_state sw w -> v = w.
Proof.
  introv h.
  unfold swap_state in h.
  apply functional_extensionality; introv.
  pose proof (equal_f h (swap_assgn sw x)) as q; simpl in q.
  autorewrite with core in *; auto.
Qed.

Lemma length_swap_vars :
  forall sw vars, length (swap_vars sw vars) = length vars.
Proof.
  introv.
  unfold swap_vars.
  rewrite map_length; auto.
Qed.
Hint Rewrite length_swap_vars : core.

Lemma length_swap_assgns :
  forall sw vars, length (swap_assgns sw vars) = length vars.
Proof.
  introv.
  unfold swap_assgns.
  rewrite map_length; auto.
Qed.
Hint Rewrite length_swap_assgns : core.

Lemma upd_list_state_swap_state :
  forall sw v vars rs a,
    upd_list_state (swap_state sw v) (combine vars rs) a
    = swap_state sw (upd_list_state v (combine (swap_vars sw vars) rs)) a.
Proof.
  induction vars; introv; simpl; auto.
  destruct rs; simpl; auto.
  unfold upd_state at 1.
  rewrite IHvars.
  rewrite swap_state_upd_state_KAssignVar; auto.
Qed.

Lemma interp_swap_ext :
  forall (I : interpretation) C sw,
    interpQuantExt
      (fun f s =>
         interp_quant_f
           (I (SymbolQuantifier C))
           (fun s => f (swap_state sw s))
           (swap_state sw s)).
Proof.
  introv h q.
  remember (I (SymbolQuantifier C)) as c; simpl in c.
  destruct c as [F cond]; clear Heqc; simpl.
  apply cond; auto.
  introv.
  unfold swap_state.
  apply h; auto.
Qed.

Lemma interpOdeExt_swap :
  forall sw (I : interpretation) c,
    interpOdeExt
      (swap_assgns sw (interp_ode_bv (I (SymbolODE c))))
      (fun s =>
         swap_state
           sw
           (interp_ode_dm
              (I (SymbolODE c))
              (swap_state sw s))).
Proof.
  introv h.
  remember (I (SymbolODE c)) as C; destruct C as [bv sem ext]; simpl; clear HeqC.
  apply ext; introv.
  unfold swap_state.
  apply h.
Qed.

Definition swap_interp (sw : swapping) (I : interpretation) : interpretation :=
  fun f : Symbol =>
    match f with
    | SymbolFunction g n => I (SymbolFunction g n)
    | SymbolDotTerm n => I (SymbolDotTerm n)
    | SymbolPredicate p n => I (SymbolPredicate p n)
    | SymbolQuantifier C =>
      MkInterpQuant
        (fun f s =>
           interp_quant_f
             (I (SymbolQuantifier C))
             (fun s => f (swap_state sw s))
             (swap_state sw s))
        (interp_swap_ext I C sw)

    | SymbolDotForm => fun s => I SymbolDotForm (swap_state sw s)

    | SymbolODE c =>
      MkInterpODE
        (swap_assgns sw (interp_ode_bv (I (SymbolODE c))))
        (fun s =>
           swap_state
             sw
             (interp_ode_dm
                (I (SymbolODE c))
                (swap_state sw s)))
        (interpOdeExt_swap sw I c)

    | SymbolProgramConst a =>
      fun v w => I (SymbolProgramConst a) (swap_state sw v) (swap_state sw w)
    end.

Lemma eq_maps3 :
  forall (A B C : Type) (f : A -> B) (g  : C -> B) (la : list A) (lc : list C),
    length la = length lc
    -> (forall a c,  List.In (a,c) (combine la lc) -> f a = g c)
    -> map f la = map g lc.
Proof.
  induction la; destruct lc; introv len imp; allsimpl; tcsp; tcsp.
  f_equal; auto.
Qed.

Lemma length_ode_vars_swap_interp :
  forall sw I ode,
    length (ode_assign (swap_interp sw I) ode)
    = length (ode_assign I ode).
Proof.
  induction ode; simpl.

  { destruct child; simpl; auto.
    autorewrite with core; auto. }

  { allrw app_length.
    rewrite IHode1, IHode2; auto. }
Qed.
Hint Rewrite length_ode_vars_swap_interp : core.

Lemma length_ode_vars_swap_ode :
  forall I sw ode,
    length (ode_assign I (swap_ode sw ode))
    = length (ode_assign I ode).
Proof.
  induction ode; simpl.

  { destruct child; simpl; auto. }

  { allrw app_length.
    rewrite IHode1, IHode2; auto. }
Qed.
Hint Rewrite length_ode_vars_swap_ode : core.

Lemma map_ode_vars_swap_ode :
  forall sw I ode,
    map (swap_assgn sw) (ode_assign I (swap_ode sw ode))
    = ode_assign (swap_interp sw I) ode.
Proof.
  induction ode; simpl.

  { destruct child; simpl; auto.
    rewrite swap_assgn_twice; auto. }

  { allrw map_app.
    rewrite IHode1, IHode2; auto. }
Qed.

Lemma combine_map_l :
  forall {A B} (f : A -> B) (l : list A),
    combine (map f l) l = map (fun a : A => (f a, a)) l.
Proof.
  induction l; simpl; auto.
  f_equal; auto.
Qed.

Lemma combine_map_r :
  forall {A B} (f : A -> B) l,
    combine l (map f l)
    = map (fun a => (a, f a)) l.
Proof.
  induction l; simpl; auto.
  rw IHl; sp.
Qed.

Lemma ode_footprint_diff_swap_interp :
  forall ode sw I,
    ode_footprint_diff (swap_interp sw I) ode
    = map (swap_assgn sw) (ode_footprint_diff I (swap_ode sw ode)).
Proof.
  introv.
  unfold ode_footprint_diff.
  allrw map_map; unfold compose.
  apply eq_maps3.

  { autorewrite with core; auto. }

  { introv i.
    simpl.
    unfold KD; f_equal.
    rewrite <- map_ode_vars_swap_ode in i.
    rewrite combine_map_l in i.
    apply in_map_iff in i; exrepnd; ginv; auto.
  }
Qed.

Lemma ode_footprint_vars_swap_interp :
  forall ode sw I,
    ode_footprint_vars (swap_interp sw I) ode
    = map (swap_assgn sw) (ode_footprint_vars I (swap_ode sw ode)).
Proof.
  introv.
  unfold ode_footprint_vars.
  rewrite map_ode_vars_swap_ode; auto.
Qed.

Lemma ode_footprint_swap_interp :
  forall ode sw I,
    ode_footprint (swap_interp sw I) ode
    = map (swap_assgn sw) (ode_footprint I (swap_ode sw ode)).
Proof.
  introv.
  unfold ode_footprint.
  rewrite ode_footprint_diff_swap_interp.
  rewrite ode_footprint_vars_swap_interp.
  rewrite map_app; auto.
Qed.

Lemma swap_state_upd_state_swap_assgn :
  forall sw v x t,
    swap_state sw (upd_state v (swap_assgn sw x) t)
    = upd_state (swap_state sw v) x t.
Proof.
  introv.
  apply functional_extensionality; introv.
  unfold swap_state.
  unfold upd_state; simpl.
  repeat (dest_cases w; subst; tcsp).
  apply eq_swap_assgn_implies_eq in e; subst; tcsp.
Qed.

Lemma swap_term_dynamic_semantics_term :
  forall t I v sw,
    dynamic_semantics_term I v (swap_term sw t)
    = dynamic_semantics_term (swap_interp sw I) (swap_state sw v) t.
Proof.
  term_ind t Case; introv; simpl; auto;
    try (complete (rewrite IHt; auto));
    try (complete (rewrite IHt1, IHt2; auto)).

  { Case "KTfuncOf".
    f_equal.
    rewrite vec_map_map; unfold compose; simpl.
    apply eq_vec_map; introv i; tcsp.
  }

  { Case "KTdifferential".
    unfold term_assignables_nodup.
    rewrite free_vars_term_swap_term_eq.
    apply big_sum_map_ext; auto; try (apply eq_swap_assgn_implies_eq);[].

    introv i.
    rewrite swap_state_as_apply_diff_swap.
    rewrite swap_state_as_apply_swap_assgn.
    f_equal.
    apply Derive_ext; introv.

    rewrite IHt.
    rewrite swap_state_upd_state_swap_assgn; auto.
  }
Qed.

Lemma dynamic_semantics_ode_fun_swap_ode :
  forall ode I sw s a,
    dynamic_semantics_ode_fun I (swap_ode sw ode) s a
    = dynamic_semantics_ode_fun
          (swap_interp sw I) ode
          (swap_state sw s) (swap_assgn sw a).
Proof.
  induction ode; introv; simpl.

  { destruct child; simpl; auto.

    { rewrite swap_state_twice.
      remember (I (SymbolODE name)) as C; simpl in C.
      destruct C as [bv sem ext]; clear HeqC; simpl.
      unfold swap_state; simpl.
      rewrite swap_assgn_twice; auto. }

    { repeat (dest_cases w; subst; simpl in *; GC); autorewrite with core in *; ginv.
      { apply swap_term_dynamic_semantics_term. }
      { unfold KD in n; tcsp. }
      { destruct a; simpl in *; ginv.
        fold KD in *; ginv.
        rewrite swap_assgn_twice in n; tcsp. }
    }
  }

  { rewrite IHode1, IHode2; auto. }
Qed.

Lemma dynamic_semantics_ode_swap_ode :
  forall ode I sw r phi,
    dynamic_semantics_ode I (swap_ode sw ode) r phi
    <-> dynamic_semantics_ode
          (swap_interp sw I) ode r
          (fun x : R => swap_state sw (phi x)).
Proof.
  introv; split; introv h i; simpl in *; autorewrite with core.

  { rewrite <- map_ode_vars_swap_ode in i.
    rewrite in_map_iff in i; exrepnd; subst.
    apply (h zeta) in i0; repnd.
    dands; auto.

    { eapply ex_derive_ext;[|exact i1]; introv; simpl; auto.
      unfold swap_state; simpl.
      rewrite swap_assgn_twice; auto. }

    { unfold swap_state; simpl.
      rewrite swap_assgn_twice.
      fold KD in *.
      rewrite i2; auto. }

    { unfold swap_state; simpl in *.
      rewrite swap_assgn_twice.
      fold KD in *.
      rewrite i0; auto.
      apply dynamic_semantics_ode_fun_swap_ode. }
  }

  { pose proof (h zeta (swap_assgn sw v)) as q.
    rewrite <- map_ode_vars_swap_ode in q.
    rewrite in_map_iff in q; autodimp q hyp.
    { eexists; dands; eauto. }
    simpl in *.
    repnd; dands; auto.

    { eapply ex_derive_ext;[|exact q0]; introv; simpl; auto.
      unfold swap_state; simpl.
      rewrite swap_assgn_twice; auto. }

    { unfold swap_state in q1; simpl in q1.
      rewrite swap_assgn_twice in q1; auto. }

    { unfold swap_state in q; simpl in q.
      rewrite swap_assgn_twice in q.
      fold KD in *.
      rewrite q.
      symmetry.
      apply dynamic_semantics_ode_fun_swap_ode. }
  }
Qed.

Lemma swap_dynamic_semantics_formula_program :
  (forall f sw I v,
      dynamic_semantics_formula I (swap_formula sw f) v
      <->
      dynamic_semantics_formula (swap_interp sw I) f (swap_state sw v)
  )
  /\
  (forall p sw I v w,
      dynamic_semantics_program I (swap_program sw p) v w
      <->
      dynamic_semantics_program (swap_interp sw I) p (swap_state sw v) (swap_state sw w)
  ).
Proof.
  form_prog_ind Case;
    introv;
    simpl in *; tcsp; auto;
      try (complete (repeat (rewrite swap_term_dynamic_semantics_term); tcsp));
      try (complete (introv ih; introv; rewrite ih; tcsp));
      try (complete (introv ih1 ih2; split; introv h; repnd;
                     try (rewrite <- ih1, <- ih2; tcsp);
                     try (rewrite ih1, ih2; tcsp))).

  { Case "KFdot".
    rewrite swap_state_twice; tcsp. }

  { Case "KFpredOf".
    rewrite vec_map_map; unfold compose.
    match goal with
    | [ |- _ _ ?x <-> _ _ ?y ] => assert (x = y) as xx;[|rewrite xx;tcsp];[]
    end.
    apply eq_vec_map; introv i.
    rewrite swap_term_dynamic_semantics_term; auto.
  }

  { Case "KFquantifier".
    introv ih; introv.
    remember (I (SymbolQuantifier f)) as C; simpl in C.
    destruct C as [C ext]; simpl in *; clear HeqC.
    apply ext; introv; tcsp.
    rewrite swap_state_twice; auto.
  }

  { Case "KFforallVars".
    introv ih; introv.
    split; intro h; introv len; autorewrite with core in *.

    { applydup h in len.
      rewrite ih in len0.
      eapply ext_dynamic_semantics_formula;[| |exact len0].
      { introv; apply upd_list_state_swap_state. }
      { apply ext_interpretations_refl. }
    }

    { applydup h in len.
      rewrite ih.
      eapply ext_dynamic_semantics_formula;[| |exact len0].
      { introv; symmetry; apply upd_list_state_swap_state. }
      { apply ext_interpretations_refl. }
    }
  }

  { Case "KFexistsVars".
    introv ih; introv.
    split; intro h; introv; exrepnd; exists rs; autorewrite with core in *; dands; auto.

    { apply ih in h0.
      eapply ext_dynamic_semantics_formula;[| |exact h0].
      { introv; apply upd_list_state_swap_state. }
      { apply ext_interpretations_refl. }
    }

    { apply ih.
      eapply ext_dynamic_semantics_formula;[| |exact h0].
      { introv; symmetry; apply upd_list_state_swap_state. }
      { apply ext_interpretations_refl. }
    }
  }

  { Case "KFbox".
    introv ihp ihf; introv.
    split; introv h dsp.

    {
      pose proof (ihf sw I (swap_state sw w)) as q.
      rewrite swap_state_twice in q; apply q; clear q.
      apply h; clear h.
      apply ihp.
      rewrite swap_state_twice; auto.
    }

    {
      apply ihf; clear ihf.
      apply h; clear h.
      apply ihp; auto.
    }
  }

  { Case "KFdiamond".
    introv ihp ihf; introv.
    split; introv h; exrepnd.

    {
      exists (swap_state sw w); dands; auto.
      { apply ihf; auto. }
      { apply ihp; auto. }
    }

    {
      exists (swap_state sw w); dands.
      { apply ihf; rewrite swap_state_twice; auto. }
      { apply ihp; rewrite swap_state_twice; auto. }
    }
  }

  { Case "KPconstant".
    repeat (rewrite swap_state_twice); tcsp.
  }

  { Case "KPassign".
    rewrite swap_term_dynamic_semantics_term.
    split; introv h; unfold differ_state_except in *;
      repnd; dands; auto; introv i.

    { unfold swap_state.
      apply h0; intro xx.
      apply eq_swap_assgn_implies_eq in xx; tcsp. }

    { pose proof (h0 (swap_assgn sw y)) as q.
      autodimp q hyp.
      { intro xx; subst.
        autorewrite with core in *; tcsp. }
      repeat (rewrite swap_state_swap_assgn in q); auto. }
  }

  { Case "KPassignAny".
    split; intro h; exrepnd; exists r; unfold differ_state_except in *;
      repnd; dands; auto; introv i.

    { unfold swap_state.
      apply h1; intro xx.
      apply eq_swap_assgn_implies_eq in xx; tcsp. }

    { pose proof (h1 (swap_assgn sw y)) as q.
      autodimp q hyp.
      { intro xx; subst.
        autorewrite with core in *; tcsp. }
      repeat (rewrite swap_state_swap_assgn in q); auto. }
  }

  { Case "KPtest".
    introv ihf; introv.
    split; intro h; repnd; subst.

    { rewrite <- ihf; dands; auto. }

    { rewrite <- ihf in h; dands; auto.
      apply swap_state_inj in h0; auto. }
  }

  { Case "KPcompose".
    introv ih1 ih2; introv.
    split; intro h; exrepnd.
    { rewrite ih1 in h1.
      rewrite ih2 in h0.
      eexists; dands; eauto. }
    { pose proof (ih1 sw I v (swap_state sw s)) as q.
      rewrite swap_state_twice in q.
      apply q in h1; clear q.

      pose proof (ih2 sw I (swap_state sw s) w) as q.
      rewrite swap_state_twice in q.
      apply q in h0; clear q.

      exists (swap_state sw s); dands; auto.
    }
  }

  { Case "KPloop".
    introv ih; introv; split; introv h;
      allrw program_close_implies_all; exrepnd; exists n.

    {
      revert w h0.
      induction n; introv dsp; simpl in *; repnd; subst; dands; auto.
      exrepnd.
      exists (swap_state sw s).
      apply IHn in dsp1; clear IHn.
      apply ih in dsp0; clear ih.
      dands; auto.
    }

    {
      revert w h0.
      induction n; introv dsp; simpl in *; repnd; subst; dands; auto.

      { apply swap_state_inj in dsp0; auto. }

      exrepnd.
      pose proof (IHn (swap_state sw s)) as q; clear IHn.
      rewrite swap_state_twice in q; apply q in dsp1; clear q.
      pose proof (ih sw I (swap_state sw s) w) as q; clear ih.
      rewrite swap_state_twice in q; apply q in dsp0; clear q.
      exists (swap_state sw s); dands; auto.
    }
  }

  { Case "KPodeSystem".
    introv ih; introv.
    split; intro h; exrepnd; subst.

    { exists r (fun x => swap_state sw (phi x)).
      dands; auto.

      { introv i.
        unfold swap_state.
        apply h0.
        rewrite ode_footprint_diff_swap_interp in i.
        intro j; destruct i; rewrite in_map_iff.
        eexists; dands;[|eauto].
        rewrite swap_assgn_twice; auto. }

      { apply dynamic_semantics_ode_swap_ode; auto. }

      { introv; pose proof (h1 zeta) as q; clear h1; repnd.
        unfold swap_state; simpl.
        rewrite ih in q0; clear ih.
        unfold swap_state in q0; dands; auto.

        introv i.
        apply q.
        rewrite ode_footprint_swap_interp in i.
        intro j; destruct i; rewrite in_map_iff.
        eexists; dands;[|eauto].
        rewrite swap_assgn_twice; auto. }
    }

    { exists r (fun x => swap_state sw (phi x)).
      unfold swap_state in *; simpl in *.
      dands; auto.

      { introv i.
        pose proof (h0 (swap_assgn sw x)) as q.
        rewrite ode_footprint_diff_swap_interp in q.
        autodimp q hyp.
        { rewrite in_map_iff.
          introv xx; destruct i; exrepnd.
          apply eq_swap_assgn_implies_eq in xx1; subst; auto. }
        rewrite swap_assgn_twice in q; auto. }

      { rewrite <- h2.
        apply functional_extensionality; introv.
        rewrite swap_assgn_twice; auto. }

      { apply dynamic_semantics_ode_swap_ode; auto.
        unfold swap_state; simpl.
        assert ((fun (x : R) (a : KAssignable) => phi x (swap_assgn sw (swap_assgn sw a)))
                = phi) as xx.
        { apply functional_extensionality; introv.
          apply functional_extensionality; introv.
          rewrite swap_assgn_twice; auto. }
        rewrite xx; clear xx; auto. }

      { introv; pose proof (h1 zeta) as q; clear h1; repnd.
        rewrite ih; clear ih.
        assert ((fun (a : KAssignable) => phi zeta (swap_assgn sw (swap_assgn sw a)))
                = phi zeta) as xx.
        { apply functional_extensionality; introv.
          rewrite swap_assgn_twice; auto. }
        rewrite xx; clear xx; dands; auto.

        introv i.
        apply q.
        rewrite ode_footprint_swap_interp.
        intro j; destruct i; rewrite in_map_iff in j; exrepnd.
        apply eq_swap_assgn_implies_eq in j1; subst; auto. }
    }
  }
Qed.

Lemma swap_dynamic_semantics_formula :
  forall f sw I v,
    dynamic_semantics_formula I (swap_formula sw f) v
    <->
    dynamic_semantics_formula (swap_interp sw I) f (swap_state sw v).
Proof.
  pose proof swap_dynamic_semantics_formula_program; tcsp.
Qed.

Definition swap_rule (f : Formula) (sw : swapping) : rule :=
  MkRule
    [f]
    (swap_formula sw f).

Lemma swap_rule_true :
  forall f sw, rule_true (swap_rule f sw).
Proof.
  introv h; simpl in *.
  dLin_hyp q.
  repeat introv.
  apply swap_dynamic_semantics_formula.
  apply q.
Qed.

Lemma swap_vars_twice :
  forall sw l,
    swap_vars sw (swap_vars sw l) = l.
Proof.
  induction l; simpl; auto.
  rewrite IHl.
  rewrite swap_twice; auto.
Qed.
Hint Rewrite swap_vars_twice : core.

Lemma swap_assgns_twice :
  forall sw l,
    swap_assgns sw (swap_assgns sw l) = l.
Proof.
  induction l; simpl; auto.
  rewrite IHl.
  rewrite swap_assgn_twice; auto.
Qed.
Hint Rewrite swap_assgns_twice : core.

Lemma ext_interpretations_at_swap_interp_twice :
  forall sw I s,
    ext_interpretations_at
      (swap_interp sw (swap_interp sw I))
      I
      s.
Proof.
  repeat introv.
  destruct s; simpl; tcsp.

  { introv h q.
    remember (I (SymbolQuantifier f)) as F.
    destruct F as [F cond]; clear HeqF; simpl in *.
    apply cond; clear cond; introv;
      rewrite swap_state_twice; auto. }

  { introv h.
    rewrite swap_state_twice.
    assert (v = w) as xx by (apply functional_extensionality; auto).
    subst; tcsp. }

  { rewrite swap_assgns_twice; dands; auto.
    introv h.
    rewrite swap_state_twice.
    remember (I (SymbolODE c)) as C.
    destruct C as [bv sem ext]; simpl in *; clear HeqC.
    apply ext; clear ext.
    introv.
    rewrite swap_state_twice; auto. }

  { introv h1 h2.
    repeat (rewrite swap_state_twice).
    assert (v1 = v2) as xx1 by (apply functional_extensionality; auto).
    assert (w1 = w2) as xx2 by (apply functional_extensionality; auto).
    subst; tcsp. }
Qed.
Hint Resolve ext_interpretations_at_swap_interp_twice : core.

Lemma swap_interp_twice :
  forall sw I,
    ext_interpretations
      (swap_interp sw (swap_interp sw I))
      I.
Proof.
  repeat introv.
  apply ext_interpretations_at_swap_interp_twice.
Qed.
Hint Resolve swap_interp_twice : core.

Lemma equal_interpretations_on_ext_swap_interp_twice :
  forall sw I l,
    equal_interpretations_on_ext
      (swap_interp sw (swap_interp sw I))
      I
      l.
Proof.
  introv i.
  apply ext_interpretations_at_swap_interp_twice.
Qed.
Hint Resolve equal_interpretations_on_ext_swap_interp_twice : core.
