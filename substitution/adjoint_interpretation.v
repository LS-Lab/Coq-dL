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
Require Export US_defs.
Require Export static_sem_lemmas.
Require Export lookup_lemmas.
Require Export admissible_terms.
Require Export eassignables_terms.
Require Export lookup_lemmas.
Require Export list_util.
Require Export coincidence.
Require Export bound_effect.
Require Export dynamic_semantics_prop.


(**

  This file contains some the definition of adjoint interpretations and
  therefore, a proof of their well-formedness.

*)


Hint Rewrite Nat.sub_succ : core.
Hint Rewrite orb_false_r  : core.
Hint Rewrite orb_true_r   : core.

(*
Lemma sub_sub_same_prop1 :
  forall (a b : nat),
    b <= a -> a - (a - b) = b.
Proof.
  introv l; omega.
Qed.
*)

Lemma ext_dynamic_semantics_term :
  forall t v (I J : interpretation),
    ext_interpretations I J
    -> dynamic_semantics_term I v t = dynamic_semantics_term J v t.
Proof.
  introv ext.
  apply coincidence_term; eauto with core.
Qed.

Lemma ext_dynamic_semantics_formula :
  forall F (I J : interpretation) v w,
    (forall a, v a = w a)
    -> ext_interpretations I J
    -> dynamic_semantics_formula I F v <-> dynamic_semantics_formula J F w.
Proof.
  introv exts ext.
  apply coincidence_formula; eauto 3 with core.
  introv i; apply exts.
Qed.

Lemma ext_interpretations_upd_interpretation_dot_form :
  forall I f g,
    (forall s, f s <-> g s)
    -> ext_interpretations
         (upd_interpretation_dot_form I f)
         (upd_interpretation_dot_form I g).
Proof.
  introv imp; introv.
  destruct s; simpl; tcsp; introv.

  { introv h1 h2.
    remember (I (SymbolQuantifier f0)) as iQ; simpl in iQ; destruct iQ as [F cond]; simpl.
    apply cond; auto. }

  { introv h; rewrite imp.
    (* make interpretations more extensional to get rid of functional_extensionality *)
    assert (v = w) as xx by (apply functional_extensionality; auto).
    rewrite xx; tcsp. }

  { dands; auto.
    introv h.
    remember (I (SymbolODE c)) as ic; simpl in ic.
    destruct ic as [bv sem cond]; simpl in *.
    apply cond; auto.
  }

  { introv h1 h2.
    (* make interpretations more extensional to get rid of functional_extensionality *)
    assert (v1 = v2) as xx1 by (apply functional_extensionality; auto).
    assert (w1 = w2) as xx2 by (apply functional_extensionality; auto).
    rewrite xx1, xx2; tcsp. }
Qed.

Definition ex_partial_derive_st_func_partial_derive_st
           (f : interpretation -> state -> R)
           (m : nat)
           (l : list KAssignable)
           (s : state)
           (I : interpretation) : Prop :=
  smooth_fun_T
    (fun d : Vector.t R m => partial_derive (f (upd_interpretation_dots I d)) l s).

Definition ex_partial_derive_st_func_partial_derive_st_all
           (f : interpretation -> state -> R) :=
  forall (m : nat)
         (l : list KAssignable)
         (s : state)
         (I : interpretation),
    ex_partial_derive_st_func_partial_derive_st f m l s I.

Hint Resolve vec_nth_in : core.

Lemma ex_partial_derive_st_func_partial_derive_st_all_dot :
  forall n,
    ex_partial_derive_st_func_partial_derive_st_all (fun I _ => I (SymbolDotTerm n)).
Proof.
  introv d cond; introv; subst; simpl in *.

  pose proof (cond (vec_nth ts n d)) as q; clear cond.

  destruct (le_lt_dec m n).

  { clear q.
    eapply ex_derive_ext;
      [simpl;introv;symmetry;apply partial_derive_st_ext;introv;
       rewrite vec_nth_default;[reflexivity|auto] |].

    destruct l0.

    { simpl; apply @ex_derive_const. }

    { eapply ex_derive_ext;
        [introv;symmetry;apply partial_derive_st_const; simpl; try omega|].
      apply @ex_derive_const. }
  }

  { pose proof (q v l0) as h; clear q.
    repeat (autodimp h hyp); eauto 2 with core; try (apply sublist_refl).
    eapply ex_derive_ext;
      [simpl;introv;symmetry;apply partial_derive_st_ext;introv;
       rewrite (vec_nth_map _ _ _ d);auto;reflexivity|].
    destruct l.

    { simpl; apply h. }

    { eapply ex_derive_ext;
        [introv;symmetry;apply partial_derive_st_ext;introv;
         apply partial_derive_st_const;simpl;omega|].
      eapply ex_derive_ext;
        [introv;symmetry;apply partial_derive_st_const0|].
      simpl; apply @ex_derive_const. }
  }
Qed.

Lemma ex_partial_derive_st_func_partial_derive_st_all_read :
  forall v, ex_partial_derive_st_func_partial_derive_st_all (fun _ s => s v).
Proof.
  introv d cond; introv; simpl in *.

  destruct l0.

  { simpl; apply @ex_derive_const. }

  { eapply ex_derive_ext;
      [introv;symmetry;apply partial_derive_st_const; simpl; try omega|].
    apply @ex_derive_const. }
Qed.

Lemma ex_partial_derive_st_func_partial_derive_st_all_const :
  forall r, ex_partial_derive_st_func_partial_derive_st_all (fun _ _ => r).
Proof.
  introv d cond; introv; subst; simpl in *.

  destruct l0.

  { simpl; apply @ex_derive_const. }

  { eapply ex_derive_ext;
      [introv;symmetry;apply partial_derive_st_const; simpl; try omega|].
    apply @ex_derive_const. }
Qed.

Lemma ex_partial_derive_st_l_pt_opp :
  forall (L : state -> R) v l,
    (forall w l', sublist (w :: l') (v :: l) -> ex_partial_derive L w l')
    -> ex_partial_derive (fun st => - L st) v l.
Proof.
  introv d1; introv; simpl in *.
  eapply ex_derive_ext;
    [introv;symmetry;apply partial_derive_st_opp_sublist; auto|].
  simpl.
  apply @ex_derive_opp; simpl; apply d1; apply sublist_refl.
Qed.

Lemma ex_partial_derive_st_func_partial_derive_st_all_neg :
  forall F,
    (forall I, ex_all_partial_derive_st (F I))
    -> ex_partial_derive_st_func_partial_derive_st_all F
    -> ex_partial_derive_st_func_partial_derive_st_all (fun I s => - (F I s)).
Proof.
  introv h1 h2 d cond; simpl in *.
  eapply ex_partial_derive_ext;
    [introv; symmetry; apply partial_derive_st_opp;
     introv len; apply h1|].
  apply ex_partial_derive_st_l_pt_opp; introv ss.
  apply h2; auto.
  introv i ss'.
  apply cond; auto.
  eapply sublist_trans; eauto.
Qed.

Lemma ex_partial_derive_st_func_partial_derive_st_all_plus :
  forall F G,
    (forall I, ex_all_partial_derive_st (F I))
    -> (forall I, ex_all_partial_derive_st (G I))
    -> ex_partial_derive_st_func_partial_derive_st_all F
    -> ex_partial_derive_st_func_partial_derive_st_all G
    -> ex_partial_derive_st_func_partial_derive_st_all (fun I s => (F I s + G I s)%R).
Proof.
  introv F1 G1 F2 G2 d cond.
  eapply ex_partial_derive_ext;
    [introv;symmetry;apply partial_derive_st_plus;
     introv len;[apply F1|apply G1] |].
  apply ex_partial_derive_st_l_pt_plus; introv ss;
    [apply F2|apply G2]; auto; introv i ss';
      apply cond; auto; eapply sublist_trans; eauto.
Qed.

Lemma partial_derive_st_minus_sublist :
  forall l st L R,
    (forall v k, sublist (v :: k) l -> ex_partial_derive L v k)
    -> (forall v k, sublist (v :: k) l -> ex_partial_derive R v k)
    -> partial_derive (fun s => (L s - R s)%R) l st
       = (partial_derive L l st - partial_derive R l st)%R.
Proof.
  induction l; introv dL dR; simpl in *; auto.
  erewrite Derive_ext;[|introv;apply IHl;auto].

  rewrite Derive_minus; auto.

  { apply dL.
    apply sublist_refl. }

  { apply dR.
    apply sublist_refl. }
Qed.

Lemma ex_partial_derive_st_l_pt_minus :
  forall (L R : state -> R) v l,
    (forall w l', sublist (w :: l') (v :: l) -> ex_partial_derive L w l')
    -> (forall w l', sublist (w :: l') (v :: l) -> ex_partial_derive R w l')
    -> ex_partial_derive (fun st => (L st - R st)%R) v l.
Proof.
  introv d1 d2; introv; simpl in *.
  eapply ex_derive_ext;
    [introv;symmetry;apply partial_derive_st_minus_sublist; auto|].
  simpl.
  apply @ex_derive_minus; simpl;[apply d1|apply d2];apply sublist_refl.
Qed.

Lemma ex_partial_derive_st_func_partial_derive_st_all_minus :
  forall F G,
    (forall I, ex_all_partial_derive_st (F I))
    -> (forall I, ex_all_partial_derive_st (G I))
    -> ex_partial_derive_st_func_partial_derive_st_all F
    -> ex_partial_derive_st_func_partial_derive_st_all G
    -> ex_partial_derive_st_func_partial_derive_st_all (fun I s => (F I s - G I s)%R).
Proof.
  introv F1 G1 F2 G2 d cond.
  eapply ex_partial_derive_ext;
    [introv;symmetry;apply partial_derive_st_minus;
     introv len;[apply F1|apply G1] |].
  Locate ex_partial_derive_st_l_pt_plus.
  apply ex_partial_derive_st_l_pt_minus; introv ss;
    [apply F2|apply G2]; auto; introv i ss';
      apply cond; auto; eapply sublist_trans; eauto.
Qed.

Lemma ex_derive_big_sum :
  forall (vs : list KAssignable) (F : R -> KAssignable -> R) pt,
    (forall v, List.In v vs -> ex_derive_R (fun r => F r v) pt)
    -> ex_derive_R (fun r => big_sum vs (F r)) pt.
Proof.
  induction vs; introv imp; simpl.

  { apply @ex_derive_const. }

  { apply @ex_derive_plus.
    - apply imp; simpl; auto.
    - apply IHvs; introv i; apply imp; simpl; auto. }
Qed.

Lemma Derive_big_sum :
  forall (vs : list KAssignable) (F : R -> KAssignable -> R) pt,
    (forall v, List.In v vs -> ex_derive_R (fun x => F x v) pt)
    -> Derive (fun w => big_sum vs (F w)) pt
       = big_sum vs (fun v => Derive (fun w => F w v) pt).
Proof.
  induction vs; introv imp.

  { simpl; auto.
    rewrite Derive_const; auto. }

  simpl.
  rewrite Derive_plus; auto.

  { rewrite IHvs; auto.
    introv i; apply imp; simpl; tcsp. }

  { apply imp; simpl; tcsp. }

  { apply ex_derive_big_sum; introv i; apply imp; simpl; auto. }
Qed.

Lemma partial_derive_st_big_sum :
  forall l (vs : list KAssignable) (F : state -> KAssignable -> R) s,
    (forall v, ex_all_partial_derive_st (fun s => F s v))
    -> partial_derive (fun w => big_sum vs (F w)) l s
       = big_sum vs (fun v => partial_derive (fun w => F w v) l s).
Proof.
  induction l using list_ind_snoc; introv imp; simpl; auto.

  rewrite partial_derive_st_S;[|autorewrite with core;omega].
  erewrite big_sum_ext;[|introv i;apply partial_derive_st_S;autorewrite with core;omega].
  simpl.
  erewrite partial_derive_st_ext;
    [|introv;apply Derive_big_sum; introv i;
      simpl in *;
      pose proof (imp v 0%nat s0 []) as q;
      simpl in q; apply q;auto
    ].
  autorewrite with core.

  rewrite IHl; auto.
  introv.

  pose proof (ex_all_partial_derive_st_add_Derive (fun s => F s v)) as q.
  apply q; auto.
Qed.

(*
Lemma ex_partial_derive_st_func_dynamic_semantics :
  forall m I v t,
    ex_partial_derive_st_func
      (fun d : Vector.t R m =>
         dynamic_semantics_term
           (upd_interpretation_dots I d)
           v
           t).
Proof.
  term_ind t Case; simpl.

  { Case "KTdot".
    introv d cond len; subst; simpl.

    destruct (le_lt_dec m n).

    { eapply ex_derive_ext;
        [simpl;introv;symmetry;apply partial_derive_st_ext;introv;
         rewrite vec_nth_default;[reflexivity|auto] |].

      destruct l.

      { simpl; apply @ex_derive_const. }

      { eapply ex_derive_ext;
          [introv;symmetry;apply partial_derive_st_const; simpl; try omega|].
        apply @ex_derive_const. }
    }

    { eapply ex_derive_ext;
        [simpl;introv;symmetry;apply partial_derive_st_ext;introv;
         rewrite (vec_nth_map _ _ _ d);auto;reflexivity|].
      eapply cond;[|reflexivity].
      apply vec_nth_in; auto.
    }
  }

  { Case "KTfuncOf".
    introv d cond len; simpl; subst.

    remember (I (SymbolFunction f n)) as iF; destruct iF as [F edf]; simpl.
    clear dependent f.

    eapply edf;[exact (KTdot 0)|]; clear edf.
    introv i ss.
    apply ex_all_partial_derive_st_implies_l_pt.
    apply IHargs; auto.
  }

  Focus 9.

  { Case "KTdifferential".
    introv d cond len; subst; simpl.

    eapply ex_derive_ext;
      [introv; symmetry;
       apply partial_derive_st_big_sum; introv;
       apply ex_all_partial_derive_st_mult;
       [apply ex_all_partial_derive_st_constant
       |(*apply ex_partial_derive_st_add_Derive;eauto 2 with core*)]
      |].

    introv len; subst.
    unfold ex_partial_derive_st_l; simpl.

(*
    Check partial_derive_st_S.

    SearchAbout partial_derive_st Derive.

    SearchAbout ex_partial_derive_st.

    apply ex_derive_n_big_sum; introv ltkn i.

    eapply ex_derive_n_ext;[introv;symmetry;apply partial_derive_st_DVar_mult|].

    { apply ex_partial_derive_st_add_Derive; eauto 2 with core. }

    eapply ex_derive_n_mult_gen; introv ltk.

    { apply ex_derive_n_const. }


    pose proof (IHt k0 (snoc l v) s I) as q.
    unfold partial_derive_I_st in q.
    eapply ex_derive_n_ext;[|apply q]; clear q.
    introv; cbv beta; simpl in *.
    rewrite partial_derive_st_S; autorewrite with core; try omega; auto.
 *)

Abort.
*)

Definition renaming := list (KVariable * KVariable).

Fixpoint rename_var (v : KVariable) (ren : renaming) : KVariable :=
  match ren with
  | [] => v
  | (a,b) :: r =>
    if KVariable_dec a v
    then b
    else rename_var v r
  end.

Definition arenaming := list (KAssignable * KAssignable).

Fixpoint rename_assign (v : KAssignable) (ren : arenaming) : KAssignable :=
  match ren with
  | [] => v
  | (a,b) :: r =>
    if KAssignable_dec a v
    then b
    else rename_assign v r
  end.

Inductive check_pair_ren (v1 v2 : KAssignable) : list KAssignable -> list KAssignable -> Prop :=
| check_pair_ren_nil : check_pair_ren v1 v2 [] []
| check_pair_ren_cons_same :
    forall l1 l2,
      check_pair_ren v1 v2 l1 l2
      -> check_pair_ren v1 v2 (v1 :: l1) (v2 :: l2)
| check_pair_ren_cons_diff :
    forall v1' v2' l1 l2,
      v1 <> v1'
      -> v2 <> v2'
      -> check_pair_ren v1 v2 l1 l2
      -> check_pair_ren v1 v2 (v1' :: l1) (v2' :: l2).
Hint Constructors check_pair_ren.

Inductive is_renaming : list KAssignable -> list KAssignable -> Prop :=
| is_renaming_nil : is_renaming [] []
| is_renaming_cons :
    forall v1 v2 l1 l2,
      check_pair_ren v1 v2 l1 l2
      -> is_renaming l1 l2
      -> is_renaming (v1 :: l1) (v2 :: l2).
Hint Constructors is_renaming.

Fixpoint rebase_var_sub (l : list KVariable) (s : var_sub) : var_sub :=
  match l, s with
  | [], _ => []
  | _, [] => []
  | v1 :: l, (_,r) :: s => (v1,r) :: rebase_var_sub l s
  end.

(** builds a var_sub from a state [s] w.r.t. a support [l1]
    and changes the domain to l2 *)
Fixpoint state2var_sub_rebase (s : state) (l1 l2 : list KVariable) : var_sub :=
  match l1,l2 with
  | [], _ => []
  | _, [] => []
  | v1 :: l1, v2 :: l2 => (v2, s (KAssignVar v1)) :: state2var_sub_rebase s l1 l2
  end.

Definition upd_state_rebase_st (s1 : state) (s2 : state) (l1 l2 : list KVariable) : state :=
  upd_list_state s1 (state2var_sub_rebase s2 l1 l2).

Definition assign_in_vars (a : KAssignable) (l : list KVariable) : bool :=
  match a with
  | KAssignVar v => if in_dec KVariable_dec v l then true else false
  | KAssignDiff _ => false
  end.

(** Same as upd_state_st but direct *)
Definition update_state_st_ext (s1 s2 : state) (l : list KAssignable) : state :=
  fun a : KAssignable =>
    if in_dec KAssignable_dec a l
    then s2 a
    else s1 a.

(**
  Same as upd_state_st_rebase but direct.
  It only really makes sense when [is_renaming l1 l2] is true
 *)
Definition update_state_st_ext_rebase (s1 s2 : state) (l1 l2 : list KAssignable) : state :=
  fun a =>
    if in_dec KAssignable_dec a l2
    then s2 (rename_assign a (combine l2 l1))
    else s1 a.

Fixpoint update_state_st (s1 s2 : state) (l : list KAssignable) : state :=
  match l with
  | [] => s1
  | v :: vs => upd_state (update_state_st s1 s2 vs) v (s2 v)
  end.

Fixpoint update_state_st_rebase (s1 s2 : state) (l1 l2 : list KAssignable) : state :=
  match l1,l2 with
  | [], _ => s1
  | _, [] => s1
  | v1 :: l1, v2 :: l2 =>
    upd_state (update_state_st_rebase s1 s2 l1 l2) v2 (s2 v1)
  end.

Lemma update_state_st_eq_ext :
  forall l s1 s2, update_state_st s1 s2 l = update_state_st_ext s1 s2 l.
Proof.
  induction l; introv; simpl.
  { unfold update_state_st_ext; simpl.
    apply functional_extensionality; introv; simpl.
    unfold assign_in_vars.
    destruct x; auto. }
  { rewrite IHl; clear IHl.
    unfold update_state_st_ext; simpl.
    apply functional_extensionality; introv; simpl.
    unfold upd_state; simpl.
    repeat (dest_cases w); ginv; tcsp.
    { apply not_or in n; repnd; tcsp. }
    { apply not_or in n0; repnd; tcsp. }
  }
Qed.

Lemma combine_nil_r :
  forall {A B} (l : list A), combine l (@nil B) = [].
Proof.
  induction l; simpl; auto.
Qed.
Hint Rewrite @combine_nil_r.

Lemma update_state_st_rebase_eq_ext :
  forall l1 l2 s1 s2,
    length l1 = length l2
    -> update_state_st_rebase s1 s2 l1 l2
       = update_state_st_ext_rebase s1 s2 l1 l2.
Proof.
  unfold update_state_st_ext_rebase; induction l1; introv len; simpl in *.
  { destruct l2; simpl in *; ginv. }
  { destruct l2; simpl in *; ginv.
    rewrite IHl1; clear IHl1; auto.
    apply functional_extensionality; introv; simpl.
    unfold upd_state; simpl.
    repeat (dest_cases w); ginv; simpl in *; tcsp.
    { apply not_or in n; repnd; tcsp. }
    { apply not_or in n0; repnd; tcsp. }
  }
Qed.

Lemma update_state_st_app_not_in :
  forall l s1 s2 v,
    ~ In v l
    -> update_state_st s1 s2 l v
       = s1 v.
Proof.
  induction l; simpl; introv i; auto.
  apply not_or in i; repnd.
  rewrite upd_state_diff;[|intro xx; inversion xx; tcsp]; auto.
Qed.

Lemma update_state_st_upd_state_not_in :
  forall s1 s2 v r l,
    ~In v l
    -> update_state_st s1 (upd_state s2 v r) l = update_state_st s1 s2 l.
Proof.
  induction l; introv i; simpl in *; auto.
  apply not_or in i; repnd.
  rewrite upd_state_diff;[|introv xx; inversion xx; tcsp];[].
  f_equal; auto.
Qed.

Lemma update_state_st_rebase_upd_state_not_in :
  forall s1 s2 v r l l',
    ~In v l'
    -> update_state_st_rebase (upd_state s1 v r) s2 l l'
       = upd_state (update_state_st_rebase s1 s2 l l') v r.
Proof.
  induction l as [|v1 l1 ind]; introv ni; simpl in *; auto.
  destruct l' as [|v2 l2]; simpl in *; auto.
  apply not_or in ni; repnd.
  rewrite upd_state_swap; dest_cases w;[].
  f_equal; auto.
Qed.

Lemma update_state_st_rebase_upd_state_right_not_in :
  forall v l1 l2 s1 s2 t,
    ~ In v l1
    -> update_state_st_rebase s1 (upd_state s2 v t) l1 l2
       = update_state_st_rebase s1 s2 l1 l2.
Proof.
  induction l1; simpl; tcsp; introv ni.
  apply not_or in ni; repnd.
  destruct l2; simpl; auto.
  rewrite (upd_state_diff s2 v t); [|introv xx; inversion xx; tcsp];[].
  rewrite IHl1; auto.
Qed.

Lemma update_state_st_rebase_app_not_in :
  forall s1 s2 l1 l2 v,
    ~In v l2
    -> update_state_st_rebase s1 s2 l1 l2 v
       = s1 v.
Proof.
  induction l1 as [|v1 l1 ind]; introv ni; simpl; auto.
  destruct l2 as [|v2 l2]; simpl in *; auto.
  apply not_or in ni; repnd.
  rewrite upd_state_diff;[|intro xx; inversion xx; tcsp];[]; auto.
Qed.

(*
Fixpoint rename_list (l : list KVariable) (ren : renaming) : list KVariable :=
  match l with
  | [] => []
  | v :: l => rename_var v ren :: rename_list l ren
  end.
*)

(*
Definition is_renaming1 (l1 l2 : list KVariable) :=
  rename_list l1 (combine l1 l2) = l2.
*)

Lemma ite_KVariable_dec_same :
  forall {T} v (a b : T),
    (if KVariable_dec v v then a else b) = a.
Proof.
  introv; dest_cases w.
Qed.
Hint Rewrite @ite_KVariable_dec_same : core.

Hint Rewrite upd_state_var_twice : core.

Lemma is_renaming2_implies_length :
  forall l1 l2, is_renaming l1 l2 -> length l1 = length l2.
Proof.
  induction l1; simpl; introv isren;
    inversion isren; subst; simpl; auto.
Qed.

Lemma check_pair_ren_sym :
  forall v1 v2 l1 l2,
    check_pair_ren v1 v2 l1 l2
    -> check_pair_ren v2 v1 l2 l1.
Proof.
  introv chk.
  induction chk; auto.
Qed.

Lemma check_pair_ren_refl :
  forall v l, check_pair_ren v v l l.
Proof.
  induction l; auto.
  destruct (KAssignable_dec v a); subst.
  { apply check_pair_ren_cons_same; auto. }
  { apply check_pair_ren_cons_diff; auto. }
Qed.

Lemma is_renaming_sym :
  forall l1 l2, is_renaming l1 l2 -> is_renaming l2 l1.
Proof.
  induction l1; introv isren; inversion isren; subst; auto.
  constructor; auto.
  apply check_pair_ren_sym; auto.
Qed.

Lemma is_renaming_refl :
  forall l, is_renaming l l.
Proof.
  induction l; introv; auto.
  constructor; auto.
  apply check_pair_ren_refl; auto.
Qed.

Lemma check_pair_ren_in :
  forall v1 v2 l1 l2,
    check_pair_ren v1 v2 l1 l2
    -> (In v1 l1 <-> In v2 l2).
Proof.
  introv chk.
  induction chk; simpl; tcsp; split; intro h; repndors; tcsp.
  { rewrite IHchk in h; tcsp. }
  { rewrite <- IHchk in h; tcsp. }
Qed.

Lemma update_state_st_rebase_switch_if_in :
  forall s1 s2 v1 v2 t l1 l2,
    check_pair_ren v1 v2 l1 l2
    -> In v1 l1
    -> update_state_st_rebase s1 (upd_state s2 v1 t) l1 l2
       = upd_state (update_state_st_rebase s1 s2 l1 l2) v2 t.
Proof.
  induction l1; introv chk i; simpl in *; tcsp.

  inversion chk as [|? ? chk1|? ? ? ? diff1 diff2 chk1]; subst; clear chk.

  {
    clear i.
    autorewrite with core.

    destruct (in_dec KAssignable_dec a l1) as [d|d].

    {
      rewrite IHl1; auto.
      autorewrite with core; auto.
    }

    { rewrite update_state_st_rebase_upd_state_right_not_in; auto. }
  }

  {
    rewrite upd_state_swap.
    dest_cases w;[].
    rewrite upd_state_diff;[|intro xx; inversion xx; tcsp];[].
    repndors; subst; tcsp;[].
    rewrite IHl1; auto.
  }
Qed.

Lemma upd_state_update_state_st_rebase_left_if_in :
  forall l2 v1 v2 l1 s s1,
    check_pair_ren v1 v2 l1 l2
    -> In v1 l1
    -> upd_state (update_state_st_rebase s1 s l2 l1) v1 (s v2)
       = update_state_st_rebase s1 s l2 l1.
Proof.
  induction l2; simpl; introv chk i.

  { inversion chk; subst; simpl in *; tcsp. }

  { inversion chk as [|? ? chk1|? ? ? ? diff1 diff2 chk1]; subst; clear chk; simpl in *.

    { clear i.
      autorewrite with core; auto. }

    { repndors; subst; autorewrite with core; tcsp.
      rewrite upd_state_swap.
      dest_cases w;[].
      f_equal; auto. }
  }
Qed.

Lemma update_state_st_rebase_update_state_left_if_in2 :
  forall l2 v1 l1 s s1 t,
    is_renaming l2 l1
    -> In v1 l1
    -> update_state_st_rebase (upd_state s1 v1 t) s l2 l1
       = update_state_st_rebase s1 s l2 l1.
Proof.
  induction l2; introv isren i; simpl in *.

  { inversion isren; subst; simpl in *; tcsp. }

  { inversion isren as [|? ? ? ? chk isren2]; subst; clear isren; simpl in *.

    repndors; subst.

    { destruct (in_dec KAssignable_dec v1 l3) as [d|d].

      { rewrite IHl2; auto. }

      { rewrite update_state_st_rebase_upd_state_not_in; auto.
        autorewrite with core; auto. }
    }

    { rewrite IHl2; auto. }
  }
Qed.

Lemma partial_derive_change_list :
  forall l1 l2 s1 s2 F,
    is_renaming l1 l2
    -> partial_derive F l1 s1
       = partial_derive
           (fun s => F (update_state_st_rebase s1 s l2 l1)) l2
           (update_state_st_rebase s2 s1 l1 l2).
Proof.
  induction l1 as [|v1 l1 ind]; simpl; introv isren.

  { inversion isren; subst; simpl; auto. }

  { inversion isren as [|? ? ? ? chk isr]; subst; clear isren; simpl.
    autorewrite with core.
    apply Derive_ext; introv.
    autorewrite with core.

    assert ({~ In v2 l3} + {In v2 l3})
      as d
        by (destruct (in_dec KAssignable_dec v2 l3) as [d|d]; tcsp).
    destruct d as [d|d].

    {
      assert (~ In v1 l1) as d2.
      { intro xx.
        eapply check_pair_ren_in in xx;[|apply check_pair_ren_sym;eauto]; tcsp. }

      repeat (rewrite partial_derive_st_add_upd; auto;[]).
      rewrite (ind l3 s1 s2); auto.
      apply partial_derive_st_ext; introv.
      autorewrite with core.
      rewrite update_state_st_rebase_upd_state_right_not_in; auto.
    }

    {
      assert (In v1 l1) as d2.
      { eapply check_pair_ren_in;eauto. }
      rewrite (ind l3 _ s2); auto.
      rewrite (update_state_st_rebase_switch_if_in _ _ _ v2); auto.

      (* do that now? *)
      apply partial_derive_st_ext; introv.
      f_equal.
      rewrite upd_state_update_state_st_rebase_left_if_in; auto.
      rewrite update_state_st_rebase_update_state_left_if_in2; auto.
      apply is_renaming_sym; auto.
    }
  }
Qed.

Lemma upd_state_update_state_st_apply_if_in :
  forall s s1 v l,
    In v l
    -> upd_state (update_state_st s s1 l) v (s1 v)
       = update_state_st s s1 l.
Proof.
  induction l; introv i; simpl in *; tcsp.
  repndors; subst; simpl in *; autorewrite with core; auto;[].
  rewrite upd_state_swap.
  dest_cases w.
  rewrite IHl; auto.
Qed.

Lemma update_state_st_upd_state_swap_if_not_in :
  forall l s1 s2 v t,
    ~ In v l
    -> update_state_st (upd_state s1 v t) s2 l
       = upd_state (update_state_st s1 s2 l) v t.
Proof.
  induction l; introv i; simpl in *; tcsp.
  apply not_or in i; repnd.
  rewrite upd_state_swap; dest_cases w; GC;[].
  rewrite IHl; auto.
Qed.

Definition equal_states_except_vars (s1 s2 : state) (vs : list KVariable) : Prop :=
  forall x : KAssignable, assign_in_vars x vs = false -> s1 x = s2 x.

Lemma equal_states_except_vars_nil_implies_eq :
  forall s1 s2, equal_states_except_vars s1 s2 [] -> s1 = s2.
Proof.
  introv equ.
  apply functional_extensionality; introv.
  apply equ.
  destruct x; simpl; auto.
Qed.

Lemma update_state_st_same :
  forall s l, update_state_st s s l = s.
Proof.
  induction l; introv; simpl; auto.
  rewrite IHl; clear IHl.
  apply upd_state_ext.
Qed.

Lemma update_state_st_upd_state_if_in :
  forall s1 s2 v t l,
    In v l
    -> update_state_st (upd_state s1 v t) s2 l
       = update_state_st s1 s2 l.
Proof.
  induction l; introv i; simpl in *; tcsp.
  repndors; subst; autorewrite with core.

  { destruct (in_dec KAssignable_dec v l) as [d|d].

    { rewrite IHl; auto. }

    { rewrite update_state_st_upd_state_swap_if_not_in; auto.
      autorewrite with core; auto. }
  }

  { rewrite IHl; auto. }
Qed.

(* generalize that *)
Lemma partial_derive_st_update_state_st_fst_ss :
  forall l2 s1 s2 l1 l3 F,
    is_renaming l1 l2
    -> subset l2 l3
    -> partial_derive (F s1) l2 (update_state_st_rebase s1 s2 l1 l2)
       = partial_derive
           (fun s => F (update_state_st s s1 l3) s)
           l2
           (update_state_st_rebase s1 s2 l1 l2).
Proof.
  induction l2; introv isren ss; simpl.

  { inversion isren; subst; simpl in *; auto.
    rewrite update_state_st_same; auto.
  }

  { inversion isren as [|? ? ? ? chk isren2]; clear isren; subst; simpl in *.
    apply Derive_ext; introv.
    autorewrite with core.
    apply subset_cons_l in ss; repnd.

    destruct (in_dec KAssignable_dec a l2) as [d|d].

    {
      assert (In v1 l0) as d2.
      { eapply check_pair_ren_in;eauto. }
      erewrite <- update_state_st_rebase_switch_if_in;[|eauto|]; auto.
    }

    {
      assert (~In v1 l0) as d2.
      { intro xx;eapply check_pair_ren_in in xx;[|apply check_pair_ren_sym];eauto. }
      rewrite partial_derive_st_add_upd; auto.

      pose proof (IHl2 s1 s2 l0 l3 (fun s1 s => F s1 (upd_state s a t))) as q.
      clear IHl2; simpl in q; rewrite q; auto; clear q.

      rewrite partial_derive_st_add_upd; auto.

      apply partial_derive_st_ext; introv.
      rewrite update_state_st_upd_state_if_in; auto.
    }
  }
Qed.

(* generalize that *)
Lemma partial_derive_st_update_state_st_fst :
  forall s1 s2 l1 l2 F,
    is_renaming l1 l2
    -> partial_derive (F s1) l2 (update_state_st_rebase s1 s2 l1 l2)
       = partial_derive
           (fun s => F (update_state_st s s1 l2) s)
           l2
           (update_state_st_rebase s1 s2 l1 l2).
Proof.
  introv isren.
  apply partial_derive_st_update_state_st_fst_ss; auto.
Qed.

Lemma partial_derive_st_second_rebase :
  forall l2 l2' s1 s2 F,
    is_renaming l2 l2'
    -> partial_derive (fun s : state => F s1 s) l2 s2
       = partial_derive
           (fun s => F (update_state_st s s1 l2')
                       (update_state_st_rebase s2 s l2' l2))
           l2'
           (update_state_st_rebase s1 s2 l2 l2').
Proof.
  introv isren.
  rewrite (partial_derive_change_list l2 l2' s2 s1); auto.
  pose proof (partial_derive_st_update_state_st_fst
                s1 s2 l2 l2'
                (fun s1 s => F s1 (update_state_st_rebase s2 s l2' l2))) as h.
  simpl in h.
  rewrite h; auto.
Qed.

Lemma update_state_st_rebase_app_eq_if_not_in :
  forall s1 s2 l1 l2 v,
    ~ In v l2
    -> update_state_st_rebase s1 s2 l1 l2 v = s1 v.
Proof.
  induction l1; introv i; simpl in *; auto.
  destruct l2; auto.
  simpl in *.
  apply not_or in i; repnd.
  rewrite upd_state_diff;[auto|intro xx; inversion xx; tcsp].
Qed.

(*
   l2' has to be disjoint from l1: [disjoint l2' l1]
   but also has the same repetitions as l2: [is_renaming l2 l2'].
 *)
Lemma partial_derive_st_combine :
  forall l1 l2 l2' s1 s2 F,
    disjoint l2' l1
    -> is_renaming l2 l2'
    -> partial_derive
         (fun s1 => partial_derive (fun s2 => F s1 s2) l2 s2)
         l1
         s1
       = partial_derive
           (fun s => F (update_state_st s s1 l2')
                       (update_state_st_rebase s2 s l2' l2))
           (l1 ++ l2')
           (update_state_st_rebase s1 s2 l2 l2').
Proof.
  induction l1; introv disj isren; simpl.

  { clear disj.
    apply partial_derive_st_second_rebase; auto. }

  { apply disjoint_cons_r in disj; repnd.
    rewrite update_state_st_rebase_app_eq_if_not_in; auto.
    apply Derive_ext; introv.
    rewrite (IHl1 _ l2'); auto.

    rewrite update_state_st_rebase_upd_state_not_in; auto.
    apply partial_derive_st_ext; introv.
    rewrite update_state_st_upd_state_not_in; auto.
  }
Qed.

Lemma partial_derive_st_combine2 :
  forall l2 l1 l1' s1 s2 F,
    disjoint l1' l2
    -> is_renaming l1 l1'
    -> partial_derive
         (fun s1 => partial_derive (fun s2 => F s1 s2) l2 s2)
         l1
         s1
       = partial_derive
           (fun s => F (update_state_st_rebase s1 s l1' l1)
                       (update_state_st s s2 l1'))
           (l1' ++ l2)
           (update_state_st_rebase s2 s1 l1 l1').
Proof.
  induction l2 using list_ind_snoc; introv disj isren;
    simpl in *; autorewrite with core.

  { rewrite (partial_derive_st_second_rebase l1 l1' s2 s1 (fun a b => F b a)); auto. }

  { apply disjoint_snoc_r in disj; repnd.
    erewrite partial_derive_st_ext;
      [|introv;apply partial_derive_st_S; autorewrite with core; omega].
    autorewrite with core.
    rewrite (IHl2 l1 l1'); auto;[].
    rewrite app_snoc.

    symmetry.
    rewrite partial_derive_st_S;autorewrite with core; try omega.
    symmetry.
    apply partial_derive_st_ext; introv.
    rewrite update_state_st_app_not_in; auto.
    apply Derive_ext; introv.
    rewrite update_state_st_rebase_upd_state_right_not_in; auto.
    rewrite update_state_st_upd_state_swap_if_not_in; auto. }
Qed.

Lemma update_state_st_rebase_cancel :
  forall s1 s2 l1 l2,
    is_renaming l1 l2
    -> update_state_st_rebase s1 (update_state_st_rebase s2 s1 l1 l2) l2 l1
       = s1.
Proof.
  induction l1; introv isren; simpl.

  { inversion isren; subst; simpl; auto. }

  { inversion isren as [|? ? ? ? chk isren1]; subst; clear isren; simpl.
    autorewrite with core.

    destruct (in_dec KAssignable_dec v2 l3) as [i|i].

    { assert (In a l1) as j.
      { eapply check_pair_ren_in;eauto. }

      rewrite upd_state_update_state_st_rebase_left_if_in; auto;
        [|apply check_pair_ren_sym;auto].
      rewrite IHl1; auto.
      apply upd_state_ext. }

    { assert (~In a l1) as d2.
      { intro xx;eapply check_pair_ren_in in xx;[|apply check_pair_ren_sym];eauto. }
      rewrite <- update_state_st_rebase_upd_state_not_in; auto.
      rewrite update_state_st_rebase_upd_state_right_not_in; auto.
      rewrite upd_state_ext.
      rewrite IHl1; auto. }
  }
Qed.

Lemma update_state_st_rebase_app_in :
  forall s1 s2 l1 l2 v1 v2,
    check_pair_ren v1 v2 l1 l2
    -> In v2 l2
    -> update_state_st_rebase s1 s2 l1 l2 v2
       = s2 v1.
Proof.
  induction l1; introv chk i; simpl; auto.
  { inversion chk; subst; simpl in *; tcsp. }

  inversion chk as [|? ? chk2|? ? ? ? diff1 diff2 chk2];
    subst; clear chk; autorewrite with core; auto.
  simpl in *; repndors; subst; tcsp.
  rewrite upd_state_diff;[|intro xx;inversion xx;tcsp].
  apply IHl1; auto.
Qed.

Inductive is_sub_renaming :
  list KAssignable
  -> list KAssignable
  -> list KAssignable
  -> list KAssignable
  -> Prop :=
| is_sub_renaming_nil :
    forall l1 l2,
      is_renaming l1 l2
      -> is_sub_renaming [] [] l1 l2
| is_sub_renaming_in :
    forall v1 v2 sl1 sl2 l1 l2,
      check_pair_ren v1 v2 l1 l2
      -> is_sub_renaming sl1 sl2 l1 l2
      -> is_sub_renaming (v1 :: sl1) (v2 :: sl2) (v1 :: l1) (v2 :: l2)
| is_sub_renaming_out :
    forall v1 v2 sl1 sl2 l1 l2,
      check_pair_ren v1 v2 l1 l2
      -> is_sub_renaming sl1 sl2 l1 l2
      -> is_sub_renaming sl1 sl2 (v1 :: l1) (v2 :: l2).
Hint Constructors is_sub_renaming.

Lemma check_pair_ren_is_sub_renaming_implies :
  forall v1 v2 sl1 sl2 l1 l2,
    is_sub_renaming sl1 sl2 l1 l2
    -> check_pair_ren v1 v2 l1 l2
    -> check_pair_ren v1 v2 sl1 sl2.
Proof.
  introv isren.
  induction isren; introv chk; auto;
    inversion chk; subst; auto.
Qed.

Lemma is_sub_renaming_implies :
  forall sl1 sl2 l1 l2,
    is_sub_renaming sl1 sl2 l1 l2
    ->
    (
      sublist sl1 l1
      /\
      sublist sl2 l2
      /\
      is_renaming sl1 sl2
      /\
      is_renaming l1 l2
    ).
Proof.
  introv isren.
  induction isren; repnd; dands; auto.
  constructor; auto.
  eapply check_pair_ren_is_sub_renaming_implies; eauto.
Qed.

Lemma is_sub_renaming_implies_is_rename :
  forall sl1 sl2 l1 l2,
    is_sub_renaming sl1 sl2 l1 l2
    -> is_renaming l1 l2.
Proof.
  introv isren.
  apply is_sub_renaming_implies in isren; tcsp.
Qed.
Hint Resolve is_sub_renaming_implies_is_rename : core.

(* generalization of [partial_derive_change_list] to sublists *)
Lemma partial_derive_change_list_sublist :
  forall l1 l2 sl1 sl2 s1 s2 F,
    is_sub_renaming sl1 sl2 l1 l2
    -> partial_derive F sl1 s1
       = partial_derive
           (fun s => F (update_state_st_rebase s1 s l2 l1)) sl2
           (update_state_st_rebase s2 s1 l1 l2).
Proof.
  induction l1 as [|v1 l1 ind]; simpl; introv isren.

  { inversion isren as [? ? isren2| |]; clear isren; subst; simpl; auto.
    inversion isren2; subst; clear isren2; simpl; auto. }

  { inversion isren as [? ? isren1|? ? ? ? ? ? chk1 isr1|? ? ? ? ? ? chk isren1];
      subst; clear isren; simpl.

    { inversion isren1 as [|? ? ? ? chk isren]; subst; clear isren1; simpl.

      destruct (in_dec KAssignable_dec v1 l1) as [d|d].

      { assert (In v2 l3) as j.
        { eapply check_pair_ren_in;[apply check_pair_ren_sym;eauto|];auto. }
        simpl.
        rewrite upd_state_update_state_st_rebase_left_if_in; auto.
        rewrite upd_state_update_state_st_rebase_left_if_in; auto;
          [|apply check_pair_ren_sym;auto].
        rewrite update_state_st_rebase_cancel; auto. }

      { assert (~In v2 l3) as d2.
        { intro xx;eapply check_pair_ren_in in xx;eauto. }
        rewrite update_state_st_rebase_upd_state_right_not_in; auto.
        rewrite update_state_st_rebase_cancel; auto.
        rewrite <- update_state_st_rebase_upd_state_not_in; auto.
        rewrite update_state_st_rebase_app_eq_if_not_in; auto.
        autorewrite with core.
        rewrite upd_state_ext; auto. }
    }

    { autorewrite with core.
      apply Derive_ext; introv.
      autorewrite with core.

      assert ({~ In v2 l3} + {In v2 l3})
        as d
          by (destruct (in_dec KAssignable_dec v2 l3) as [d|d]; tcsp).
      destruct d as [d|d].

      {
        assert (~ In v1 l1) as d2.
        { intro xx.
          eapply check_pair_ren_in in xx;[|apply check_pair_ren_sym;eauto]; tcsp. }

        assert (sublist sl0 l1) as sub1.
        { pose proof (is_sub_renaming_implies sl0 sl3 l1 l3) as q; tcsp. }

        assert (~ In v1 sl0) as d3.
        { intro xx; destruct d2; eapply sublist_in_implies; eauto. }

        assert (sublist sl3 l3) as sub3.
        { pose proof (is_sub_renaming_implies sl0 sl3 l1 l3) as q; tcsp. }

        assert (~ In v2 sl3) as d4.
        { intro xx; destruct d; eapply sublist_in_implies; eauto. }

        repeat (rewrite partial_derive_st_add_upd; auto;[]).

        rewrite (ind l3 sl0 sl3 s1 s2); auto.
        apply partial_derive_st_ext; introv.
        autorewrite with core.
        rewrite update_state_st_rebase_upd_state_right_not_in; auto.
      }

      {
        assert (In v1 l1) as d2.
        { eapply check_pair_ren_in;eauto. }

        rewrite (ind l3 sl0 sl3 _ s2); auto.
        rewrite (update_state_st_rebase_switch_if_in _ _ _ v2); auto.

        assert (is_renaming l3 l1) as isren.
        { apply is_renaming_sym;
            pose proof (is_sub_renaming_implies sl0 sl3 l1 l3) as q;
            tcsp. }

        apply partial_derive_st_ext; introv.
        f_equal.
        rewrite upd_state_update_state_st_rebase_left_if_in; auto.
        rewrite update_state_st_rebase_update_state_left_if_in2; auto.
      }
    }

    {
      assert (sublist sl2 l3) as sub1.
      { pose proof (is_sub_renaming_implies sl1 sl2 l1 l3) as q; tcsp. }

      destruct (in_dec KAssignable_dec v2 l3) as [i|i].

      { assert (In v1 l1) as k.
        { eapply check_pair_ren_in;eauto. }

        rewrite upd_state_update_state_st_rebase_left_if_in; auto;
          [|apply check_pair_ren_sym;auto].
        rewrite (ind l3 sl1 sl2 _ s2); auto.
        apply partial_derive_st_ext; introv.

        rewrite upd_state_update_state_st_rebase_left_if_in; auto.
      }

      { assert (~ In v2 sl2) as j.
        { intro xx; destruct i; eapply sublist_in_implies; eauto. }

        assert (~ In v1 l1) as k.
        { intro xx;eapply check_pair_ren_in in xx;[|apply check_pair_ren_sym];eauto. }

        rewrite partial_derive_st_add_upd; auto.
        rewrite (ind l3 sl1 sl2 _ s2); auto.
        apply partial_derive_st_ext; introv.
        autorewrite with core.
        rewrite update_state_st_rebase_upd_state_right_not_in; auto.
        rewrite <- update_state_st_rebase_upd_state_not_in; auto.
        rewrite upd_state_ext; auto.
      }
    }
  }
Qed.

Lemma update_state_st_update_state_st_rebase_subset :
  forall s1 s2 l1 l2 l3,
    subset l2 l3
    -> update_state_st (update_state_st_rebase s1 s2 l1 l2) s1 l3
       = s1.
Proof.
  induction l1; introv ss; simpl.
  { rewrite update_state_st_same; auto. }
  { destruct l2.
    { rewrite update_state_st_same; auto. }
    { rewrite update_state_st_upd_state_if_in;[|apply ss;simpl;tcsp].
      apply IHl1; introv i; apply ss; simpl; tcsp. }
  }
Qed.

Lemma check_pair_ren_same_left_implies :
  forall la1 la2 lb1 lb2 v1 v2 v,
    Datatypes.length la1 = Datatypes.length lb1
    -> check_pair_ren v1 v2 (la1 ++ v1 :: la2) (lb1 ++ v :: lb2)
    -> v2 = v.
Proof.
  induction la1; simpl; introv len chk.

  { destruct lb1; simpl in *; ginv.
    inversion chk; subst; tcsp. }

  { destruct lb1; simpl in *; ginv.
    inversion chk; subst; simpl in *; clear chk.

    { eapply IHla1;[|eauto]; auto. }

    { eapply IHla1;[|eauto]; auto. }
  }
Qed.

Lemma check_pair_ren_same_right_implies :
  forall la1 la2 lb1 lb2 v1 v2 v,
    Datatypes.length la1 = Datatypes.length lb1
    -> check_pair_ren v1 v2 (la1 ++ v :: la2) (lb1 ++ v2 :: lb2)
    -> v1 = v.
Proof.
  induction la1; simpl; introv len chk.

  { destruct lb1; simpl in *; ginv.
    inversion chk; subst; tcsp. }

  { destruct lb1; simpl in *; ginv.
    inversion chk; subst; simpl in *; clear chk.

    { eapply IHla1;[|eauto]; auto. }

    { eapply IHla1;[|eauto]; auto. }
  }
Qed.

Lemma is_renaming_member_implies_check_pair_ren :
  forall la1 la2 lb1 lb2 v1 v2,
    is_renaming (la1 ++ v1 :: la2) (lb1 ++ v2 :: lb2)
    -> length la1 = length lb1
    -> check_pair_ren v1 v2 (la1 ++ v1 :: la2) (lb1 ++ v2 :: lb2).
Proof.
  induction la1; introv isren len; simpl in *.

  { destruct lb1; simpl in *; ginv.
    inversion isren; subst; clear isren.
    constructor; auto. }

  { destruct lb1; simpl in *; ginv.
    inversion isren; subst; clear isren.
    destruct (KAssignable_dec v1 a) as [d|d]; subst.

    { assert (k = v2) as xx.
      { eapply check_pair_ren_same_left_implies;[|eauto]; auto. }
      subst.
      constructor; auto. }

    { assert (k <> v2) as xx.
      { intro xx; subst; destruct d; symmetry;
          eapply check_pair_ren_same_right_implies;[|eauto]; auto. }
      constructor; auto. }
  }
Qed.

Lemma is_sub_renaming_cons_lr :
  forall (l1 l2 sl1 sl2 : list KAssignable) v1 v2,
    is_sub_renaming (v1 :: sl1) (v2 :: sl2) l1 l2
    -> is_sub_renaming sl1 sl2 l1 l2.
Proof.
  induction l1; introv isren.

  { inversion isren. }

  { inversion isren as [|? ? ? ? ? ? chk isren1|? ? ? ? ? ? chk isren1];
      subst; clear isren.

    { constructor; auto. }

    { apply IHl1 in isren1.
      constructor; auto. }
  }
Qed.

Lemma is_sub_renaming_cons_snd :
  forall (l1 l2 sl1 sl2 : list KAssignable) v,
    is_sub_renaming sl1 (v :: sl2) l1 l2
    <->
    exists w l la1 la2 lb1 lb2,
      sl1 = w :: l
      /\ l1 = app la1 (w :: la2)
      /\ l2 = app lb1 (v :: lb2)
      /\ length la1 = length lb1
      /\ check_pair_ren w v la2 lb2
      /\ check_pair_ren w v l1 l2
      /\ is_sub_renaming l sl2 la2 lb2
      /\ is_renaming l1 l2.
Proof.
  induction l1; introv; simpl; split; intro h; exrepnd; subst; ginv.

  { inversion h. }

  { destruct la1; ginv. }

  { inversion h as [|? ? ? ? ? ? chk isren|? ? ? ? ? ? chk isren]; subst; clear h.

    { exists a sl0 (@nil KAssignable) l1 (@nil KAssignable) l3; simpl; dands; auto.
      constructor; auto.
      pose proof (is_sub_renaming_implies sl0 sl2 l1 l3) as q; tcsp. }

    { apply IHl1 in isren; exrepnd; subst; clear IHl1.

      exists w l (a :: la1) la2 (v2 :: lb1) lb2; simpl; dands; auto;

      destruct (KAssignable_dec w a) as [d|d]; subst.

      { assert (v2 = v) as xx.
        { eapply check_pair_ren_same_left_implies;[|eauto]; auto. }
        subst.
        constructor; auto. }

      { assert (v2 <> v) as xx.
        { intro xx; subst; destruct d; symmetry;
            eapply check_pair_ren_same_right_implies;[|eauto]; auto. }
        constructor; auto. }
    }
  }

  { destruct la1; simpl in *; ginv.

    { destruct lb1; simpl in *; ginv. }

    { destruct lb1; simpl in *; ginv.
      inversion h1; subst.
      apply is_sub_renaming_out; auto.
      apply IHl1; clear IHl1.
      exists w l la1 la2 lb1 lb2; dands; auto.
      inversion h6; subst; auto.
    }
  }
Qed.

(* generalize that *)
Lemma partial_derive_st_update_state_st_fst_ss_sublist :
  forall sl2 sl1 l2 s1 s2 l1 l3 F,
    is_sub_renaming sl1 sl2 l1 l2
    -> subset l2 l3
    -> partial_derive (F s1) sl2 (update_state_st_rebase s1 s2 l1 l2)
       = partial_derive
           (fun s => F (update_state_st s s1 l3) s)
           sl2
           (update_state_st_rebase s1 s2 l1 l2).
Proof.
  induction sl2; introv isren ss; simpl.

  { rewrite update_state_st_update_state_st_rebase_subset; auto. }

  { apply Derive_ext; introv.

    applydup is_sub_renaming_cons_snd in isren as q; exrepnd.

    assert (check_pair_ren w a l1 l2) as chk.
      { subst; apply is_renaming_member_implies_check_pair_ren; auto. }

    destruct (in_dec KAssignable_dec a l2) as [i|i].

    { assert (In w l1) as d2.
      { eapply check_pair_ren_in;eauto. }
      erewrite <- update_state_st_rebase_switch_if_in;[|eauto|]; auto.
      apply (IHsl2 l); auto.
      subst sl1; eapply is_sub_renaming_cons_lr;eauto.
    }

    { subst l2.
      destruct i.
      apply in_app_iff; simpl; tcsp.
    }
  }
Qed.

(* generalize that *)
Lemma partial_derive_st_update_state_st_fst_sublist :
  forall s1 s2 sl1 sl2 l1 l2 F,
    is_sub_renaming sl1 sl2 l1 l2
    -> partial_derive (F s1) sl2 (update_state_st_rebase s1 s2 l1 l2)
       = partial_derive
           (fun s => F (update_state_st s s1 l2) s)
           sl2
           (update_state_st_rebase s1 s2 l1 l2).
Proof.
  introv isren.
  eapply partial_derive_st_update_state_st_fst_ss_sublist; eauto.
Qed.

Lemma partial_derive_st_second_rebase_sublist :
  forall l2 l2' sl2 sl2' s1 s2 F,
    is_sub_renaming sl2 sl2' l2 l2'
    -> partial_derive (fun s : state => F s1 s) sl2 s2
       = partial_derive
           (fun s => F (update_state_st s s1 l2')
                       (update_state_st_rebase s2 s l2' l2))
           sl2'
           (update_state_st_rebase s1 s2 l2 l2').
Proof.
  introv isren.
  assert ((fun s => F s1 s) = F s1) as h by auto; rewrite h; clear h.
  rewrite (partial_derive_change_list_sublist l2 l2' sl2 sl2' s2 s1 (F s1)); auto.

  pose proof (partial_derive_st_update_state_st_fst_sublist
                s1 s2 sl2 sl2' l2 l2'
                (fun s1 s => F s1 (update_state_st_rebase s2 s l2' l2))) as h.
  simpl in h.
  rewrite h; auto.
Qed.

(*
   Shouldn't [partial_derive_st_combine] be also true when we only
   derive sublists of [l1] and [l2]/[l2'] (a generalization)?
 *)
Lemma partial_derive_st_combine_sublist :
  forall l1 l2 l2' sl1 sl2 sl2' s1 s2 F,
    disjoint l2' l1
    -> sublist sl1 l1
    -> is_sub_renaming sl2 sl2' l2 l2'
    -> partial_derive
         (fun s1 => partial_derive (fun s2 => F s1 s2) sl2 s2)
         sl1
         s1
       = partial_derive
           (fun s => F (update_state_st s s1 l2')
                       (update_state_st_rebase s2 s l2' l2))
           (sl1 ++ sl2')
           (update_state_st_rebase s1 s2 l2 l2').
Proof.
  induction sl1; introv disj sub isren; simpl.

  { clear sub.
    apply partial_derive_st_second_rebase_sublist; auto. }

  { (*apply disjoint_cons_r in disj; repnd.*)
    assert (In a l1) as i.
    { eapply sublist_in_implies;[exact sub|]; simpl; auto. }
    assert (~ In a l2') as d.
    { intro j; apply disj in j; tcsp. }
    assert (sublist sl1 l1) as sub2.
    { apply sublist_cons_l in sub; exrepnd; subst.
      apply sublist_app_r_weak; auto. }

    rewrite update_state_st_rebase_app_eq_if_not_in; auto.
    apply Derive_ext; introv.
    rewrite (IHsl1 _ sl2'); auto.

    rewrite update_state_st_rebase_upd_state_not_in; auto.
    apply partial_derive_st_ext; introv.
    rewrite update_state_st_upd_state_not_in; auto.
  }
Qed.

Lemma update_state_st_app_in :
  forall l s1 s2 v,
    In v l
    -> update_state_st s1 s2 l v
       = s2 v.
Proof.
  induction l; introv i; simpl in *; tcsp.
  repndors; subst; autorewrite with core; auto.

  destruct (in_dec KAssignable_dec a l) as [d|d].

  { rewrite upd_state_update_state_st_apply_if_in; auto. }

  { rewrite <- update_state_st_upd_state_swap_if_not_in; auto. }
Qed.

Lemma update_state_st_right_same :
  forall s1 s2 s3 l,
    update_state_st s1 (update_state_st s2 s3 l) l
    = update_state_st s1 s3 l.
Proof.
  induction l; simpl; auto.
  autorewrite with core.

  destruct (in_dec KAssignable_dec a l) as [d|d].

  { rewrite upd_state_update_state_st_apply_if_in; auto.
    rewrite IHl; auto. }

  { rewrite update_state_st_upd_state_not_in; auto.
    rewrite IHl; auto. }
Qed.
Hint Rewrite update_state_st_right_same : core.

Lemma update_state_st_rebase_update_state_st_left :
  forall l1 l2 s1 s2 s3,
    is_renaming l1 l2
    -> update_state_st_rebase (update_state_st s1 s2 l1) s3 l2 l1
       = update_state_st_rebase s1 s3 l2 l1.
Proof.
  induction l1; introv isren; simpl.

  { inversion isren; simpl; auto. }

  { inversion isren as [|? ? ? ? chk isren2]; subst; clear isren; simpl.

    destruct (in_dec KAssignable_dec a l1) as [d|d].

    { assert (In v2 l3) as d2.
      { eapply check_pair_ren_in;[apply check_pair_ren_sym|];eauto. }
      rewrite upd_state_update_state_st_apply_if_in; auto.
      rewrite IHl1; auto. }

    { rewrite update_state_st_rebase_upd_state_not_in; auto.
      rewrite IHl1; auto.
      autorewrite with core; auto. }
  }
Qed.

Lemma update_state_st_rebase_shadow :
  forall s1 s2 s3 l1 l2,
    is_renaming l1 l2
    -> update_state_st_rebase (update_state_st_rebase s1 s2 l1 l2) s3 l1 l2
       = update_state_st_rebase s1 s3 l1 l2.
Proof.
  induction l1; introv isren; simpl; auto.
  inversion isren as [|? ? ? ? chk isren2]; clear isren; subst.

  destruct (in_dec KAssignable_dec v2 l3) as [d|d].

  { repeat (rewrite upd_state_update_state_st_rebase_left_if_in;
            [|apply check_pair_ren_sym|];auto). }

  { rewrite update_state_st_rebase_upd_state_not_in; auto.
    autorewrite with core.
    rewrite IHl1; auto. }
Qed.

(*
  Similar to [partial_derive_st_combine] but for any state [s]:
 *)
Lemma partial_derive_st_uncombine :
  forall l1 l2 l2' sl1 sl2 sl2' s1 s2 s F,
    disjoint l2' l1
    -> sublist sl1 l1
    -> is_sub_renaming sl2 sl2' l2 l2'
    -> partial_derive
         (fun s => F (update_state_st s s1 l2')
                     (update_state_st_rebase s2 s l2' l2))
         (sl1 ++ sl2')
         s
       = partial_derive
           (fun s1 =>
              partial_derive
                (fun s2 => F s1 s2)
                sl2
                (update_state_st_rebase s2 s l2' l2))
           sl1
           (update_state_st s s1 l2').
Proof.
  induction sl1; introv disj sub isren; simpl.

  { clear sub.
    erewrite partial_derive_st_second_rebase_sublist;[|eauto].

    assert (is_renaming l2 l2') as isren2 by eauto with core.

    rewrite update_state_st_rebase_update_state_st_left;
      [|apply is_renaming_sym;auto].
    rewrite update_state_st_rebase_cancel;
      [|apply is_renaming_sym;auto].

    apply partial_derive_st_ext; introv.
    autorewrite with core.
    rewrite update_state_st_rebase_shadow; auto.
    apply is_renaming_sym; auto.
  }

  { assert (In a l1) as i.
    { eapply sublist_in_implies;[exact sub|]; simpl; auto. }
    assert (~ In a l2') as d.
    { intro xx; apply disj in xx; auto. }

    assert (sublist sl1 l1) as sub2.
    { apply sublist_cons_l in sub; exrepnd; subst.
      apply sublist_app_r_weak; constructor; auto. }

    rewrite update_state_st_app_not_in; auto;[].

    apply Derive_ext; introv.

    rewrite (IHsl1 sl2); auto;[].
    rewrite update_state_st_upd_state_swap_if_not_in; auto;[].

    apply partial_derive_st_ext; introv.
    rewrite update_state_st_rebase_upd_state_right_not_in; auto.
  }
Qed.


(*
Fixpoint vec_snoc {T n} (v : Vector.t T n) (x : T) : Vector.t T (S n) :=
  match v with
  | Vector.nil => Vector.cons _ x 0 (Vector.nil _)
  | Vector.cons h _ t => Vector.cons _ h _ (vec_snoc t x)
  end.
*)

(*
(* TODO: try to transform the dot update on interpretation to state update
   --- See [upd_interpretation_dots_as_upd_list_state].  I don't know how
   that will help though. *)
Lemma dynamic_semantics_term_diff:
  forall (t : Term) (I : interpretation) s1 l,
    ex_all_partial_derive_st
      (fun s : state => dynamic_semantics_term I (upd_state_st s1 s l) t).
Proof.
Abort.
*)

(*
Fixpoint partial_derive_st_vec (n : nat) :
  (Vector.t state (S n) -> R)
  -> list (list KAssignable)
  -> list state
  -> R :=
  match n with
  | 0 =>
    fun F Vs St =>
      match Vs, St with
      | l :: _, s :: _ =>
        partial_derive (fun s => F (Vector.cons _ s _ (Vector.nil _))) l s
      | _, _ => DumR
      end
  | S n =>
    fun F Vs St =>
      match Vs, St with
      | l :: ls, s :: ss =>
        partial_derive
          (fun x => partial_derive_st_vec n (fun v => F (Vector.cons _ x _ v)) ls ss)
          l s
      | _, _ => DumR
      end
  end.
*)

(*
Lemma partial_derive_st_vec_S :
  forall (n  : nat)
         (f  : Vector.t state (S (S n)) -> R)
         (Vs : list (list KAssignable))
         (St : list state),
    length Vs = S (S n)
    -> length St = S (S n)
    -> partial_derive_st_vec (S n) f Vs St
       = partial_derive_st_vec
           n
           (fun v : Vector.t state (S n) =>
              partial_derive
                (fun x : state => f (vec_snoc v x))
                (last Vs [])
                (last St DumState))
           (removelast Vs)
           (removelast St).
Proof.
  induction n; introv len1 len2.

  { repeat (destruct Vs; simpl in *; ginv).
    repeat (destruct St; simpl in *; ginv). }

  { match goal with
    | [ |- ?x = _ ] => remember x as r
    end.

    pose proof (snoc_cases Vs) as h; repndors.
    { subst; simpl in *; ginv. }
    exrepnd.
    rewrite h1.

    pose proof (snoc_cases St) as q; repndors.
    { subst; simpl in *; ginv. }
    exrepnd.
    rewrite q1.

    simpl.
    autorewrite with core.
    destruct k.

    { subst; simpl in *; ginv. }

    destruct k0.

    { subst; simpl in *; ginv. }

    erewrite partial_derive_st_ext;
      [|introv;
        pose proof (IHn (fun v => f (Vector.cons state s0 (S (S n)) v))
                        (snoc k a)
                        (snoc k0 a0)) as Q;
        autorewrite with core in Q;
        repeat (autodimp Q hyp);
        try (subst Vs St; simpl in *; autorewrite with core in *; omega);
        rewrite <- Q;
        reflexivity];[].

    subst; auto.
  }
Qed.

Lemma partial_derive_st_vec_ext :
  forall (n  : nat)
         (f g : Vector.t state (S n) -> R)
         (Vs : list (list KAssignable))
         (St : list state),
    (forall v, f v = g v)
    -> partial_derive_st_vec n f Vs St
       = partial_derive_st_vec n g Vs St.
Proof.
  induction n; introv h; simpl.

  { destruct Vs; auto.
    destruct St; auto.
    apply partial_derive_st_ext; auto. }

  { destruct Vs; auto.
    destruct St; auto.
    apply partial_derive_st_ext; introv.
    apply IHn; auto. }
Qed.
*)

(*
Definition ex_partial_derive_st_vec_l
           (n  : nat)
           (f  : Vector.t state (S n) -> R)
           (Vs : list (list KAssignable))
           (s  : state)
           (St : list state)
           (v  : KAssignable) :=
  ex_derive_R
    (fun X => partial_derive_st_vec n f Vs ((upd_state s v X) :: St))
    (s v).

Definition ex_all_partial_derive_st_vec (n : nat) (f : Vector.t state (S n) -> R) :=
  forall Vs s St v,
    length Vs = S n
    -> length St = n
    -> ex_partial_derive_st_vec_l n f Vs s St v.
*)

(*
Definition ex_all_le_partial_derive_st_vec (n : nat) (f : Vector.t state (S n) -> R) :=
  forall k (s : Vector.t state (n - k)) (lekn : k <= n),
    ex_all_partial_derive_st_vec
      k
      (fun v : Vector.t state (S k) => f (vec_app s v (vec_len_app1 lekn))).
*)

(*
Inductive ex_all_le_partial_derive_st_vec :
  forall (n : nat), (Vector.t state (S n) -> R) -> Prop :=
| PDV0 :
    forall f : Vector.t state 1 -> R,
      ex_all_partial_derive_st_vec 0 f
      -> ex_all_le_partial_derive_st_vec 0 f
| PDVS :
    forall n (f : Vector.t state (S (S n)) -> R),
      ex_all_partial_derive_st_vec (S n) f
      -> (forall s, ex_all_le_partial_derive_st_vec n (fun v : Vector.t state (S n) => f (Vector.cons _ s _ v)))
      -> ex_all_le_partial_derive_st_vec (S n) f.

Definition ex_partial_derive_st_vec_func {m : nat} (f : Vector.t R m -> R) :=
  forall (T  : Type)
         (d  : T) (* forall non-empty T *)
         (k  : nat)
         (ts : Vector.t T m)
         (G  : Vector.t state (S k) -> T -> R),
    (forall t, Vector.In t ts -> ex_all_le_partial_derive_st_vec k (fun s => G s t))
    -> ex_all_le_partial_derive_st_vec k (fun s => f (Vector.map (G s) ts)).

Lemma ex_all_le_partial_derive_st_vec_implies_ex_derive_partial_derive_st :
  forall (k  : nat)
         (L  : Vector.t state (S k) -> R)
         (v  : Vector.t state k)
         (st : state)
         (w  : KAssignable)
         (l  : list KAssignable),
    ex_all_le_partial_derive_st_vec k L
    -> ex_derive_R
         (fun X =>
            partial_derive
              (fun s => L (vec_snoc v s))
              l
              (upd_state st w X))
         (st w).
Proof.
  introv pd.
  revert v st w l.
  induction pd as [? eapd|? ? apd eapd ih]; introv.

  { simpl.
    apply Vector.case0 with (v := v).
    simpl; clear v.
    pose proof (eapd [l] st [] w) as q; simpl in q; repeat (autodimp q hyp). }

  { apply (Vector.caseS' v); clear v; introv; simpl.
    apply ih. }
Qed.
*)

(*
Lemma ex_all_partial_derive_st_vec_ext :
  forall (n  : nat)
         (f g : Vector.t state (S n) -> R),
    (forall v, f v = g v)
    -> ex_all_partial_derive_st_vec n f
    -> ex_all_partial_derive_st_vec n g.
Proof.
  introv e eapd len1 len2.
  pose proof (eapd Vs s St v len1 len2) as q; clear eapd.
  unfold ex_partial_derive_st_vec_l in *.
  eapply ex_derive_ext;[|exact q].
  simpl; introv.
  apply partial_derive_st_vec_ext; auto.
Qed.
*)

(*
Lemma ex_all_le_partial_derive_st_vec_ext :
  forall (n  : nat)
         (f g : Vector.t state (S n) -> R),
    (forall v, f v = g v)
    -> ex_all_le_partial_derive_st_vec n f
    -> ex_all_le_partial_derive_st_vec n g.
Proof.
  induction n; introv e eapd.

  { inversion eapd as [? pd|]; eqDepDec; subst; clear eapd.
    constructor.
    eapply ex_all_partial_derive_st_vec_ext; eauto. }

  { inversion eapd as [|? ? pd F]; clear eapd; eqDepDec; subst.
    constructor; auto.

    { eapply ex_all_partial_derive_st_vec_ext; eauto. }

    { introv.
      eapply IHn;[|apply F].
      simpl; auto. }
  }
Qed.
*)

(*
Lemma ex_all_le_partial_derive_st_vec_implies_vec_snoc :
  forall k (L : Vector.t state (S (S k)) -> R) l a,
    ex_all_le_partial_derive_st_vec (S k) L
    -> ex_all_le_partial_derive_st_vec
         k
         (fun v : Vector.t state (S k) =>
            partial_derive (fun s : state => L (vec_snoc v s)) l a).
Proof.
  induction k; introv pd.

  { constructor.
    introv len1 len2.
    repeat (destruct Vs; simpl in *; ginv).
    repeat (destruct St; simpl in *; ginv).
    unfold ex_partial_derive_st_vec_l; simpl.
    inversion pd as [|? ? eapd F]; clear pd; eqDepDec; subst.

    pose proof (eapd [l0,l] s [a] v) as q; clear eapd.
    simpl in q; repeat (autodimp q hyp). }

  { constructor.

    { introv len1 len2.
      inversion pd as [|? ? eapd F]; clear pd; eqDepDec; subst.
      clear F.
      pose proof (eapd (snoc Vs l) s (snoc St a) v) as q.
      autorewrite with core in q; repeat (autodimp q hyp).
      eapply ex_derive_ext;[|exact q].
      introv; cbv beta.
      rewrite <- snoc_cons.
      rewrite partial_derive_st_vec_S; autorewrite with core; auto.
      simpl; auto. }

    { introv.
      inversion pd as [|? ? eapd F]; clear pd; eqDepDec; subst.
      clear eapd.
      pose proof (F s) as q; clear F.
      apply (IHk _ l a) in q.
      simpl in *; auto. }
  }
Qed.

Lemma ex_all_le_partial_derive_st_vec_implies_all :
  forall k (L : Vector.t state (S k) -> R),
    ex_all_le_partial_derive_st_vec k L
    -> ex_all_partial_derive_st_vec k L.
Proof.
  destruct k; introv eapd; inversion eapd; eqDepDec; subst; auto.
Qed.

Lemma ex_all_le_partial_derive_st_vec_plus :
  forall {k} (L R : Vector.t state (S k) -> R),
    ex_all_le_partial_derive_st_vec k L
    -> ex_all_le_partial_derive_st_vec k R
    -> ex_all_le_partial_derive_st_vec k (fun v => (L v + R v)%R).
Proof.
  induction k; introv d1 d2.

  { inversion d1 as [? pd1|]; eqDepDec; subst; clear d1.
    inversion d2 as [? pd2|]; eqDepDec; subst; clear d2.
    constructor.
    introv len1 len2.
    repeat (destruct Vs; simpl; ginv).
    repeat (destruct St; simpl; ginv).
    unfold ex_partial_derive_st_vec_l.
    simpl in *.
    eapply (ex_all_partial_derive_st_plus
              (fun s0 => L (Vector.cons state s0 0 (Vector.nil state)))
              (fun s0 => R (Vector.cons state s0 0 (Vector.nil state))));[| |eauto].

    { introv len; subst.
      unfold ex_partial_derive_st_l; simpl.
      pose proof (pd1 [l0] st [] v0) as q; simpl in q.
      repeat (autodimp q hyp). }

    { introv len; subst.
      unfold ex_partial_derive_st_l; simpl.
      pose proof (pd2 [l0] st [] v0) as q; simpl in q.
      repeat (autodimp q hyp). }
  }

  { inversion d1 as [|? ? pd1 pdl1]; eqDepDec; subst.
    inversion d2 as [|? ? pd2 pdl2]; eqDepDec; subst.
    constructor.

    { introv len1 len2.

      eapply ex_derive_ext;
        [introv; symmetry;
         apply partial_derive_st_vec_S;simpl;auto
        |].

      destruct (snoc_cases St) as [h|h];[subst; simpl in *; ginv|];[].
      exrepnd; subst.
      eapply ex_derive_ext;
        [introv;rewrite <- snoc_cons;autorewrite with core;
         reflexivity|].
      destruct (snoc_cases Vs) as [h|h];[subst; simpl in *; ginv|];[].
      exrepnd; subst; autorewrite with core in *; simpl in *.

      eapply ex_derive_ext;
        [introv;symmetry;
         apply partial_derive_st_vec_ext; introv;
         apply partial_derive_st_plus
        |].

      { introv len len'; subst.
        unfold ex_partial_derive_st_l; simpl.
        apply ex_all_le_partial_derive_st_vec_implies_ex_derive_partial_derive_st; auto. }

      { introv len len'; subst.
        unfold ex_partial_derive_st_l; simpl.
        apply ex_all_le_partial_derive_st_vec_implies_ex_derive_partial_derive_st; auto. }

      { simpl.
        pose proof (IHk (fun v => partial_derive (fun s => L (vec_snoc v s)) a0 a)
                        (fun v => partial_derive (fun s => R (vec_snoc v s)) a0 a))
          as q; clear IHk.
        simpl in q.
        repeat (autodimp q hyp).

        { apply ex_all_le_partial_derive_st_vec_implies_vec_snoc; auto. }

        { apply ex_all_le_partial_derive_st_vec_implies_vec_snoc; auto. }

        { apply ex_all_le_partial_derive_st_vec_implies_all in q.
          apply (q k1 s k0 v); auto. }
      }
    }

    { introv; apply IHk; auto. }
  }
Qed.
*)

(*
Definition ex_all_partial_derive_st2 (f : state -> R) :=
  forall (s : state)
         (l : list KVariable)
         (v : KVariable),
    ex_derive_R
      (fun X =>
         partial_derive_st
    ex_partial_derive_st_l f s l v.

Definition ex_partial_derive_st_func2 {m : nat} (f : Vector.t R m -> R) :=
  forall (T  : Type)
         (d  : T) (* forall non-empty T *)
         (ts : Vector.t T m)
         (G  : state -> state -> T -> R),
    (forall t, Vector.In t ts -> ex_all_partial_derive_st (fun s1 s2 => G s1 s2 t))
    -> ex_all_partial_derive_st (fun s => f (Vector.map (G s) ts)).
 *)

(*
Lemma ex_all_le_partial_derive_st_vec_big_sum :
  forall k (F : Vector.t state (S k) -> KVariable -> R) l,
    (forall v, In v l -> ex_all_le_partial_derive_st_vec k (fun s => F s v))
    -> ex_all_le_partial_derive_st_vec k (fun s => big_sum l (F s)).
Proof.
Abort.

Lemma ex_all_le_partial_derive_st_vec_mult :
  forall {k} (L R : Vector.t state (S k) -> R),
    ex_all_le_partial_derive_st_vec k L
    -> ex_all_le_partial_derive_st_vec k R
    -> ex_all_le_partial_derive_st_vec k (fun v => (L v * R v)%R).
Proof.
Abort.

Lemma ex_all_le_partial_derive_st_vec_const :
  forall k c, ex_all_le_partial_derive_st_vec k (fun _ => c).
Proof.
Abort.
*)

Lemma partial_derive_st_1 :
  forall F v s,
    partial_derive F [v] s
    = Derive (fun X => F (upd_state s v X)) (s v).
Proof.
  sp.
Qed.

(*
Definition ex_partial_derive_st_vec_func_pd
           (f : interpretation -> state -> R)
           (m : nat)
           (l : list KAssignable)
           (s : state)
           (I : interpretation) : Prop :=
  ex_partial_derive_st_vec_func
    (fun d : Vector.t R m => partial_derive (f (upd_interpretation_dots I d)) l s).

Definition ex_partial_derive_st_vec_func_pda
           (f : interpretation -> state -> R) :=
  forall (m : nat)
         (l : list KAssignable)
         (s : state)
         (I : interpretation),
    ex_partial_derive_st_vec_func_pd f m l s I.
*)

(*
(* Try to prove this multi-state version of
   [ex_partial_derive_st_func_partial_derive_st_dynamic_semantics_term].
 *)
Lemma ex_partial_derive_st_vec_func_dynamic_semantics_term :
  forall (t : Term),
    ex_partial_derive_st_vec_func_pda
      (fun I s => dynamic_semantics_term I s t).
Proof.
  term_ind t Case; simpl.

  Focus 2.

  { Case "KTfuncOf".
    introv d cond; simpl.
    remember (I (SymbolFunction f n)) as iF; destruct iF as [F epd]; simpl.
    clear dependent f.

(*
    assert (ex_partial_derive_st_vec_func F) as pd by admit; clear epd.

    pose proof (pd Term
                   (KTdot 0)
                   (S k)
                   args
                   (fun v t =>
                      dynamic_semantics_term
                        (upd_interpretation_dots I m (Vector.map (G (vec_iseg v)) ts))
                        (vec_last v) t)) as q; simpl in q.
*)

    (*
Lemma xxx :
  forall k F,
    (forall l s,
        ex_all_le_partial_derive_st_vec
          k
          (fun v : Vector.t state (S k) =>
             partial_derive_st (fun s : state => F v s) l s))
    <->
    ex_all_le_partial_derive_st_vec
      (S k)
      (fun s : Vector.t state (S (S k)) => F (vec_iseg s) (vec_last s)).
Proof.
  induction k; introv; split; intro h.

  { constructor.

    { introv len1 len2.
      repeat (destruct Vs; simpl in *; ginv).
      repeat (destruct St; simpl in *; ginv).
      unfold ex_partial_derive_st_vec_l; simpl.
      pose proof (h l0 s0) as q; clear h.
      inversion q as [? pd|]; eqDepDec; subst; clear q.
      pose proof (pd [l] s [] v) as q; clear pd; simpl in q.
      repeat (autodimp q hyp). }

    { introv.
      constructor.
      introv len1 len2.
      repeat (destruct Vs; simpl in *; ginv).
      repeat (destruct St; simpl in *; ginv).
      unfold ex_partial_derive_st_vec_l; simpl.
      pose proof (h l s) as q; clear h.
      inversion q as [? pd|]; eqDepDec; subst; clear q.
      pose proof (pd [l] s [] v) as q; clear pd; simpl in q.
      repeat (autodimp q hyp). }
Qed.


    autodimp q hyp.

    { introv i.

    }

    SearchAbout ex_all_le_partial_derive_st_vec.

  }

  Focus 11.

  { Case "KTdifferential".
    introv d args.
    apply ex_all_le_partial_derive_st_vec_big_sum; introv i.
    apply ex_all_le_partial_derive_st_vec_mult.

    { apply ex_all_le_partial_derive_st_vec_const. }

    { eapply ex_all_le_partial_derive_st_vec_ext;
        [introv;
         pose proof (partial_derive_st_1
                       (fun s => dynamic_semantics_term
                                   (upd_interpretation_dots I m (Vector.map (G v1) ts))
                                   s t) v0 v) as h;
         apply h
        |].
*)

(*
      pose proof (IHt m I v T d 1 ts) as q; clear IHt; simpl in * |-.

      SearchAbout Vector.t.

      pose proof (q (fun (v : Vector.t state 2) (x : T) =>
                       dynamic_semantics_term
                         (upd_interpretation_dots I m (Vector.map (G v1) ts))
                         (upd_state v (KAssignVar v0) X)
                         t)) as h.

    }

    SearchAbout big_sum.

    destruct k.

    { constructor.
      introv len1 len2.
      repeat (destruct Vs; simpl in *; ginv).
      repeat (destruct St; simpl in *; ginv).
      unfold ex_partial_derive_st_vec_l; simpl.

      eapply ex_derive_ext;
        [introv; symmetry;
         apply partial_derive_st_big_sum
        |].

      { introv len; subst.
        eapply ex_all_partial_derive_st_mult;[| |reflexivity].

        { apply ex_all_partial_derive_st_constant. }

        { introv len; subst.
          unfold ex_partial_derive_st_l; simpl.
*)

(*          pose proof (q (fun v t => )


         apply ex_partial_derive_st_mult;
         [apply ex_partial_derive_st_read
         |apply ex_partial_derive_st_add_Derive;eauto 2 with core]
        |];[].

    apply ex_derive_n_big_sum; introv ltkn i.

    eapply ex_derive_n_ext;[introv;symmetry;apply partial_derive_st_DVar_mult|].

    { apply ex_partial_derive_st_add_Derive; eauto 2 with core. }

    eapply ex_derive_n_mult_gen; introv ltk.

    { apply ex_derive_n_const. }

    pose proof (IHt k0 (snoc l v) s I) as q.
    unfold partial_derive_I_st in q.
    eapply ex_derive_n_ext;[|apply q]; clear q.
    introv; cbv beta; simpl in *.
    rewrite partial_derive_st_S; autorewrite with core; try omega; auto.
*)

Abort.
*)

Lemma ex_all_partial_derive_st_big_sum :
  forall (vs : list KAssignable) F,
    (forall v, In v vs -> ex_all_partial_derive_st (fun s : state => F s v))
    -> ex_all_partial_derive_st (fun s : state => big_sum vs (F s)).
Proof.
  introv h.
  introv.
  apply ex_nth_partial_derive_st_big_sum.
  introv i j.
  apply h; auto.
Qed.

(*
Lemma update_state_st_rebase_DVar :
  forall s1 s2 l1 l2 v,
    update_state_st_rebase s1 s2 l1 l2 (DVar v)
    = s1 (DVar v).
Proof.
  induction l1; introv; simpl; auto.
  destruct l2; auto.
  autorewrite with core; auto.
Qed.
Hint Rewrite update_state_st_rebase_DVar : core.
*)

Lemma fold_upd_state_var :
  forall s v, upd_state s (KAssignVar v) = upd_state_var s v.
Proof.
  sp.
Qed.

Lemma update_state_st_rebase_KAssignVar_if_in :
  forall s1 s2 l1 l2 v,
    In v l2
    -> is_renaming l1 l2
    -> update_state_st_rebase s1 s2 l1 l2 v
       = s2 (rename_assign v (combine l2 l1)).
Proof.
  induction l1; introv i isren.
  { inversion isren; subst; simpl in *; tcsp. }

  { inversion isren as [|? ? ? ? chk isren1]; clear isren; subst; simpl in *.
    repndors; subst; dest_cases w; subst; GC; tcsp.

    { autorewrite with core; auto. }

    { rewrite upd_state_eq2; dest_cases w. }

    { rewrite upd_state_eq2; dest_cases w. }
  }
Qed.

(*
Definition ex_partial_derive_st_l_func (f : interpretation -> state -> R) :=
  forall (m     : nat)
         (I     : interpretation)
         (T     : Type)
         (d     : T)
         (ts    : Vector.t T m)
         (G     : state -> T -> R)
         (l1 l2 : list KAssignable)
         (s1 s2 : state)
         (v     : KAssignable)
         (t     : Term),
    (forall t s v l',
        Vector.In t ts
        -> sublist l' l2
        -> ex_partial_derive_st_l (fun s => G s t) s l' v)
    -> if l2 then
         ex_partial_derive_st_l
           (fun w : state =>
              dynamic_semantics_term
                (upd_interpretation_dots I (Vector.map (G s1) ts))
                w
                t)
           s1
           l1
           v
       else
         ex_partial_derive_st_l
           (fun v : state =>
              partial_derive
                (fun w : state =>
                   dynamic_semantics_term
                     (upd_interpretation_dots I (Vector.map (G v) ts))
                     w
                     t)
                l1
                s1)
           s2
           l2
           v.
*)

Lemma check_pair_ren_2_if_in_l :
  forall v a b l1 l2,
    In v l1
    -> check_pair_ren v a l1 l2
    -> check_pair_ren v b l1 l2
    -> a = b.
Proof.
  induction l1; introv i chk1 chk2; simpl in *; tcsp.
  repndors; subst.

  { inversion chk1 as [|? ? chk1'|]; subst; clear chk1; tcsp.
    inversion chk2 as [|? ? chk2'|]; subst; clear chk2; tcsp. }

  { inversion chk1 as [|? ? chk1'|]; subst; clear chk1; tcsp.

    { inversion chk2 as [|? ? chk2'|]; subst; clear chk2; tcsp. }

    { inversion chk2 as [|? ? chk2'|]; subst; clear chk2; tcsp; GC.
      eapply IHl1; eauto. }
  }
Qed.

Lemma check_pair_ren_if_in_l :
  forall v l1 l2,
    is_renaming l1 l2
    -> In v l1
    -> exists w, check_pair_ren v w l1 l2.
Proof.
  induction l1; introv isren i.

  { simpl in *; tcsp. }

  { inversion isren as [|? ? ? ? chk isren2]; subst; clear isren.
    simpl in *.
    repndors; subst; auto.

    { exists v2; auto. }

    { pose proof (IHl1 l3 isren2 i) as q; clear IHl1.
      exrepnd.
      destruct (KAssignable_dec a v); subst.

      { assert (w = v2) as xx.
        { eapply check_pair_ren_2_if_in_l; eauto. }
        subst.
        exists v2; auto. }

      { assert (In w l3) as j.
        { eapply check_pair_ren_in;[apply check_pair_ren_sym;eauto|];auto. }
        assert (w <> v2) as xx.
        { introv xx; subst.
          apply check_pair_ren_sym in chk.
          apply check_pair_ren_sym in q0.
          destruct n.
          eapply check_pair_ren_2_if_in_l;[|exact chk|exact q0]; auto. }
        exists w.
        constructor; auto. }
    }
  }
Qed.

Lemma check_pair_ren_if_not_in :
  forall a b l1 l2,
    ~ In a l1
    -> ~ In b l2
    -> length l1 = length l2
    -> check_pair_ren a b l1 l2.
Proof.
  induction l1; introv i j len; simpl in *.

  { destruct l2; simpl in *; tcsp. }

  { apply not_or in i; repnd.
    destruct l2; simpl in *; ginv.
    apply not_or in j; repnd.
    constructor; auto. }
Qed.

Lemma ex_renaming :
  forall d l,
  exists l', is_renaming l l' /\ disjoint l' d.
Proof.
  induction l; introv.

  { exists ([] : list KAssignable); dands; auto. }

  { exrepnd.

    destruct (in_dec KAssignable_dec a l) as [i|i].

    { pose proof (check_pair_ren_if_in_l a l l') as h.
      repeat (autodimp h hyp); exrepnd.
      exists (w :: l'); dands; auto.
      apply disjoint_cons_l; dands; auto.
      intro j; apply IHl0 in j; sp.
      eapply check_pair_ren_in;[apply check_pair_ren_sym;eauto|];auto. }

    { pose proof (fresh_kassignable (l ++ l' ++ d)%list) as q; exrepnd.
      allrw in_app_iff.
      repeat (apply not_or in q0; repnd).
      exists (x :: l'); dands; auto.
      { constructor; auto.
        apply check_pair_ren_if_not_in; auto.
        apply is_renaming2_implies_length; auto. }
      { apply disjoint_cons_l; auto. }
    }
  }
Qed.

Lemma ex_partial_derive_st_l_pt_add_Derive :
  forall F v w l,
    ex_partial_derive F w (snoc l v)
    -> ex_partial_derive
         (fun s => Derive (fun x => F (upd_state s v x)) (s v))
         w l.
Proof.
  introv d; introv; simpl in *.
  eapply ex_derive_ext;[|apply d]; simpl; introv.
  rewrite partial_derive_st_S; autorewrite with core; try omega; auto.
Qed.

Lemma snoc_as_app :
  forall {T} (v : T) l, snoc l v = (l ++ [v])%list.
Proof.
  induction l; simpl; auto.
  rewrite IHl; simpl; auto.
Qed.

Lemma implies_sublist_snoc :
  forall {T} (v : T) l1 l2,
    sublist l1 l2
    -> sublist (snoc l1 v) (snoc l2 v).
Proof.
  induction l1; introv ss; simpl.

  { apply sublist_cons_l.
    exists l2 ([] : list T); simpl; dands; auto.
    apply snoc_as_app. }

  { apply sublist_cons_l in ss; exrepnd; subst.
    apply sublist_cons_l.
    exists la (snoc lb v); dands; auto.
    repeat (rewrite snoc_as_app); simpl; auto.
    rewrite <- app_assoc; auto. }
Qed.

Lemma partial_derive_st_big_sum_sublist :
  forall l (vs : list KAssignable) (F : state -> KAssignable -> R) s,
    (forall v w k,
        In v vs
        -> sublist (w :: k) l
        -> ex_partial_derive (fun s => F s v) w k)
    -> partial_derive (fun w => big_sum vs (F w)) l s
       = big_sum vs (fun v => partial_derive (fun w => F w v) l s).
Proof.
  induction l using list_ind_snoc; introv imp; simpl; auto.

  rewrite partial_derive_st_S;[|autorewrite with core;omega].
  erewrite big_sum_ext;[|introv i;apply partial_derive_st_S;autorewrite with core;omega].
  simpl.
  erewrite partial_derive_st_ext;
    [|introv;apply Derive_big_sum; introv i; simpl in *
    ];autorewrite with core.

  { apply IHl; introv i ss.
    apply (ex_partial_derive_st_l_pt_add_Derive (fun s => F s v)).
    apply imp; auto.
    rewrite <- snoc_cons.
    apply implies_sublist_snoc; auto. }

  { pose proof (imp v a []) as q; clear imp.
    repeat (autodimp q hyp).
    { apply sublist_cons_l.
      exists l ([] : list KAssignable); dands; auto.
      apply snoc_as_app. }
    unfold ex_partial_derive in q; simpl in q.
    apply q. }
Qed.

Lemma ex_partial_derive_st_l_pt_big_sum :
  forall (vs : list KAssignable) F v l,
    (forall x w k,
        In x vs
        -> sublist (w :: k) (v :: l)
        -> ex_partial_derive (fun s : state => F s x) w k)
    -> ex_partial_derive (fun s : state => big_sum vs (F s)) v l.
Proof.
  introv h.
  introv; simpl in *.
  eapply ex_derive_ext;
    [introv;symmetry;apply partial_derive_st_big_sum_sublist|].

  { introv i ss; apply h; auto. }

  simpl.
  apply ex_derive_big_sum; introv i; simpl.
  apply h; auto; try (apply sublist_refl).
Qed.

Lemma ex_partial_derive_st_l_pt_const :
  forall c v l, ex_partial_derive (fun _ => c) v l.
Proof.
  introv.
  apply ex_all_partial_derive_st_implies_l_pt.
  apply ex_all_partial_derive_st_constant.
Qed.

Lemma is_renaming_sublist_implies_is_sub_renaming :
  forall l1 l2 l,
    is_renaming l1 l2
    -> sublist l l2
    -> exists l', is_sub_renaming l' l l1 l2.
Proof.
  induction l1; introv isren sl.

  { inversion isren; subst.
    inversion sl; subst.
    exists ([] : list KAssignable); auto. }

  { inversion isren as [|? ? ? ? chk isren2]; subst; clear isren.
    apply sublist_cons_r in sl; repndors; exrepnd; subst.

    { exists ([] : list KAssignable); auto. }

    { pose proof (IHl1 l3 l0) as q; repeat (autodimp q hyp); exrepnd.
      exists (a :: l'); auto. }

    { pose proof (IHl1 l3 l) as q; repeat (autodimp q hyp); exrepnd.
      exists l'; auto. }
  }
Qed.

Lemma sublist_cons_app_r_implies :
  forall l1 l2 l3 l v1 v2,
    is_renaming l l3
    -> sublist (v1 :: l1) (v2 :: l2 ++ l3)%list
    -> exists sl1 sl2 sl2',
        sublist sl1 l2
        /\ is_sub_renaming sl2 sl2' l l3
        /\ l1 = (sl1 ++ sl2')%list.
Proof.
  introv isren sl.

  apply sublist_cons_r in sl; repndors; ginv; exrepnd; ginv.

  { apply sublist_app_r in sl0; exrepnd; subst.
    pose proof (is_renaming_sublist_implies_is_sub_renaming l l3 lb) as q.
    repeat (autodimp q hyp); exrepnd.
    exists la l' lb.
    dands; auto. }

  { apply sublist_app_r in sl; exrepnd.

    destruct la; simpl in *; subst; ginv.

    { clear sl2.
      apply sublist_cons_l in sl1; exrepnd; subst.
      pose proof (is_renaming_sublist_implies_is_sub_renaming l (la ++ v1 :: lb) l1) as q.
      repeat (autodimp q hyp).
      { apply sublist_app_r_weak; constructor; auto. }
      exrepnd.
      exists ([] : list KAssignable) l' l1; simpl; dands; auto. }

    { apply sublist_cons_l in sl2; exrepnd; subst.
      pose proof (is_renaming_sublist_implies_is_sub_renaming l l3 lb) as q.
      repeat (autodimp q hyp); exrepnd.
      exists la l' lb; dands; auto.
      apply sublist_app_r_weak; constructor; auto.
    }
  }
Qed.

Lemma ex_partial_derive_st_l_pt_mult :
  forall l (L R : state -> R) v,
    (forall w l', sublist (w :: l') (v :: l) -> ex_partial_derive L w l')
    -> (forall w l', sublist (w :: l') (v :: l) -> ex_partial_derive R w l')
    -> ex_partial_derive (fun st => (L st * R st)%R) v l.
Proof.
  induction l as [l IH] using list_ind_len; introv d1 d2; introv; simpl in *.
  destruct (snoc_cases l) as [xx|xx]; exrepnd; subst.

  { clear IH; simpl.
    apply ex_derive_mult.
    { apply (d1 v []); auto. }
    { apply (d2 v []); auto. }
  }

  { eapply ex_derive_ext;
      [introv; symmetry;
       apply partial_derive_st_S; autorewrite with core; omega
      |].
    simpl.
    autorewrite with core.

    eapply ex_derive_ext;
      [simpl; introv; symmetry;
       apply partial_derive_st_ext;introv;
       apply Derive_mult
      |].

    { apply (d1 a []).
      apply sublist_cons_l.
      exists (v :: k) ([] : list KAssignable); simpl.
      rewrite snoc_as_app; simpl; dands; auto. }

    { apply (d2 a []).
      apply sublist_cons_l.
      exists (v :: k) ([] : list KAssignable); simpl.
      rewrite snoc_as_app; simpl; dands; auto. }

    simpl.

    eapply ex_derive_ext;
      [simpl; introv; symmetry;
       apply partial_derive_st_plus_sublist
      |].

    { introv sl.
      applydup @sublist_implies_le_length in sl as len; simpl in len.
      apply IH; autorewrite with core; try omega;[|].

      { introv sl'.
        pose proof (d1 w (snoc l' a)) as q; clear d1.
        autodimp q hyp.
        { repeat (rewrite <- snoc_cons).
          apply implies_sublist_snoc.
          eapply sublist_trans;eauto. }
        introv; simpl in *.
        pose proof (q pt0 s0) as h; clear q; simpl in *.
        eapply ex_derive_ext;[|exact h]; clear h; simpl; introv.
        rewrite partial_derive_st_S; autorewrite with core; auto; try omega. }

      { introv sl'; introv; simpl in *.
        eapply ex_derive_ext;
          [simpl; introv; symmetry;
           apply partial_derive_st_ext;introv;
           rewrite upd_state_ext; reflexivity
          |].
        pose proof (d2 w l') as q; clear d2.
        autodimp q hyp.
        { eapply sublist_trans;eauto.
          eapply sublist_trans;eauto.
          apply implies_sublist_cons_r_weak.
          apply implies_sublist_snoc_r_weak.
          apply sublist_refl. }
        pose proof (q pt0 s0) as h; clear q; simpl in *; auto. }
    }

    { introv sl.
      applydup @sublist_implies_le_length in sl as len; simpl in len.
      apply IH; autorewrite with core; try omega;[|].

      { introv sl'; introv; simpl in *.
        eapply ex_derive_ext;
          [simpl; introv; symmetry;
           apply partial_derive_st_ext;introv;
           rewrite upd_state_ext; reflexivity
          |].
        pose proof (d1 w l') as q; clear d1.
        autodimp q hyp.
        { eapply sublist_trans;eauto.
          eapply sublist_trans;eauto.
          apply implies_sublist_cons_r_weak.
          apply implies_sublist_snoc_r_weak.
          apply sublist_refl. }
        pose proof (q pt0 s0) as h; clear q; simpl in *; auto. }

      { introv sl'.
        pose proof (d2 w (snoc l' a)) as q; clear d2.
        autodimp q hyp.
        { repeat (rewrite <- snoc_cons).
          apply implies_sublist_snoc.
          eapply sublist_trans;eauto. }
        introv; simpl in *.
        pose proof (q pt0 s0) as h; clear q; simpl in *.
        eapply ex_derive_ext;[|exact h]; clear h; simpl; introv.
        rewrite partial_derive_st_S; autorewrite with core; auto; try omega. }
    }

    { apply @ex_derive_plus; simpl.

      { apply IH; autorewrite with core; try omega.

        { introv sl'.
          pose proof (d1 w (snoc l' a)) as q; clear d1.
          autodimp q hyp.
          { repeat (rewrite <- snoc_cons).
            apply implies_sublist_snoc; auto. }
          introv; simpl in *.
          pose proof (q pt0 s0) as h; clear q; simpl in *.
          eapply ex_derive_ext;[|exact h]; clear h; simpl; introv.
          rewrite partial_derive_st_S; autorewrite with core; auto; try omega. }

        { introv sl'; introv; simpl in *.
          eapply ex_derive_ext;
            [simpl; introv; symmetry;
             apply partial_derive_st_ext;introv;
             rewrite upd_state_ext; reflexivity
            |].
          pose proof (d2 w l') as q; clear d2.
          autodimp q hyp.
          { eapply sublist_trans;eauto.
            rewrite <- snoc_cons.
            apply implies_sublist_snoc_r_weak.
            apply sublist_refl. }
          pose proof (q pt0 s0) as h; clear q; simpl in *; auto. }
      }

      { apply IH; autorewrite with core; try omega.

        { introv sl'; introv; simpl in *.
          eapply ex_derive_ext;
            [simpl; introv; symmetry;
             apply partial_derive_st_ext;introv;
             rewrite upd_state_ext; reflexivity
            |].
          pose proof (d1 w l') as q; clear d1.
          autodimp q hyp.
          { eapply sublist_trans;eauto.
            rewrite <- snoc_cons.
            apply implies_sublist_snoc_r_weak.
            apply sublist_refl. }
          pose proof (q pt0 s0) as h; clear q; simpl in *; auto. }

        { introv sl'.
          pose proof (d2 w (snoc l' a)) as q; clear d2.
          autodimp q hyp.
          { repeat (rewrite <- snoc_cons).
            apply implies_sublist_snoc; auto. }
          introv; simpl in *.
          pose proof (q pt0 s0) as h; clear q; simpl in *.
          eapply ex_derive_ext;[|exact h]; clear h; simpl; introv.
          rewrite partial_derive_st_S; autorewrite with core; auto; try omega. }
      }
    }
  }
Qed.

Lemma ex_partial_derive_st_func_partial_derive_st_all_mult :
  forall F G,
    (forall I, ex_all_partial_derive_st (F I))
    -> (forall I, ex_all_partial_derive_st (G I))
    -> ex_partial_derive_st_func_partial_derive_st_all F
    -> ex_partial_derive_st_func_partial_derive_st_all G
    -> ex_partial_derive_st_func_partial_derive_st_all (fun I s => (F I s * G I s)%R).
Proof.
  introv F1 G1 F2 G2 d cond.
  revert F G F1 G1 F2 G2 m s I T d ts G0 v l0 cond.
  induction l as [l IH] using list_ind_len.
  introv F1 G1 F2 G2 d cond.

  destruct (snoc_cases l) as [xx|xx]; exrepnd; subst.

  { clear IH.
    simpl.
    apply ex_partial_derive_st_l_pt_mult; introv ss.

    { apply (F2 m [] s I T d ts G0 w l').
      introv i ss'.
      apply cond; auto.
      eapply sublist_trans; eauto. }

    { apply (G2 m [] s I T d ts G0 w l').
      introv i ss'.
      apply cond; auto.
      eapply sublist_trans; eauto. }
  }

  { eapply ex_partial_derive_ext;
      [introv;symmetry;apply partial_derive_st_S;autorewrite with core;omega
      |].
    simpl.
    autorewrite with core.

    eapply ex_partial_derive_ext;
      [simpl; introv; symmetry;
       apply partial_derive_st_ext;introv;
       apply Derive_mult
      |].

    { apply (F1 _ 0 s1 [] a eq_refl). }

    { apply (G1 _ 0 s1 [] a eq_refl). }

    simpl.

    eapply ex_partial_derive_ext;
      [simpl; introv; symmetry;
       apply partial_derive_st_plus_sublist
      |].

    { introv sl.
      apply ex_partial_derive_st_l_pt_mult.

      { introv sl'.
        introv; simpl in *.
        pose proof (F1 (upd_interpretation_dots I (Vector.map (G0 s0) ts))) as q.
        apply ex_partial_derive_st_pt_eq_all in q.
        pose proof (q w (snoc l' a) pt s1) as h; clear q; simpl in h.
        eapply ex_derive_ext;[|exact h]; clear h.
        simpl; introv.
        rewrite partial_derive_st_S; autorewrite with core; try omega; simpl; auto. }

      { introv sl'.
        introv; simpl in *.
        pose proof (G1 (upd_interpretation_dots I (Vector.map (G0 s0) ts))) as q.
        apply ex_partial_derive_st_pt_eq_all in q.
        pose proof (q w l' pt s1) as h; clear q; simpl in h.
        eapply ex_derive_ext;[|exact h]; clear h.
        simpl; introv.
        apply partial_derive_st_ext; introv.
        rewrite upd_state_ext; auto. }
    }

    { introv sl.
      apply ex_partial_derive_st_l_pt_mult.

      { introv sl'.
        introv; simpl in *.
        pose proof (F1 (upd_interpretation_dots I (Vector.map (G0 s0) ts))) as q.
        apply ex_partial_derive_st_pt_eq_all in q.
        pose proof (q w l' pt s1) as h; clear q; simpl in h.
        eapply ex_derive_ext;[|exact h]; clear h.
        simpl; introv.
        apply partial_derive_st_ext; introv.
        rewrite upd_state_ext; auto. }

      { introv sl'.
        introv; simpl in *.
        pose proof (G1 (upd_interpretation_dots I (Vector.map (G0 s0) ts))) as q.
        apply ex_partial_derive_st_pt_eq_all in q.
        pose proof (q w (snoc l' a) pt s1) as h; clear q; simpl in h.
        eapply ex_derive_ext;[|exact h]; clear h.
        simpl; introv.
        rewrite partial_derive_st_S; autorewrite with core; try omega; simpl; auto. }
    }

    { apply ex_partial_derive_st_l_pt_plus; introv sl.

      { pose proof (IH k) as q; clear IH; autorewrite with core in q.
        autodimp q hyp.
        apply (q (fun I s =>
                    Derive
                      (fun x : R =>
                         F I (upd_state s a x)) (s a))
                 (fun I s =>
                    G I (upd_state s a (s a)))); auto; clear q.

        { introv.
          pose proof (F1 I0) as q.
          apply ex_partial_derive_st_pt_eq_all; repeat introv; simpl in *.
          apply ex_partial_derive_st_pt_eq_all in q.
          pose proof (q v0 (snoc l a) pt s0) as h; clear q; simpl in h.
          eapply ex_derive_ext;[|exact h]; clear h.
          simpl; introv.
          rewrite partial_derive_st_S; autorewrite with core; try omega; simpl; auto. }

        { introv.
          pose proof (G1 I0) as q.
          apply ex_partial_derive_st_pt_eq_all; repeat introv; simpl in *.
          apply ex_partial_derive_st_pt_eq_all in q.
          pose proof (q v0 l pt s0) as h; clear q; simpl in h.
          eapply ex_derive_ext;[|exact h]; clear h.
          simpl; introv.
          apply partial_derive_st_ext; introv.
          rewrite upd_state_ext; auto. }

        { introv d0 cond0.
          pose proof (F2 m0 (snoc l a) s0 I0 T0 d0 ts0 G3 v0 l1 cond0) as q; simpl in q.
          eapply ex_partial_derive_ext;[|exact q]; clear q.
          introv; simpl.
          rewrite partial_derive_st_S; autorewrite with core; auto; try omega. }

        { introv d0 cond0.
          pose proof (G2 m0 l s0 I0 T0 d0 ts0 G3 v0 l1 cond0) as q; simpl in q.
          eapply ex_partial_derive_ext;[|exact q]; clear q.
          introv; simpl.
          apply partial_derive_st_ext; introv.
          rewrite upd_state_ext; auto. }

        { introv i ss; introv; simpl in *.
          apply cond; auto.
          eapply sublist_trans; eauto. }
      }

      { pose proof (IH k) as q; clear IH; autorewrite with core in q.
        autodimp q hyp.
        apply (q (fun I s =>
                    F I (upd_state s a (s a)))
                 (fun I s =>
                    Derive
                      (fun x : R =>
                         G I (upd_state s a x)) (s a))); auto; clear q.

        { introv.
          pose proof (F1 I0) as q.
          apply ex_partial_derive_st_pt_eq_all; repeat introv; simpl in *.
          apply ex_partial_derive_st_pt_eq_all in q.
          pose proof (q v0 l pt s0) as h; clear q; simpl in h.
          eapply ex_derive_ext;[|exact h]; clear h.
          simpl; introv.
          apply partial_derive_st_ext; introv.
          rewrite upd_state_ext; auto. }

        { introv.
          pose proof (G1 I0) as q.
          apply ex_partial_derive_st_pt_eq_all; repeat introv; simpl in *.
          apply ex_partial_derive_st_pt_eq_all in q.
          pose proof (q v0 (snoc l a) pt s0) as h; clear q; simpl in h.
          eapply ex_derive_ext;[|exact h]; clear h.
          simpl; introv.
          rewrite partial_derive_st_S; autorewrite with core; try omega; simpl; auto. }

        { introv d0 cond0.
          pose proof (F2 m0 l s0 I0 T0 d0 ts0 G3 v0 l1 cond0) as q; simpl in q.
          eapply ex_partial_derive_ext;[|exact q]; clear q.
          introv; simpl.
          apply partial_derive_st_ext; introv.
          rewrite upd_state_ext; auto. }

        { introv d0 cond0.
          pose proof (G2 m0 (snoc l a) s0 I0 T0 d0 ts0 G3 v0 l1 cond0) as q; simpl in q.
          eapply ex_partial_derive_ext;[|exact q]; clear q.
          introv; simpl.
          rewrite partial_derive_st_S; autorewrite with core; auto; try omega. }

        { introv i ss; introv; simpl in *.
          apply cond; auto.
          eapply sublist_trans; eauto. }
      }
    }
  }
Qed.

Lemma fold_ex_partial_derive :
  forall f v l,
    (forall pt s, ex_derive_R (fun X => partial_derive f l (upd_state s v X)) pt)
    = ex_partial_derive f v l.
Proof.
  sp.
Qed.

Lemma ex_partial_derive_update_state_st_rebase_KD :
  forall l s l1 l2 a v,
    is_renaming l1 l2
    -> ex_partial_derive
         (fun s1 : state => update_state_st_rebase s s1 l1 l2 (KD a))
         v
         l.
Proof.
  induction l using list_ind_snoc; introv isren.

  { unfold ex_partial_derive; simpl; introv.
    destruct (in_dec KAssignable_dec v l1) as [d|d].

    { pose proof (check_pair_ren_if_in_l v l1 l2 isren d) as xx; exrepnd.
      eapply ex_derive_ext;
        [simpl; introv; symmetry;
         erewrite update_state_st_rebase_switch_if_in;[|eauto|];auto;
         reflexivity
        |].
      unfold upd_state.
      dest_cases w.
      { apply @ex_derive_id. }
      { apply @ex_derive_const. }
    }

    { eapply ex_derive_ext;
        [simpl; introv; symmetry;
         rewrite update_state_st_rebase_upd_state_right_not_in;
         [reflexivity|];auto
        |].
      apply @ex_derive_const. }
  }

  { unfold ex_partial_derive; introv.
    eapply ex_derive_ext;
      [introv; symmetry;
       apply partial_derive_st_S;simpl;
       autorewrite with core; omega
      |].
    autorewrite with core.
    simpl in *.

    destruct (in_dec KAssignable_dec a l1) as [d|d].

    { pose proof (check_pair_ren_if_in_l a l1 l2 isren d) as xx; exrepnd.
      eapply ex_derive_ext;
        [introv; symmetry;
         apply partial_derive_st_ext; introv;
         apply Derive_ext; introv;
         erewrite update_state_st_rebase_switch_if_in;[|eauto|];auto;
         reflexivity
        |].
      simpl.
      unfold upd_state.
      repeat (dest_cases w; subst; GC).

      { eapply ex_derive_ext;
          [introv; symmetry;
           apply partial_derive_st_ext;introv;
           apply Derive_id
          |].
        simpl.
        destruct l.

        { simpl; apply @ex_derive_const. }

        { eapply ex_derive_ext;
            [introv; symmetry;
             apply partial_derive_st_const;simpl;omega
            |].
          apply @ex_derive_const. }
      }

      { eapply ex_derive_ext;
          [simpl; introv; symmetry;
           apply partial_derive_st_ext;introv;
           apply Derive_const
          |].
        destruct l.

        { simpl; apply @ex_derive_const. }

        { eapply ex_derive_ext;
            [introv; symmetry;
             apply partial_derive_st_const;simpl;omega
            |].
          apply @ex_derive_const. }
      }
    }

    { eapply ex_derive_ext;
        [simpl; introv; symmetry;
         apply partial_derive_st_ext;introv;
         apply Derive_ext;introv;
         rewrite update_state_st_rebase_upd_state_right_not_in;
         [reflexivity|];auto
        |].

      eapply ex_derive_ext;
        [simpl; introv; symmetry;
         apply partial_derive_st_ext;introv;
         apply Derive_const
        |].
      destruct l.

      { simpl; apply @ex_derive_const. }

      { eapply ex_derive_ext;
          [introv; symmetry;
           apply partial_derive_st_const;simpl;omega
          |].
        apply @ex_derive_const. }
    }
  }
Qed.

Lemma ex_partial_derive_st_func_partial_derive_st_dynamic_semantics_term :
  forall (t : Term),
    ex_partial_derive_st_func_partial_derive_st_all
      (fun I s => dynamic_semantics_term I s t).
Proof.
  term_ind t Case; simpl.

  { Case "KTdot".
    apply ex_partial_derive_st_func_partial_derive_st_all_dot. }

  { Case "KTfuncOf".
    introv d cond; simpl.
    remember (I (SymbolFunction f n)) as iF; destruct iF as [F epd]; simpl.
    clear dependent f.

    introv; simpl in *.

    pose proof (ex_renaming (v :: l0 ++ l)%list l) as isren.
    exrepnd.
    apply disjoint_cons_r in isren0; repnd.
    apply disjoint_app_r in isren2; repnd.

    eapply ex_derive_ext;
      [simpl;introv;symmetry;
       apply (partial_derive_st_combine _ _ l');auto
      |].
    simpl.

    eapply ex_derive_ext;
      [simpl;introv;symmetry;
       apply partial_derive_st_ext; introv;
       rewrite update_state_st_upd_state_not_in;[|auto];
       reflexivity
      |].

    eapply ex_derive_ext;
      [simpl;introv;symmetry;
       rewrite update_state_st_rebase_upd_state_not_in;[|auto];
       reflexivity
      |].

    apply epd; try (exact (KTdot 0)); clear epd.
    intros t v0 l1 i ss pt' newstate; simpl in *.

    (* we need to get back to two partial derivatives to use IHargs *)

    pose proof (sublist_cons_app_r_implies l1 l0 l' l v0 v) as q.
    repeat (autodimp q hyp).
    exrepnd; subst.

    eapply ex_derive_ext;[|].
    { simpl; introv; symmetry.
      apply (partial_derive_st_uncombine
               l0 _ _ _ sl2 _ _ _ _
               (fun sa sb =>
                  dynamic_semantics_term
                    (upd_interpretation_dots I (Vector.map (G sa) ts))
                    sb t));auto. }

    pose proof (sublist_cons_app_prop1 v0 v sl1 sl2' l0 l') as j.
    repeat (autodimp j hyp).
    { introv i1 i2.
      apply isren3 in i1; destruct i1.
      eapply sublist_in_implies; eauto. }
    destruct j as [j|j].

    { repnd; subst.
      simpl in *.

      eapply ex_derive_ext;
        [simpl;introv;symmetry;
         rewrite update_state_st_upd_state_if_in;[|auto];
         reflexivity
        |].

      pose proof (check_pair_ren_if_in_l v0 l' l) as chk.
      repeat (autodimp chk hyp);[apply is_renaming_sym;auto|].
      exrepnd.

      eapply ex_derive_ext;
        [introv;symmetry;
         erewrite update_state_st_rebase_switch_if_in;[|eauto|auto];
         reflexivity
        |];simpl.

      remember (upd_interpretation_dots
                  I
                  (Vector.map (G (update_state_st newstate s0 l')) ts)) as J; clear HeqJ.

      apply ex_partial_derive_st_pt_dynamic_semantics_term.
    }

    { repnd.
      assert (~ In v0 l') as k.
      { intro xx; applydup isren3 in xx; simpl in j0; repndors; subst; tcsp. }

      pose proof (IHargs
                    t i m sl2
                    (update_state_st_rebase s newstate l' l)
                    I T d ts G v0 sl1) as q; clear IHargs; simpl in q.
      autodimp q hyp.

      { introv iv ss'.
        apply cond; auto.
        eapply sublist_trans; eauto. }

      unfold ex_partial_derive in q; simpl in q.
      pose proof (q pt' (update_state_st newstate s0 l')) as h; clear q; simpl in h.
      eapply ex_derive_ext;[|exact h]; clear h.
      simpl; introv.
      rewrite update_state_st_upd_state_swap_if_not_in; auto.
      apply partial_derive_st_ext; introv.
      rewrite update_state_st_rebase_upd_state_right_not_in; auto.
    }
  }

  { Case "KTnumber".
    apply ex_partial_derive_st_func_partial_derive_st_all_const.
  }

  { Case "KTread".
    apply ex_partial_derive_st_func_partial_derive_st_all_read.
  }

  { Case "KTneg".
    apply ex_partial_derive_st_func_partial_derive_st_all_neg; auto.
  }

  { Case "KTplus".
    apply ex_partial_derive_st_func_partial_derive_st_all_plus; auto.
  }

  { Case "KTminus".
    apply ex_partial_derive_st_func_partial_derive_st_all_minus; auto.
  }

  { Case "KTtimes".
    apply ex_partial_derive_st_func_partial_derive_st_all_mult; auto.
  }

  { Case "KTdifferential".
    introv d cond; subst.
    eapply ex_partial_derive_ext;
      [introv;symmetry;apply partial_derive_st_big_sum|].

    { introv.
      apply ex_all_partial_derive_st_mult;
        [apply ex_all_partial_derive_st_read|].

      apply (ex_all_partial_derive_st_add_Derive
               (fun s =>
                  dynamic_semantics_term
                    (upd_interpretation_dots I (Vector.map (G s0) ts))
                    s
                    t)).
      apply ex_all_partial_derive_st_dynamic_semantics_term. }

    { simpl.

      apply ex_partial_derive_st_l_pt_big_sum.
      introv i ss.

      (* ======================= *)

      pose proof (ex_renaming (w :: v :: l0 ++ l ++ k)%list l) as isren.
      exrepnd.
      apply disjoint_cons_r in isren0; repnd.
      apply disjoint_cons_r in isren2; repnd.
      apply disjoint_app_r in isren3; repnd.
      apply disjoint_app_r in isren3; repnd.

      introv; simpl in *.
      eapply ex_derive_ext;[|].
      { simpl; introv; symmetry.
        apply (partial_derive_st_combine _ _ l');auto. }
      simpl.

      eapply ex_derive_ext;
        [simpl;introv;symmetry;
         apply partial_derive_st_ext; introv;
         rewrite update_state_st_upd_state_not_in;[|auto];
         reflexivity
        |].

      eapply ex_derive_ext;
        [simpl;introv;symmetry;
         rewrite update_state_st_rebase_upd_state_not_in;[|auto];
         reflexivity
        |].

      pose proof (ex_partial_derive_st_l_pt_mult
                    (k ++ l')
                    (fun s1 => update_state_st_rebase s s1 l' l (KD x))
                    (fun s1 =>
                       Derive
                         (fun X : R =>
                            dynamic_semantics_term
                              (upd_interpretation_dots
                                 I
                                 (Vector.map (G (update_state_st s1 s0 l')) ts))
                              (upd_state (update_state_st_rebase s s1 l' l) x X) t)
                         (update_state_st_rebase s s1 l' l x))%R
                    w) as exm.
      simpl in exm.
      repeat (autodimp exm hyp);
        [introv sl;apply ex_partial_derive_update_state_st_rebase_KD;auto;
         apply is_renaming_sym; auto
        |introv sl
        |apply exm].

      pose proof (sublist_cons_app_r_implies l'0 k l' l w0 w) as q.
      repeat (autodimp q hyp).
      exrepnd; subst.

      introv; simpl in *.
      eapply ex_derive_ext;[|].
      { simpl; introv; symmetry.
        apply (partial_derive_st_uncombine
                 k _ _ _ sl2 _ _ _ _
                 (fun sa sb =>
                    Derive
                      (fun X : R =>
                         dynamic_semantics_term
                           (upd_interpretation_dots
                              I
                              (Vector.map (G sa) ts))
                           (upd_state sb x X) t)
                      (sb x)));auto. }

      eapply ex_derive_ext;[|].
      { simpl; introv; symmetry.
        apply partial_derive_st_ext; introv.
        pose proof (partial_derive_st_S
                      (fun s3 =>
                         dynamic_semantics_term
                           (upd_interpretation_dots I (Vector.map (G s2) ts))
                           s3
                           t)
                      (snoc sl2 x)
                      (update_state_st_rebase s (upd_state s1 w0 t0) l' l)) as xx.
        autorewrite with core in *.
        autodimp xx hyp; try omega.
        rewrite <- xx; clear xx.
        reflexivity. }

      pose proof (sublist_cons_app_prop1 w0 w sl1 sl2' k l') as j.
      repeat (autodimp j hyp).
      { introv i1 i2.
        apply isren3 in i1; destruct i1.
        eapply sublist_in_implies; eauto. }
      destruct j as [j|j].

      { repnd; subst.
        simpl in *.

        eapply ex_derive_ext;
          [simpl;introv;symmetry;
           rewrite update_state_st_upd_state_if_in;[|auto];
           reflexivity
          |].

        pose proof (check_pair_ren_if_in_l w0 l' l) as chk.
        repeat (autodimp chk hyp);[apply is_renaming_sym;auto|].
        exrepnd.

        eapply ex_derive_ext;
          [introv;symmetry;
           erewrite update_state_st_rebase_switch_if_in;[|eauto|auto];
           reflexivity
          |];simpl.
        apply ex_partial_derive_st_pt_dynamic_semantics_term.
      }

      { repnd.
        assert (~ In w0 l') as kk.
        { intro xx; applydup isren3 in xx; simpl in j0; repndors; subst; tcsp. }

        pose proof (IHt
                      m (snoc sl2 x)
                      (update_state_st_rebase s s1 l' l)
                      I T d ts G w0 sl1) as q;
          clear IHt; simpl in q.
        autodimp q hyp.

        { introv iv ss'.
          apply cond; auto.
          eapply sublist_trans; eauto.
          eapply sublist_trans; eauto. }

        unfold ex_partial_derive in q; simpl in q.
        pose proof (q pt0 (update_state_st s1 s0 l')) as h; clear q; simpl in h.
        eapply ex_derive_ext;[|exact h]; clear h.
        simpl; introv.
        rewrite update_state_st_upd_state_swap_if_not_in; auto.
        apply partial_derive_st_ext; introv.
        rewrite update_state_st_rebase_upd_state_right_not_in; auto.
      }
    }
  }
Qed.

(*
Definition asub := list (KAssignable ## R).
*)

(*
Fixpoint upd_state_asub (s : state) (sub : asub) : state :=
  match sub with
  | [] => s
  | (a,r) :: sub => upd_state (upd_state_asub s sub) a r
  end.
*)

(*
Fixpoint vec2sub {n m} (vs : Vector.t KVariable n) (rs : Vector.t R m) : var_sub :=
  match vs, rs with
  | Vector.cons v _ vs, Vector.cons r _ rs => (v,r) :: vec2sub vs rs
  | _, _ => []
  end.
*)

(*
Fixpoint vec2asub
         {n m}
         (vs : Vector.t KVariable n)
         (rs : Vector.t R m) : asub :=
  match vs, rs with
  | Vector.cons v _ vs, Vector.cons r _ rs =>
    (KAssignVar v,r) :: (DVar v, R0) :: vec2asub vs rs
  | _, _ => []
  end.
*)

Fixpoint all_term_vars (f : Term) : list KVariable :=
  match f with
  | KTdot _ => []
(*  | KTanything => []*)
  | KTfuncOf f _ args => vec_flatten (Vector.map all_term_vars args)
  | KTnumber r   => []
  | KTread   x   => [KAssignable2variable x]
  | KTneg    l   => all_term_vars l
  | KTplus   l r => all_term_vars l ++ all_term_vars r
  | KTminus  l r => all_term_vars l ++ all_term_vars r
  | KTtimes  l r => all_term_vars l ++ all_term_vars r
  | KTdifferential theta => all_term_vars theta
  end.

(* same as [substitution_dots_term] but never fails on differentials *)
Fixpoint sub_dots_term (t : Term) {m} (u : Vector.t Term m) : Term :=
  match t with
  | KTdot n => vec_nth u n (KTdot n)
  | KTfuncOf f n args => KTfuncOf f n (Vector.map (fun a => sub_dots_term a u) args)
  | KTnumber r => KTnumber r
  | KTread   x => KTread x
  | KTneg    t   => KTneg    (sub_dots_term t u)
  | KTplus   l r => KTplus   (sub_dots_term l u) (sub_dots_term r u)
  | KTminus  l r => KTminus  (sub_dots_term l u) (sub_dots_term r u)
  | KTtimes  l r => KTtimes  (sub_dots_term l u) (sub_dots_term r u)
  | KTdifferential t => KTdifferential (sub_dots_term t u)
  end.

(*
Lemma var_sub_find_vec2sub_vec_nth_no_rep_in :
  forall {m} (vs : Vector.t KVariable m) (rs : Vector.t R m) n v r,
    n < m
    -> no_repeats_vec vs
    -> var_sub_find (vec2sub vs rs) (vec_nth vs n v)
       = Some (vec_nth rs n r).
Proof.
  induction m; introv ltm norep; try omega.

  revert norep.
  apply (Vector.caseS' vs); introv; simpl; clear vs.
  introv norep.
  apply (Vector.caseS' rs); introv; simpl; clear rs.
  destruct n.

  { dest_cases w. }

  { dest_cases w; subst; auto.

    { inversion norep as [|? ? ? ni norep2]; eqDepDec; subst.
      destruct ni.
      apply vec_nth_in; try omega. }

    { inversion norep; eqDepDec; subst.
      apply IHm; auto; try omega. }
  }
Qed.
*)

Lemma disjoint_vec_flatten_left_implies :
  forall {T n} (v : Vector.t (list T) n) l x,
    disjoint (vec_flatten v) l
    -> Vector.In x v
    -> disjoint x l.
Proof.
  introv disj i j k.
  apply disj in k; tcsp.
  apply in_vec_flatten.
  exists x; dands; auto.
Qed.

Lemma var_sub_find_none_implies_upd_list_state :
  forall st sub (a : KAssignable),
    var_sub_find sub a = None -> upd_list_state st sub a = st a.
Proof.
  induction sub; simpl; auto; introv e.
  destruct a; dest_cases w.
  rewrite upd_state_diff; tcsp.
  intro xx; destruct xx; tcsp.
Qed.

(*
Lemma not_in_implies_var_sub_find_vec2sub :
  forall m (vs : Vector.t KVariable m) (rs : Vector.t R m) a,
    ~ In a (Vector.to_list vs)
    -> var_sub_find (vec2sub vs rs) a = None.
Proof.
  induction m; introv ni; try omega.

  { apply (@Vector.case0
             KVariable
             (fun vs =>
                ~ In a (Vector.to_list vs)
                -> var_sub_find (vec2sub vs rs) a = None)); auto. }

  revert ni.
  apply (Vector.caseS' vs); introv ni; clear vs.
  apply (Vector.caseS' rs); introv; clear rs.
  autorewrite with core in *; simpl in *.
  apply not_or in ni; repnd.
  dest_cases w.
Qed.
*)

(*
Fixpoint asub_find (s : asub) (v : KAssignable) : option R :=
  match s with
  | [] => None
  | (w,r) :: s =>
    if KAssignable_dec v w then Some r
    else asub_find s v
  end.
*)

(*
Lemma upd_state_asub_decomp :
  forall st vs a,
    upd_state_asub st vs a
    = match asub_find vs a with
      | Some r => r
      | None => st a
      end.
Proof.
  induction vs; introv; simpl; auto.
  destruct a; simpl.
  dest_cases w; subst; auto.

  { autorewrite with core; auto. }

  { rewrite upd_state_diff; auto. }
Qed.
*)

(*
Lemma asub_find_vec2asub_vec_nth_no_rep_in :
  forall {m} (vs : Vector.t KVariable m) (rs : Vector.t R m) n v r,
    n < m
    -> no_repeats_vec vs
    -> asub_find (vec2asub vs rs) (KAssignVar (vec_nth vs n v))
       = Some (vec_nth rs n r).
Proof.
  induction m; introv ltm norep; try omega.

  revert norep.
  apply (Vector.caseS' vs); introv; simpl; clear vs.
  introv norep.
  apply (Vector.caseS' rs); introv; simpl; clear rs.
  destruct n.

  { dest_cases w. }

  { dest_cases w; subst; auto.

    { inversion e; subst; GC.
      inversion norep as [|? ? ? ni norep2]; eqDepDec; subst.
      destruct ni.
      apply vec_nth_in; try omega. }

    { inversion norep; eqDepDec; subst.
      apply IHm; auto; try omega. }
  }
Qed.
*)

(*
Lemma asub_find_none_implies_upd_state_asub :
  forall st sub (a : KAssignable),
    asub_find sub a = None -> upd_state_asub st sub a = st a.
Proof.
  induction sub; simpl; auto; introv e.
  destruct a; dest_cases w.
  rewrite upd_state_diff; tcsp.
Qed.
*)

(*
Lemma not_in_implies_asub_find_vec2asub :
  forall m (vs : Vector.t KVariable m) (rs : Vector.t R m) a,
    ~ In (KAssignable2variable a) (Vector.to_list vs)
    -> asub_find (vec2asub vs rs) a = None.
Proof.
  induction m; introv ni; try omega.

  { apply (@Vector.case0
             KVariable
             (fun vs =>
                ~ In (KAssignable2variable a) (Vector.to_list vs)
                -> asub_find (vec2asub vs rs) a = None)); auto. }

  revert ni.
  apply (Vector.caseS' vs); introv ni; clear vs.
  apply (Vector.caseS' rs); introv; clear rs.
  autorewrite with core in *; simpl in *.
  apply not_or in ni; repnd.
  dest_cases w; subst; tcsp.
  { destruct ni0; auto. }
  dest_cases w; subst; tcsp.
  destruct h; simpl in *; tcsp.
Qed.
*)

Fixpoint vec_term_variables {n} (v : Vector.t Term n) : list KVariable :=
  match v with
  | Vector.nil => []
  | Vector.cons t _ v => term_variables t ++ vec_term_variables v
  end.

Lemma big_sum0 :
  forall {T} (l : list T) f,
    (forall v, In v l -> f v = 0%R)
    -> big_sum l f = 0%R.
Proof.
  induction l; introv imp; simpl in *; auto.
  rewrite imp; auto.
  rewrite IHl; auto.
  autorewrite with core; auto.
Qed.

Lemma big_sum_if_in :
  forall {T} (l : list T) f v dec,
    In v l
    -> big_sum (remove_duplicates dec l) f
       = (f v + big_sum (remove_elt dec v (remove_duplicates dec l)) f)%R.
Proof.
  induction l; introv i; allsimpl; tcsp.
  repndors; subst; allsimpl; dest_cases w; simpl.

  { destruct (dec v v); tcsp; GC.
    f_equal.
    assert (~ List.In v (remove_duplicates dec l)) as h.
    { intro j; apply remove_duplicates_eqset in j; tcsp. }
    rewrite remove_elt_if_not_in; auto. }

  { dest_cases w; subst; simpl; tcsp.
    rewrite <- Rplus_assoc.
    rewrite (Rplus_comm (f v)).
    rewrite Rplus_assoc.
    rewrite <- IHl; auto. }
Qed.

Lemma remove_duplicates_remove_elt_comm :
  forall {T} (a : T) l dec,
    remove_duplicates dec (remove_elt dec a l)
    = remove_elt dec a (remove_duplicates dec l).
Proof.
  induction l; introv; simpl; auto.
  repeat (dest_cases w; simpl); tcsp.

  { apply in_remove_elt in i; tcsp. }

  { destruct n0; apply in_remove_elt; tcsp. }

  { rewrite IHl; auto. }
Qed.

Lemma big_sum_ext_eqset :
  forall {T} (l1 l2 : list T) f1 f2 dec,
    eqset l1 l2
    -> (forall v, In v l1 -> f1 v = f2 v)
    -> big_sum (remove_duplicates dec l1) f1 = big_sum (remove_duplicates dec l2) f2.
Proof.
  induction l1; introv eqs imp; simpl in *.

  { rewrite big_sum0; auto.
    introv i.
    apply remove_duplicates_eqset in i; tcsp.
    apply eqs in i; simpl in i; tcsp. }

  { dest_cases w; simpl.

    { apply eqset_redundant_left in eqs; auto. }

    { apply (eqset_not_redundant_left _ _ _ dec) in eqs; repnd; auto.
      pose proof (IHl1 (remove_elt dec a l2) f1 f2 dec) as h; clear IHl1.
      repeat (autodimp h hyp).
      rewrite h; clear h.
      rewrite (big_sum_if_in l2 f2 a dec); auto.
      rewrite remove_duplicates_remove_elt_comm.
      rewrite imp; auto. }
  }
Qed.

Lemma big_sum_ext2 :
  forall {T} (l1 l2 : list T) f1 f2 dec,
    (forall v, In v l1 -> In v l2 -> f1 v = f2 v)
    -> (forall v, In v l1 -> ~ In v l2 -> f1 v = 0%R)
    -> (forall v, ~ In v l1 -> In v l2 -> f2 v = 0%R)
    -> big_sum (remove_duplicates dec l1) f1
       = big_sum (remove_duplicates dec l2) f2.
Proof.
  induction l1; introv eqinter eql1 eql2; simpl in *.

  { rewrite big_sum0; auto.
    introv i.
    apply remove_duplicates_eqset in i; tcsp. }

  { dest_cases w; simpl.

    { apply IHl1; auto.
      introv h1 h2.
      apply eql2; auto.
      intro q; repndors; subst; tcsp. }

    { destruct (in_dec dec a l2) as [d1|d1].

      { pose proof (eqinter a) as h; repeat (autodimp h hyp).
        rewrite h; clear h.
        rewrite (big_sum_if_in l2 f2 a dec); auto.
        f_equal.
        rewrite <- remove_duplicates_remove_elt_comm.
        apply IHl1; introv h1 h2.

        { apply in_remove_elt in h2; repnd; apply eqinter; tcsp. }
        { rewrite in_remove_elt in h2.
          apply eql1; tcsp.
          intro j; destruct h2; dands; tcsp.
          intro xx; subst; tcsp. }
        { apply in_remove_elt in h2; repnd.
          apply eql2; tcsp. }
      }

      { rewrite (eql1 a); tcsp; autorewrite with core.
        apply IHl1; introv h1 h2; tcsp.
        apply eql2; tcsp.
        intro xx; repndors; subst; tcsp. }
    }
  }
Qed.

Lemma term_variables_subset_all_term_vars :
  forall t, subset (term_variables t) (all_term_vars t).
Proof.
  term_ind t case; introv; simpl; auto;
    try (complete (intro i; allrw in_app_iff; tcsp)).

  { Case "KTdot".
    intro i.
    apply in_vec_flatten in i.
    apply in_vec_flatten.
    exrepnd.
    apply in_vec_map in i1; exrepnd; subst.
    exists (all_term_vars a); dands; auto.
    { apply in_vec_map; eexists; dands; eauto. }
    apply IHargs; auto. }

  { Case "KTread".
    destruct var; simpl in *; auto. }
Qed.

(*
Lemma upd_state_upd_state_asub_swap :
  forall s l a t,
    asub_find l a = None
    -> upd_state (upd_state_asub s l) a t
       = upd_state_asub (upd_state s a t) l.
Proof.
  induction l; introv e; simpl in *; auto.
  destruct a; dest_cases w.
  rewrite upd_state_swap; dest_cases w; GC.
  f_equal.
  apply IHl; auto.
Qed.
*)

Lemma term_variables_subset_sub_dots_term :
  forall t {n} (v : Vector.t Term n),
    subset (term_variables t) (term_variables (sub_dots_term t v)).
Proof.
  term_ind t Case; introv; simpl; auto;
    try (complete (introv i; allrw in_app_iff; repndors;
                   [left;apply IHt1|right;apply IHt2];auto)).

  { Case "KTfuncOf".
    introv i.
    rewrite vec_map_map; unfold compose.
    allrw in_vec_flatten; exrepnd.
    allrw in_vec_map; exrepnd; subst.
    exists (term_variables (sub_dots_term a v)); dands; auto.

    { apply in_vec_map.
      eexists; dands; eauto. }

    apply IHargs; auto. }
Qed.

Lemma implies_in_vec_term_variables :
  forall x {n} (v : Vector.t Term n) t,
    Vector.In t v
    -> In x (term_variables t)
    -> In x (vec_term_variables v).
Proof.
  induction n; introv.

  { apply (@Vector.case0
             Term
             (fun v =>
                Vector.In t v
                -> In x (term_variables t) -> In x (vec_term_variables v))); simpl.
    intro i.
    inversion i. }

  apply (Vector.caseS' v); introv i j; clear v.
  simpl in *.
  apply in_app_iff.
  inversion i; eqDepDec; subst; tcsp.
  right; eapply IHn; eauto.
Qed.

Lemma term_variables_sub_dots_term_subset_app :
  forall t {n} (v : Vector.t Term n),
    subset
      (term_variables (sub_dots_term t v))
      (term_variables t ++ vec_term_variables v).
Proof.
  term_ind t Case; introv; simpl; auto;
    try (complete (introv i; allrw in_app_iff; repndors; tcsp;
                   [apply IHt1 in i|apply IHt2 in i];
                   allrw in_app_iff; repndors; tcsp)).

  { Case "KTdot".

    introv i.

    destruct (le_lt_dec n0 n) as [d|d].

    { rewrite vec_nth_default in i; simpl in i; tcsp. }

    { eapply implies_in_vec_term_variables;[|eauto].
      apply vec_nth_in; auto. }
  }

  { Case "KTfuncOf".
    rewrite vec_map_map; unfold compose.
    introv i.
    allrw in_vec_flatten; exrepnd.
    allrw in_vec_map; exrepnd; subst.
    apply IHargs in i0; auto.
    allrw in_app_iff; repndors; tcsp.
    left.
    apply in_vec_flatten.
    eexists;dands;[|eauto].
    apply in_vec_map; eexists; dands; eauto. }

  { Case "KTread".
    introv i; apply in_app_iff; tcsp. }
Qed.

Lemma in_vec_term_variables_read_vars :
  forall v {n} (vs : Vector.t KVariable n),
    In v (vec_term_variables (Vector.map (fun v => KTread (KAssignVar v)) vs))
    -> Vector.In v vs.
Proof.
  induction n; simpl; introv.

  { apply (@Vector.case0
             KVariable
             (fun vs =>
                In v
                   (vec_term_variables
                      (Vector.map (fun v0 => KTread (KAssignVar v0)) vs))
                -> Vector.In v vs)); simpl; tcsp. }

  apply (Vector.caseS' vs); introv i; clear vs.
  simpl in *; repndors; subst; tcsp.
Qed.

Lemma in_vector_iff_in_list :
  forall {T n} v (vs : Vector.t T n),
    Vector.In v vs <-> In v (Vector.to_list vs).
Proof.
  induction n; introv.

  { apply (@Vector.case0
             T
             (fun vs =>
                Vector.In v vs <-> In v (Vector.to_list vs))); simpl.
    split; intro h; tcsp.
    inversion h. }

  apply (Vector.caseS' vs); introv; clear vs.
  autorewrite with core in *; simpl.
  split; intro q.

  { inversion q; eqDepDec; subst; tcsp.
    right; apply IHn; auto. }

  { repndors; subst; tcsp.
    constructor; apply IHn; auto. }
Qed.

(*
Lemma upd_state_asub_vec2asub_dvar_if_in :
  forall {n} (vs : Vector.t KVariable n) (rs : Vector.t R n) s v,
    Vector.In v vs
    -> upd_state_asub s (vec2asub vs rs) (DVar v) = R0.
Proof.
  induction n; introv.

  { apply (@Vector.case0
             KVariable
             (fun vs =>
                Vector.In v vs -> upd_state_asub s (vec2asub vs rs) (DVar v) = 0%R)); simpl.
    intro i; inversion i. }

  apply (Vector.caseS' vs); introv; clear vs.
  apply (Vector.caseS' rs); introv; clear rs.
  simpl.
  introv i.
  inversion i; eqDepDec; subst; tcsp; clear i.

  { rewrite upd_state_diff;[|intro xx;inversion xx].
    autorewrite with core; auto. }

  { rewrite upd_state_diff;[|intro xx;inversion xx].
    unfold upd_state; dest_cases w. }
Qed.
*)

Lemma free_vars_term_subset_all_term_vars :
  forall t a,
    List.In a (free_vars_term t)
    -> List.In (KAssignable2variable a) (all_term_vars t).
Proof.
  term_ind t case; introv i; simpl in *; auto;
    try (complete (allrw in_app_iff; tcsp)).

  { Case "KTfunfOf".
    allrw in_vec_flatten; exrepnd.
    allrw in_vec_map; exrepnd; subst.
    eexists;dands;[|eauto].
    apply in_vec_map.
    eexists; dands; eauto. }

  { Case "KTread".
    repndors; subst; tcsp. }

  { Case "KTdifferential".
    apply in_app_iff in i; repndors; auto.
    apply in_map_iff in i; exrepnd; subst; simpl in *.
    apply IHt; auto. }
Qed.

Lemma free_vars_term_subset_sub_dots_term :
  forall t {n} (v : Vector.t Term n),
    subset (free_vars_term t) (free_vars_term (sub_dots_term t v)).
Proof.
  term_ind t Case; introv; simpl; auto;
    try (complete (introv i; allrw in_app_iff; repndors;
                   [left;apply IHt1|right;apply IHt2];auto)).

  { Case "KTfuncOf".
    introv i.
    rewrite vec_map_map; unfold compose.
    allrw in_vec_flatten; exrepnd.
    allrw in_vec_map; exrepnd; subst.
    exists (free_vars_term (sub_dots_term a v)); dands; auto.

    { apply in_vec_map.
      eexists; dands; eauto. }

    apply IHargs; auto. }

  { Case "KTdifferential".
    apply implies_subset_app_lr; auto.
    apply implies_subset_map_lr; auto. }
Qed.

Lemma implies_in_free_vars_vec_term :
  forall x {n} (v : Vector.t Term n) t,
    Vector.In t v
    -> In x (free_vars_term t)
    -> In x (free_vars_vec_term v).
Proof.
  induction n; introv.

  { apply Vector.case0 with (v := v); simpl.
    intro i.
    inversion i. }

  apply (Vector.caseS' v); introv i j; clear v.
  simpl in *.
  apply in_app_iff.
  inversion i; eqDepDec; subst; tcsp.
  right; eapply IHn; eauto.
Qed.

(*
Lemma term_assignables_sub_dots_term_subset_app :
  forall t {n} (v : Vector.t Term n),
    subset
      (term_assignables (sub_dots_term t v))
      (term_assignables t ++ vec_term_assignables v).
Proof.
  term_ind t Case; introv; simpl; auto;
    try (complete (introv i; allrw in_app_iff; repndors; tcsp;
                   [apply IHt1 in i|apply IHt2 in i];
                   allrw in_app_iff; repndors; tcsp)).

  { Case "KTdot".

    introv i.

    destruct (le_lt_dec n0 n) as [d|d].

    { rewrite vec_nth_default in i; simpl in i; tcsp. }

    { eapply implies_in_vec_term_assignables;[|eauto].
      apply vec_nth_in; auto. }
  }

  { Case "KTfuncOf".
    rewrite vec_map_map; unfold compose.
    introv i.
    allrw in_vec_flatten; exrepnd.
    allrw in_vec_map; exrepnd; subst.
    apply IHargs in i0; auto.
    allrw in_app_iff; repndors; tcsp.
    left.
    apply in_vec_flatten.
    eexists;dands;[|eauto].
    apply in_vec_map; eexists; dands; eauto. }

  { Case "KTread".
    introv i; simpl in *; tcsp. }

  { Case "KTdifferential".
    introv i; allrw in_app_iff.
    repndors.
    { apply IHt in i; allrw in_app_iff; repndors; tcsp. }
    { apply in_map_iff in i; exrepnd; subst; simpl in *.
      apply IHt in i0; allrw in_app_iff.
  }
Qed.
*)

Lemma in_free_vars_vec_term_read_vars :
  forall v {n} (vs : Vector.t KVariable n),
    In v (free_vars_vec_term (Vector.map (fun v => KTread (KAssignVar v)) vs))
    -> Vector.In (KAssignable2variable v) vs.
Proof.
  induction n; simpl; introv.

  { apply Vector.case0 with (v := vs); simpl; tcsp. }

  apply (Vector.caseS' vs); introv i; clear vs.
  simpl in *; repndors; subst; tcsp.
Qed.

(*
Fixpoint findInVsub
         {n m}
         (v  : KVariable)
         (vs : Vector.t KVariable n)
         (rs : Vector.t R m) : option R :=
  match vs, rs with
  | Vector.cons w _ vs, Vector.cons r _ rs =>
    if KVariable_dec v w then Some r else findInVsub v vs rs
  | _, _ => None
  end.

Definition upd_state_vsub
         {m}
         (s  : state)
         (vs : Vector.t KVariable m)
         (rs : Vector.t R m) : state :=
  fun a =>
    match findInVsub (KAssignable2variable a) vs rs with
    | None => s a
    | Some r => if a then r else R0
    end.

Lemma upd_state_vsub_KAssignVar_vec_nth :
  forall s {n} (vs : Vector.t KVariable n) (rs : Vector.t R n) v r m,
    m < n
    -> no_repeats_vec vs
    -> upd_state_vsub s vs rs (KAssignVar (vec_nth vs m v))
       = vec_nth rs m r.
Proof.
  introv ltmn norep.
  unfold upd_state_vsub.
  revert dependent m.
  induction n; introv ltmn; try omega.

  revert norep.
  apply (Vector.caseS' vs); introv; clear vs; introv norep.
  apply (Vector.caseS' rs); introv; clear rs.
  simpl.
  inversion norep as [|? ? ? i norep2]; clear norep; subst; eqDepDec; subst.
  destruct m; dest_cases w; subst; auto.

  { destruct i.
    apply vec_nth_in; omega. }

  { apply IHn; auto; try omega. }
Qed.

Lemma upd_state_vsub_if_not_in :
  forall s {n} (vs : Vector.t KVariable n) (rs : Vector.t R n) (v : KAssignable),
    ~ In (KAssignable2variable v) (Vector.to_list vs)
    -> upd_state_vsub s vs rs v = s v.
Proof.
  unfold upd_state_vsub; introv i.
  induction n; revert i.

  { apply Vector.case0 with (v := vs); clear vs; simpl; tcsp. }

  { apply (Vector.caseS' vs); introv i; clear vs.
    apply (Vector.caseS' rs); introv; clear rs.
    autorewrite with core in *.
    simpl in *.
    apply not_or in i; repnd.
    repeat (dest_cases w; subst; GC).
    pose proof (IHn t t0 i) as q.
    rewrite <- Heqw0 in q; auto. }
Qed.

Lemma upd_state_upd_state_vsub_swap_if_not_in :
  forall s {n} (vs : Vector.t KVariable n) (rs : Vector.t R n) v x,
    ~ In (KAssignable2variable v) (Vector.to_list vs)
    -> upd_state (upd_state_vsub s vs rs) v x
       = upd_state_vsub (upd_state s v x) vs rs.
Proof.
  introv i.
  unfold upd_state, upd_state_vsub; simpl.
  apply functional_extensionality; simpl; introv.
  dest_cases w; subst.
  revert i.
  induction n.

  { apply Vector.case0 with (v := vs); simpl; auto. }

  { apply (Vector.caseS' vs); introv i; simpl; clear vs.
    autorewrite with core in *; simpl in *.
    apply not_or in i; repnd.
    apply (Vector.caseS' rs); introv; simpl; clear rs.
    repeat (dest_cases w; subst; GC).
    pose proof (IHn t t0 i) as q.
    rewrite <- Heqw0 in q; auto. }
Qed.

Lemma upd_state_vsub_KD_if_in :
  forall {n} (vs : Vector.t KVariable n) (rs : Vector.t R n) s v,
    Vector.In (KAssignable2variable v) vs
    -> upd_state_vsub s vs rs (KD v) = R0.
Proof.
  induction n; introv; unfold upd_state_vsub in *.

  { apply Vector.case0 with (v := vs); simpl.
    intro i; inversion i. }

  apply (Vector.caseS' vs); introv i; clear vs.
  apply (Vector.caseS' rs); introv; clear rs.
  inversion i; subst; eqDepDec; subst; clear i; simpl in *;
    repeat (dest_cases w; subst; GC).
  pose proof (IHn t t0 s v) as q; autodimp q hyp.
  rewrite <- Heqw in q; auto.
Qed.
*)

(*
(* TOFIX! *)
Lemma upd_interpretation_dots_as_upd_list_state :
  forall (t  : Term)
         (m  : nat)
         (vs : Vector.t KVariable m)
         (rs : Vector.t R m)
         (I  : interpretation)
         (s  : state),
    disjoint (all_term_vars t) (Vector.to_list vs)
    -> no_repeats_vec vs
    -> dynamic_semantics_term (upd_interpretation_dots I m rs) s t
       = dynamic_semantics_term
           I
           (upd_state_vsub s vs rs)
           (sub_dots_term t (Vector.map (fun v => KTread (KAssignVar v)) vs)).
Proof.
  term_ind t Case; introv disj norep; simpl in *; auto;
    try (complete (apply disjoint_app_l in disj; repnd;
                   erewrite IHt1; eauto; erewrite IHt2; eauto));
    try (complete (erewrite IHt; eauto)).

  { Case "KTdot".

    destruct (le_lt_dec m n) as [d|d].

    { repeat (rewrite vec_nth_default; auto). }

    { rewrite (vec_nth_map _ _ _ DumKVar); auto.
      simpl.
      erewrite upd_state_vsub_KAssignVar_vec_nth;[reflexivity| |];auto. }
  }

  { Case "KTfuncOf".

    f_equal.
    rewrite vec_map_map; unfold compose.
    apply eq_vec_map; introv i.
    apply IHargs; auto.
    eapply disjoint_vec_flatten_left_implies in disj;[exact disj|].
    apply in_vec_map.
    eexists; dands; eauto. }

  { Case "KTread".

    apply disjoint_cons_l in disj; repnd.
    clear disj.
    rewrite upd_state_vsub_if_not_in; auto. }

  { Case "KTdifferential".
    apply big_sum_ext2.

    { introv i j.
      applydup term_assignables_subset_all_term_vars in i as k.
      applydup disj in k as z.
      repeat (rewrite upd_state_vsub_if_not_in; auto;[]).
      f_equal.
      apply Derive_ext; introv.
      rewrite upd_state_upd_state_vsub_swap_if_not_in; auto. }

    { introv i ni.
      destruct ni.
      apply term_assignables_subset_sub_dots_term; auto. }

    { introv ni i.
      apply term_assignables_sub_dots_term_subset_app in i.
      apply in_app_iff in i; repndors; tcsp;[].
      apply in_vec_term_assignables_read_vars in i.
      rewrite upd_state_vsub_KD_if_in; auto.
      autorewrite with core; auto. }
  }
Qed.
*)

Lemma ex_partial_derive_st_func_ext :
  forall {n} (f g : Vector.t R n -> R),
    (forall v, f v = g v)
    -> ex_partial_derive_st_func f
    -> ex_partial_derive_st_func g.
Proof.
  introv e pd def h.
  pose proof (pd T def ts G h) as q.
  eapply ex_all_partial_derive_st_ext;[introv;apply e|]; auto.
Qed.

(*
Lemma upd_state_asub_vec2asub_dvar_if_not_in :
  forall (n : nat) (vs : Vector.t KVariable n) m (rs : Vector.t R m) s v,
    ~ Vector.In v vs
    -> upd_state_asub s (vec2asub vs rs) (DVar v) = s (DVar v).
Proof.
  induction vs; introv ni; simpl in *; auto.
  destruct rs; simpl; auto.
  rewrite upd_state_diff;[|intro xx; inversion xx].
  unfold upd_state; dest_cases w; ginv; auto.

  { destruct ni; constructor. }

  { apply IHvs; intro xx; destruct ni; constructor; auto. }
Qed.
*)

(*
Lemma ex_partial_derive_st_func_dynamic_semantics :
  forall t m I v (vs : Vector.t KVariable m),
    ex_partial_derive_st_func
      (fun d : Vector.t R m =>
         dynamic_semantics_term I (upd_state_asub v (vec2asub vs d)) t).
Proof.
  term_ind t Case; introv; simpl.

  Focus 11.

  { Case "KTdifferential".
    introv d cond len; subst; simpl.

    eapply ex_derive_ext;
      [introv;symmetry;
       apply partial_derive_st_big_sum
      |].

    { introv.
      apply ex_all_partial_derive_st_mult.

      { destruct (vec_in_dec KVariable_dec v1 vs) as [i|i].

        { eapply ex_all_partial_derive_st_ext;
            [introv;symmetry;apply upd_state_asub_vec2asub_dvar_if_in;auto|].
          apply ex_all_partial_derive_st_constant. }

        { eapply ex_all_partial_derive_st_ext;
            [introv;symmetry;
             apply (upd_state_asub_vec2asub_dvar_if_not_in
                      m vs m (Vector.map (G s) ts) v v1);auto
            |].
          apply ex_all_partial_derive_st_constant. }
      }

Abort.
*)

Lemma adjoint_interpretation_function_derive :
  forall I v s f m,
    smooth_fun_T
      (fun d : Vector.t R m =>
         dynamic_semantics_term
           (upd_interpretation_dots I d)
           v
           (lookup_func s f m)).
Proof.
  introv.

  remember (lookup_func s f m) as t.
  clear Heqt.

  introv d cond; introv; simpl in *.

  apply (ex_partial_derive_st_func_partial_derive_st_dynamic_semantics_term
           t m [] v I T d ts); auto.
Qed.

Lemma adjoint_interpretation_quantifier_cond :
  forall s C (I : interpretation),
    interpQuantExt
      (fun R : FormulaSem =>
         dynamic_semantics_formula
           (upd_interpretation_dot_form I R)
           (lookup_quant s C)).
Proof.
  introv h q; simpl.
  apply ext_dynamic_semantics_formula; auto.
  apply ext_interpretations_upd_interpretation_dot_form; auto.
Qed.

Lemma ext_dynamic_semantics_ode_fun :
  forall I ode v w a,
    (forall (a : KAssignable), v a = w a)
    -> dynamic_semantics_ode_fun I ode v a
       = dynamic_semantics_ode_fun I ode w a.
Proof.
  induction ode; introv cond; simpl.

  { destruct child; simpl; auto;
      repeat (dest_cases w; subst; tcsp).

    { remember (I (SymbolODE name)) as C; destruct C as [bv dm ext]; clear HeqC; simpl.
      apply ext; auto. }

    { apply coincidence_term; auto.
      introv i; apply cond. }
  }

  { erewrite IHode1; eauto.
    erewrite IHode2; eauto. }
Qed.

Lemma adjoint_interp_ode_cond :
  forall (I : interpretation) s c,
    interpOdeExt
      (ode_assign I (lookup_ode s c))
      (dynamic_semantics_ode_fun I (lookup_ode s c)).
Proof.
  introv cond; simpl.
  apply ext_dynamic_semantics_ode_fun; auto.
Qed.

(** Substitution adjoint --- see Definition 11, Section 3.1 *)
Definition adjoint_interpretation
           (s : UniformSubstitution)
           (I : interpretation)
           (v : state) : interpretation :=
  fun f : Symbol =>
    match f with
    | SymbolFunction g n =>
      MkInterpFun
        n
        (fun d : Vector.t R n =>
           dynamic_semantics_term
             (upd_interpretation_dots I d)
             v
             (lookup_func s g n))
        (adjoint_interpretation_function_derive I v s g n)

    | SymbolDotTerm n => I (SymbolDotTerm n)

    | SymbolPredicate p n =>
      fun d : Vector.t R n =>
        dynamic_semantics_formula
          (upd_interpretation_dots I d)
          (lookup_pred s p n)
          v

    | SymbolQuantifier C =>
      MkInterpQuant
        (fun R =>
           dynamic_semantics_formula
             (upd_interpretation_dot_form I R)
             (lookup_quant s C))
        (adjoint_interpretation_quantifier_cond s C I)

    | SymbolDotForm => I SymbolDotForm

    | SymbolODE c =>
      MkInterpODE
        (ode_assign I (lookup_ode s c))
        (dynamic_semantics_ode_fun
           I
           (lookup_ode s c))
        (adjoint_interp_ode_cond I s c)

    | SymbolProgramConst a =>
      dynamic_semantics_program
        I
        (lookup_const s a)
    end.
