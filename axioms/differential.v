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



(* MOVE to list_util *)
Lemma implies_remove_duplicates_app_prop1 :
  forall {T} dec (l1 l2 : list T),
    null (remove_duplicates dec l1)
    -> null (remove_duplicates dec l2)
    -> null (remove_duplicates dec (l1 ++ l2)).
Proof.
  induction l1; introv n1 n2; simpl in *; auto.
  repeat (dest_cases w); simpl in *; try (complete (inversion n1)).
  rewrite in_app_iff in n; apply not_or in n; tcsp.
Qed.

(* MOVE to list_util *)
Lemma implies_remove_duplicates_app_prop2 :
  forall {T} dec (l1 l2 : list T),
    null (remove_duplicates dec l1)
    -> remove_duplicates dec (l1 ++ l2)
       = remove_duplicates dec l2.
Proof.
  induction l1; introv n; simpl in *; auto.
  repeat (dest_cases w); simpl in *; try (complete (inversion n)).
  rewrite in_app_iff in n0; apply not_or in n0; tcsp.
Qed.

(* MOVE to list_util *)
Lemma implies_in_remove_duplicates :
  forall {T} dec x (l : list T),
    List.In x l
    -> List.In x (remove_duplicates dec l).
Proof.
  induction l; introv i; simpl in *; tcsp.
  dest_cases w.
  repndors; subst; tcsp.
Qed.

(* MOVE to list_util *)
Lemma implies_remove_duplicates_app_prop3 :
  forall {T} dec (l1 l2 : list T),
    null (remove_duplicates dec l2)
    -> remove_duplicates dec (l1 ++ l2)
       = remove_duplicates dec l1.
Proof.
  induction l1; introv n1; simpl in *; auto.
  repeat (dest_cases w); simpl in *; try (complete (inversion n1)).

  { rewrite in_app_iff in i; repndors; tcsp.
    apply (implies_in_remove_duplicates dec) in i.
    rewrite n1 in i; simpl in i; tcsp. }

  { rewrite in_app_iff in n; apply not_or in n; tcsp. }

  { f_equal; auto. }
Qed.

(* MOVE to list_util *)
Lemma subset_nil_r :
  forall {T} (l : list T),
    subset l [] <-> l = [].
Proof.
  introv; split; intro h; subst; auto.
  destruct l; auto.
  pose proof (h t) as q; simpl in q; autodimp q hyp; tcsp.
Qed.

(* MOVE to list_util *)
Lemma remove_duplicates_middle_if_in_tail :
  forall {T} dec (x : T) l1 l2,
    List.In x l2
    -> remove_duplicates dec (l1 ++ x :: l2)
       = remove_duplicates dec (l1 ++ l2).
Proof.
  induction l1; introv i; simpl in *; tcsp; repeat (dest_cases w); auto.

  { apply in_app_iff in i0; repnd; simpl in *.
    rewrite in_app_iff in n; apply not_or in n; repnd.
    repndors; subst; tcsp. }

  { rewrite in_app_iff in n; apply not_or in n; repnd; simpl in n.
    apply not_or in n; repnd.
    rewrite in_app_iff in i0; repndors; tcsp. }

  { f_equal; auto. }
Qed.

(* MOVE to list_util *)
Lemma implies_remove_duplicates_app_prop4 :
  forall {T} dec (l1 l2 : list T),
    subset l1 l2
    -> remove_duplicates dec (l1 ++ l2)
       = remove_duplicates dec l2.
Proof.
  induction l1; introv ss; simpl in *; auto.
  apply subset_cons_l in ss; repnd.
  apply IHl1 in ss.
  rewrite ss.
  dest_cases w.
  rewrite in_app_iff in n; apply not_or in n; repnd; tcsp.
Qed.

Lemma remove_duplicate_map_KD :
  forall l,
    null (remove_duplicates KAssignable_dec l)
    -> null (remove_duplicates KAssignable_dec (map KD l)).
Proof.
  induction l; simpl; introv n; auto.
  repeat (dest_cases w); simpl in *.
  { destruct n0; apply in_map_iff; eexists; dands; eauto. }
  { inversion n. }
  { inversion n. }
Qed.

(* MOVE to list_util *)
Lemma eqset_implies_subset :
  forall {T} (l1 l2 : list T),
    eqset l1 l2 -> subset l1 l2.
Proof.
  introv e i; apply e in i; auto.
Qed.

Lemma free_vars_term_nodup_eqset :
  forall t, eqset (term_assignables_nodup t) (free_vars_term t).
Proof.
  introv; unfold term_assignables_nodup.
  apply remove_duplicates_eqset.
Qed.

(* MOVE to list_util *)
Lemma eqset_nil_l :
  forall {T} (l : list T), eqset [] l <-> l = [].
Proof.
  introv; split; intro h; subst; auto.
  destruct l; auto.
  pose proof (h t) as q; clear h; simpl in q.
  destruct q as [q1 q2].
  autodimp q2 hyp; tcsp.
Qed.

(* MOVE to list_util *)
Lemma eqset_singleton_lr :
  forall {T} (a b : T), eqset [a] [b] <-> a = b.
Proof.
  introv; split; intro h; subst; auto.
  pose proof (h a) as q; clear h; simpl in q.
  destruct q as [q1 q2].
  autodimp q1 hyp; tcsp.
Qed.

Lemma eqset_implies_eq_remove_duplicates_singleton :
  forall {T} dec x (l : list T),
    eqset l [x]
    -> remove_duplicates dec l = [x].
Proof.
  induction l; introv eqs; simpl in *.
  { apply eqset_nil_l in eqs; auto. }
  { pose proof (eqs a) as q; simpl in q.
    destruct q as [q1 q2].
    clear q2.
    autodimp q1 hyp; repndors; subst; tcsp.
    dest_cases w; auto.
    { apply IHl; introv; split; intro h; auto; simpl in *.
      { apply eqs; simpl; auto. }
      { apply eqs in h; simpl in h; repndors; subst; tcsp. }
    }
    { destruct l; simpl in *; GC.
      { apply eqset_singleton_lr in eqs; subst; auto. }
      { apply not_or in n; repnd.
        pose proof (eqs t) as q.
        destruct q as [q1 q2]; simpl in *.
        clear q2.
        autodimp q1 hyp; repndors; subst; tcsp. }
    }
  }
Qed.

Definition DumState : state := fun _ => DumR.

Fixpoint vec_all {n : nat} (l : Vector.t bool n) : bool :=
  match l with
  | Vector.nil => true
  | Vector.cons x _ t => x && vec_all t
  end.

Fixpoint nodiff (t : Term) : bool :=
  match t with
  | KTdot _           => true
  | KTfuncOf f _ args => vec_all (Vector.map nodiff args)
  | KTnumber r     => true
  | KTread x       => true
  | KTneg    l     => nodiff l
  | KTplus   l r   => nodiff l && nodiff r
  | KTminus  l r   => nodiff l && nodiff r
  | KTtimes  l r   => nodiff l && nodiff r
  | KTdifferential theta => false
  end.

Lemma subset_free_vars_term_singleton_implies :
  forall u (v : KVariable),
    nodiff u = true
    -> subset (free_vars_term u) [KAssignVar v]
    ->
    (
      (
        null (free_vars_term u)
        /\ null (term_assignables_nodup u)
      )
      \/
      (
        List.In (KAssignVar v) (free_vars_term u)
        /\ term_assignables_nodup u = [KAssignVar v]
      )
    ).
Proof.
  term_ind u Case; introv nod ss; simpl in *; auto;
    try (complete (unfold term_assignables_nodup; simpl; left; dands; reflexivity));
    try (complete (apply subset_app_l in ss; repnd;
                   allrw andb_true_iff; repnd;
                   apply IHu1 in ss0; apply IHu2 in ss; auto;
                   rewrite null_app; repndors; repnd;
                   [ left; rewrite ss1, ss2; dands; try reflexivity;
                     apply implies_remove_duplicates_app_prop1; auto
                   | right; rewrite ss1; autorewrite with core;
                     dands; auto; unfold term_assignables_nodup; simpl;
                     rewrite implies_remove_duplicates_app_prop3; auto
                   | right; rewrite ss2; simpl;
                     dands; auto; unfold term_assignables_nodup; simpl;
                     rewrite implies_remove_duplicates_app_prop2; auto
                   | right; rewrite in_app_iff; dands; auto;
                     unfold term_assignables_nodup; simpl;
                     rewrite implies_remove_duplicates_app_prop4; auto;
                     eapply subset_trans;
                     [apply eqset_implies_subset;apply eqset_sym;apply free_vars_term_nodup_eqset|];
                     eapply subset_trans;
                     [|apply eqset_implies_subset;apply free_vars_term_nodup_eqset];
                     rewrite ss0, ss; auto
                   ])).

  { Case "KTfuncOf".
    revert nod IHargs ss.
    induction n.

    { apply Vector.case0 with (v := args); simpl; clear args.
      introv nod IHargs ss; clear IHargs.
      left.
      unfold term_assignables_nodup; simpl; dands; reflexivity. }

    { apply (Vector.caseS' args); clear args; introv nod IHargs ss.
      simpl in *.
      allrw andb_true_iff; repnd.
      apply subset_app_l in ss; repnd.
      rewrite null_app.
      rewrite in_app_iff.

      pose proof (IHn t) as q; clear IHn.
      repeat (autodimp q hyp).
      { introv i ss'.
        apply IHargs; auto.
        constructor; auto. }

      apply IHargs in ss0; try (complete constructor); auto.

      clear IHargs.

      repndors; repnd.

      { left; dands; auto.
        unfold term_assignables_nodup; simpl.
        apply implies_remove_duplicates_app_prop1; auto. }

      { clear ss.
        unfold term_assignables_nodup in *; simpl in *.
        right.
        rewrite q0; simpl.
        dands; auto.
        rewrite implies_remove_duplicates_app_prop3; auto; simpl; tcsp. }

      { rewrite ss1; clear ss1.
        unfold term_assignables_nodup in *; simpl in *.
        right.
        dands; auto.
        rewrite implies_remove_duplicates_app_prop2; auto. }

      { right; dands; auto.
        unfold term_assignables_nodup in *; simpl in *.
        rewrite implies_remove_duplicates_app_prop4; auto.
        eapply subset_trans;
          [apply eqset_implies_subset;apply eqset_sym;apply free_vars_term_nodup_eqset|].
        unfold term_assignables_nodup; rewrite ss0; clear ss0.
        eapply subset_trans;
          [|apply eqset_implies_subset;apply (remove_duplicates_eqset KAssignable_dec)].
        rewrite q; auto. }
    }
  }

  { Case "KTread".
    apply subset_cons_l in ss; repnd; clear ss.
    simpl in ss0; repndors; subst; tcsp. }

  { Case "KTdifferential".
    ginv.
(*    apply subset_app_l in ss; repnd.
    rewrite null_app.
    rewrite in_app_iff.
    apply IHu in ss0; repndors; repnd.

    { left; dands; auto.
      { rewrite ss1; simpl; try reflexivity. }
      { unfold term_assignables_nodup; simpl.
        rewrite implies_remove_duplicates_app_prop3; auto.
        apply remove_duplicate_map_KD; auto. }
    }

    { right; dands; auto.
      unfold term_assignables_nodup; simpl.
    }*)
  }
Qed.

(* Lemma 12, but only for terms with no differentials for now *)
Lemma differential_space_time :
  forall (v : KVariable) I r phi z u,
    nodiff u = true
    -> (0 <= r)%R
    -> (forall (zeta : preal_upto r),
           ex_derive_R (fun t => phi t (KAssignVar v)) zeta
           /\ phi zeta (DVar v)
              = Derive (fun t => phi t (KAssignVar v)) zeta)
    -> (0 <= z)%R
    -> (z <= r)%R
    -> subset (free_vars_term u) [KAssignVar v]
    -> dynamic_semantics_term I (phi z) (KTdifferential u)
       = Derive (fun t => dynamic_semantics_term I (phi t) u) z.
Proof.
  introv nod lt0r cond le0z lezr ss; simpl in *.

  applydup subset_free_vars_term_singleton_implies in ss; repndors; repnd; auto.

  {
    rewrite ss0; simpl; symmetry.
    erewrite Derive_ext;[|introv; apply (coincidence_term _ _ DumState _ I)]; auto.
    { apply Derive_const. }
    { rewrite ss1; auto. }
  }

  {
    rewrite ss0; simpl.
    autorewrite with core.

    assert (eqset (free_vars_term u) [KAssignVar v]) as eqs.
    { introv; split; intro h; auto.
      simpl in h; repndors; subst; tcsp. }

    pose proof (cond (mk_preal_upto r (mk_preal z le0z) lezr)) as q; simpl in q; repnd.

    assert (phi z (KD (KAssignVar v)) = Derive (fun t : R => phi t (KAssignVar v)) z) as xx by auto.
    rewrite xx; clear xx.

    pose proof (Derive_comp
                  (fun X : R => dynamic_semantics_term I (upd_state (phi z) (KAssignVar v) X) u)
                  (fun t : R => phi t (KAssignVar v))
                  z) as comp.
    simpl in comp.
    rewrite <- comp; auto; clear comp;
      try (complete apply (ex_partial_derive_st_pt_dynamic_semantics_term
                             u I (KAssignVar v) [] (phi z (KAssignVar v)) (phi z))).

    apply Derive_ext; introv.
    apply coincidence_term; auto.
    introv i; apply eqs in i; simpl in i; repndors; subst; tcsp.
    autorewrite with core; auto.
  }
Qed.
