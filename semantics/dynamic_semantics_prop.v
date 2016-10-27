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


Require Export dynamic_semantics.
Require Export semantics_util.
Require Export terms_util2.
Require Export list_util.


(**

   In the dynamic semantics of terms we derived terms without
   knowing that they're actually derivable.  Here we prove that
   they're actually derivable.

   Definitions and lemmas from this file are used in US lemmas proofs.

   Also, this file needs some cleaning up because it contains some old
   definitions that are not used anymore.

 *)


(* Use [Vector.t R] instead? *)
Inductive Rn : nat -> Type :=
| Rn0 : Rn 0
| RnS : forall n, R -> Rn n -> Rn (S n).

Definition Rn2R {n} (a : Rn n) : R :=
  match a with
  | Rn0 => DumR
  | RnS _ r _ => r
  end.

Definition RnTl {n} (a : Rn n) : Rn (Nat.pred n) :=
  match a with
  | Rn0 => Rn0
  | RnS _ _ rn => rn
  end.

Fixpoint RnLast {n : nat} (rs : Rn n) : R :=
  match rs with
  | Rn0 => DumR
  | RnS 0 r _ => r
  | RnS m r rs => RnLast rs
  end.

Fixpoint RnSnoc {n : nat} (rs : Rn n) (r : R) : Rn (S n) :=
  match rs with
  | Rn0 => RnS 0 r Rn0
  | RnS m r' rs => RnS (S m) r' (RnSnoc rs r)
  end.

Fixpoint RnIS {n : nat} (rs : Rn n) : Rn (Nat.pred n) :=
  match rs in Rn n return Rn (Nat.pred n) with
  | Rn0 => Rn0
  | RnS 0 _ _ => Rn0
  | RnS (S m) r rs => RnS m r (RnIS rs)
  end.

Fixpoint partial_derive_at (n : nat) : (Rn n -> R) -> Rn n -> R :=
  match n with
  | 0 => fun f pts => f pts
  | S m =>
    fun (f : Rn (S m) -> R) (pts : Rn (S m)) =>
      Derive
        (fun x : R => partial_derive_at m (fun a : Rn m => f (RnS m x a)) (RnTl pts))
        (Rn2R pts)
  end.

Definition DumKVar : KVariable := variable "".

(* Use [Vector.t KVariable] instead? *)
Inductive KVarn : nat -> Type :=
| KV0 : KVarn 0
| KVS : forall n, KVariable -> KVarn n -> KVarn (S n).

Definition KVarn2KVar {n} (a : KVarn n) : KVariable :=
  match a with
  | KV0 => DumKVar
  | KVS _ r _ => r
  end.

Definition KVarnTl {n} (a : KVarn n) : KVarn (Nat.pred n) :=
  match a with
  | KV0 => KV0
  | KVS _ _ rn => rn
  end.

Fixpoint KVarnLast {n : nat} (vs : KVarn n) : KVariable :=
  match vs with
  | KV0 => DumKVar
  | KVS 0 v _ => v
  | KVS m v vs => KVarnLast vs
  end.

Fixpoint KVarnSnoc {n : nat} (vs : KVarn n) (v : KVariable) : KVarn (S n) :=
  match vs with
  | KV0 => KVS 0 v KV0
  | KVS m v' vs => KVS (S m) v' (KVarnSnoc vs v)
  end.

Fixpoint KVarnIS {n : nat} (vs : KVarn n) : KVarn (Nat.pred n) :=
  match vs in KVarn n return KVarn (Nat.pred n) with
  | KV0 => KV0
  | KVS 0 _ _ => KV0
  | KVS (S m) v vs => KVS m v (KVarnIS vs)
  end.

Definition DumVR : (KVariable * R) := (DumKVar, DumR).

Definition S2R :=  state -> R.

(* Use [Vector.t] instead? *)
Inductive VRn : nat -> Type :=
| VR0 : VRn 0
| VRS : forall n, KVariable -> R -> VRn n -> VRn (S n).

Definition VRn2V {n} (a : VRn n) : KVariable :=
  match a with
  | VR0 => DumKVar
  | VRS _ v _ _ => v
  end.

Definition VRn2R {n} (a : VRn n) : R :=
  match a with
  | VR0 => DumR
  | VRS _ _ r _ => r
  end.

Definition VRnTl {n} (a : VRn n) : VRn (Nat.pred n) :=
  match a with
  | VR0 => VR0
  | VRS _ _ _ tl => tl
  end.

Fixpoint VRnLastV {n : nat} (l : VRn n) : KVariable :=
  match l with
  | VR0 => DumKVar
  | VRS 0 v _ _ => v
  | VRS _ _ _ l => VRnLastV l
  end.

Fixpoint VRnLastR {n : nat} (l : VRn n) : R :=
  match l with
  | VR0 => DumR
  | VRS 0 _ r _ => r
  | VRS _ _ _ l => VRnLastR l
  end.

Fixpoint VRnSnoc {n : nat} (l : VRn n) (v : KVariable) (r : R) : VRn (S n) :=
  match l with
  | VR0 => VRS 0 v r VR0
  | VRS m v' r' l => VRS (S m) v' r' (VRnSnoc l v r)
  end.

Fixpoint VRnIS {n : nat} (l : VRn n) : VRn (Nat.pred n) :=
  match l in VRn n return VRn (Nat.pred n) with
  | VR0 => VR0
  | VRS 0 _ _ _ => VR0
  | VRS (S m) v r l => VRS m v r (VRnIS l)
  end.

Lemma partial_derive_st_test_2 :
  forall f v s,
    partial_derive f [v,v] s
    = Derive_n
        (fun r => f (upd_state s v r))
        2
        (s v).
Proof.
  introv; simpl.
  apply Derive_ext; introv.
  rewrite upd_state_same.
  apply Derive_ext; introv.
  rewrite upd_state_twice; auto.
Qed.

Lemma partial_derive_st_test_3 :
  forall f v s,
    partial_derive f [v,v,v] s
    = Derive_n
        (fun r => f (upd_state s v r))
        3
        (s v).
Proof.
  introv; simpl.
  apply Derive_ext; introv.
  rewrite upd_state_same.
  apply Derive_ext; introv.
  rewrite upd_state_same.
  rewrite upd_state_twice; auto.
  apply Derive_ext; introv.
  rewrite upd_state_twice; auto.
Qed.

Lemma partial_derive_st_const :
  forall c l st,
    (0 < List.length l)%nat -> partial_derive (fun _ => c) l st = 0%R.
Proof.
  induction l; introv h; simpl in *; try omega.
  destruct (deq_nat (List.length l) 0); subst.
  { destruct l; simpl in *; ginv.
    rewrite Derive_const; auto. }
  { rewrite (Derive_ext _ (fun _ => 0%R));
      try (introv; apply IHl; omega).
    apply Derive_const. }
Qed.

Lemma partial_derive_st_const0 :
  forall (l : list KAssignable) (st : state),
    partial_derive (fun _ : state => 0%R) l st = 0%R.
Proof.
  destruct l; introv.
  { simpl; auto. }
  { apply partial_derive_st_const; simpl; omega. }
Qed.

Lemma partial_derive_st_plus :
  forall l st L R,
    (forall k, (k <= List.length l)%nat -> ex_nth_partial_derive_st k L)
    -> (forall k, (k <= List.length l)%nat -> ex_nth_partial_derive_st k R)
    -> partial_derive (fun s => (L s + R s)%R) l st
       = (partial_derive L l st
          + partial_derive R l st)%R.
Proof.
  induction l; introv dL dR; simpl in *; auto.
  erewrite Derive_ext;[|introv;apply IHl;auto].
  rewrite Derive_plus; auto.
  { apply (dL (List.length l)); auto. }
  { apply (dR (List.length l)); auto. }
Qed.

Lemma partial_derive_st_plus_sublist :
  forall l st L R,
    (forall v k, sublist (v :: k) l -> ex_partial_derive L v k)
    -> (forall v k, sublist (v :: k) l -> ex_partial_derive R v k)
    -> partial_derive (fun s => (L s + R s)%R) l st
       = (partial_derive L l st
          + partial_derive R l st)%R.
Proof.
  induction l; introv dL dR; simpl in *; auto.
  erewrite Derive_ext;[|introv;apply IHl;auto].

  rewrite Derive_plus; auto.

  { apply dL.
    apply sublist_refl. }

  { apply dR.
    apply sublist_refl. }
Qed.

Lemma ex_nth_partial_derive_st_big_sum :
   forall (vs : list KAssignable) n (F : state -> KAssignable -> R),
    (forall v k, (k <= n)%nat -> List.In v vs -> ex_nth_partial_derive_st k (fun s => F s v))
    -> ex_nth_partial_derive_st n (fun s => big_sum vs (F s)).
Proof.
  induction vs; simpl; introv imp len; unfold ex_partial_derive_st_l.

  { destruct (deq_nat n 0) as [d|d]; subst; simpl in *.

    {
      destruct l; allsimpl; ginv.
      apply @ex_derive_const.
    }

    {
      eapply ex_derive_ext;[introv;symmetry;apply partial_derive_st_const;omega|].
      apply @ex_derive_const.
    }
  }

  {
    eapply ex_derive_ext;[introv;symmetry;apply partial_derive_st_plus|].

    { introv w; auto.
      apply imp; auto; try omega. }

    { introv w1.
      apply IHvs; introv w2 w3.
      apply imp; auto; try omega. }

    { apply @ex_derive_plus.
      { apply (imp a (List.length l)); auto; try omega. }
      { apply (IHvs (List.length l)); auto.
        introv h1 h2; apply imp; tcsp; try omega. }
    }
  }
Qed.

Definition DumKAssign : KAssignable := KAssignVar (variable "").

Definition lastv (l : list KAssignable) : KAssignable :=
  last l DumKAssign.

Lemma lastv_snoc :
  forall v l,
    lastv (snoc l v) = v.
Proof.
  unfold lastv; induction l; simpl; auto.
  rewrite IHl.
  destruct l; simpl; auto.
Qed.
Hint Rewrite lastv_snoc : core.

Lemma partial_derive_st_S :
  forall f l st,
    (0 < List.length l)%nat
    -> partial_derive f l st
       = partial_derive
           (fun s =>
              Derive
                (fun x => f (upd_state s (lastv l) x))
                (s (lastv l)))
           (removelast l)
           st.
Proof.
  induction l as [l ind] using list_ind_len; introv len.
  destruct (snoc_cases l) as [h|h]; exrepnd; subst; simpl in *; try omega.
  autorewrite with core in *.
  destruct k as [|v l]; simpl in *; auto.
  apply Derive_ext; introv.
  rewrite ind; autorewrite with core; try omega; auto.
Qed.

Lemma length_removelast :
  forall {T} (l : list T), List.length (removelast l) = Nat.pred (List.length l).
Proof.
  induction l; simpl; auto.
  destruct l; simpl; auto.
Qed.

Lemma ex_nth_partial_derive_st_add_Derive :
  forall n F v,
    ex_nth_partial_derive_st (S n) F
    -> ex_nth_partial_derive_st
         n
         (fun s => Derive (fun x => F (upd_state s v x)) (s v)).
Proof.
  introv d len.
  pose proof (d st (snoc l v) v0) as q.
  autorewrite with core in *.
  autodimp q hyp.
  eapply ex_derive_ext in q;
    [|introv;apply partial_derive_st_S;autorewrite with core;omega].
  simpl in q.
  eapply ex_derive_ext;[clear q|exact q].
  introv; simpl.
  autorewrite with core in *; auto.
Qed.

Lemma ex_all_partial_derive_st_add_Derive :
  forall F v,
    ex_all_partial_derive_st F
    -> ex_all_partial_derive_st
         (fun s => Derive (fun x => F (upd_state s v x)) (s v)).
Proof.
  introv d len.
  apply (ex_nth_partial_derive_st_add_Derive n); auto.
Qed.

Lemma upd_state_var_eq :
  forall s v r a,
    upd_state_var s v r a
    = if KAssignable_dec a (KAssignVar v)
      then r
      else s a.
Proof.
  sp.
Qed.

Lemma upd_state_var_eq2 :
  forall s v r w,
    upd_state_var s v r (KAssignVar w)
    = if KVariable_dec w v
      then r
      else s (KAssignVar w).
Proof.
  introv; rewrite upd_state_var_eq; repeat (dest_cases w); subst; tcsp.
Qed.

(* Can we do without function extensionality here?
   Use lists instead of functions? *)
Lemma upd_state_swap :
  forall st a1 r1 a2 r2,
    upd_state (upd_state st a1 r1) a2 r2
    = if KAssignable_dec a1 a2
      then upd_state st a2 r2
      else upd_state (upd_state st a2 r2) a1 r1.
Proof.
  introv.
  unfold upd_state.
  apply functional_extensionality; introv.
  destruct (KAssignable_dec x a2) as [d1|d1]; subst; tcsp;
    destruct (KAssignable_dec a1 a2) as [d2|d2]; subst; tcsp;
      try (destruct (KAssignable_dec a2 a2) as [d3|d3]; subst; tcsp);
      try (destruct (KAssignable_dec a2 a1) as [d4|d4]; subst; tcsp);
      try (destruct (KAssignable_dec x a1) as [d5|d5]; subst; tcsp);
      try (destruct (KAssignable_dec x a2) as [d6|d6]; subst; tcsp).
Qed.

Lemma upd_state_var_swap :
  forall st a1 r1 a2 r2,
    upd_state_var (upd_state_var st a1 r1) a2 r2
    = if KVariable_dec a1 a2
      then upd_state_var st a2 r2
      else upd_state_var (upd_state_var st a2 r2) a1 r1.
Proof.
  introv.
  unfold upd_state_var.
  rewrite upd_state_swap.
  destruct (KVariable_dec a1 a2) as [d1|d1];
    destruct (KAssignable_dec (KAssignVar a1) (KAssignVar a2)) as [d2|d2];
    subst; tcsp.
  inversion d2; tcsp.
Qed.

Lemma upd_state_eq2 :
  forall s v r w,
    upd_state s v r w
    = if KAssignable_dec w v
      then r
      else s w.
Proof.
  introv; unfold upd_state; auto.
Qed.

Lemma partial_derive_st_ext2 :
  forall f g l v w,
    (forall a, v a = w a)
    -> (forall s1 s2, (forall a, s1 a = s2 a) -> f s1 = g s2)
    -> partial_derive f l v = partial_derive g l w.
Proof.
  induction l; introv exts imp; simpl; auto.
  rewrite exts.
  apply Derive_ext; introv.
  apply IHl; auto.
  introv.
  unfold upd_state; dest_cases w.
Qed.

Lemma partial_derive_st_add_upd :
  forall F l st v r,
    ~ (List.In v l)
    -> partial_derive F l (upd_state st v r)
       = partial_derive (fun s => F (upd_state s v r)) l st.
Proof.
  induction l; introv h; simpl in *; auto.
  apply not_or in h; repnd.
  rewrite (upd_state_eq2 st v r a).
  dest_cases w.
  apply Derive_ext; introv; simpl.
  rewrite upd_state_swap.
  dest_cases w.
Qed.

Lemma partial_derive_st_add_upd2 :
  forall F l s v,
    ~ List.In v l
    -> partial_derive F l (upd_state s v (s v))
       = partial_derive (fun s => F (upd_state s v (s v))) l s.
Proof.
  induction l; introv h; simpl in *; auto.
  apply not_or in h; repnd.
  rewrite (upd_state_eq2 s v (s v) a); dest_cases w; GC.
  apply Derive_ext; introv; simpl.
  rewrite upd_state_swap.
  dest_cases w; subst.
  pose proof (IHl (upd_state s a t) v) as q; autodimp q hyp.
  rewrite upd_state_eq2 in q; dest_cases w.
Qed.

Lemma ex_nth_partial_derive_st_ext :
  forall n F G,
    (forall s, F s = G s)
    -> ex_nth_partial_derive_st n F
    -> ex_nth_partial_derive_st n G.
Proof.
  introv imp d len; simpl.
  eapply ex_derive_ext;[|apply d;exact len].
  simpl; introv.
  apply partial_derive_st_ext; auto.
Qed.

      (*
Lemma ex_nth_partial_derive_st_add_upd :
  forall n F v,
    ex_nth_partial_derive_st n F
    -> ex_nth_partial_derive_st n (fun s => F (upd_state_var s v (s (KAssignVar v)))).
Proof.
  introv d len; simpl.

  destruct (in_dec KVariable_dec v l) as [d1|d1].

  {
    (* v in l *)

    
  }

  {

    (* not (v in l) *)

    eapply ex_derive_ext;[introv;apply partial_derive_st_add_upd2;auto|]; simpl.
    eapply ex_derive_ext;[introv;rewrite upd_state_var_swap;reflexivity|]; simpl.
    dest_cases w; subst; simpl.
    { eapply ex_derive_ext;[introv;rewrite (upd_state_var_same st v t);reflexivity|]; simpl.
      apply d; auto. }
    { eapply ex_derive_ext;[introv;rewrite (upd_state_var_eq2 st v0 t v);dest_cases w|]; simpl.
      pose proof (d (upd_state_var st v (st (KAssignVar v))) l v0) as q; simpl in q.
      rewrite upd_state_var_eq2 in q; dest_cases w; GC.
      apply q; auto.
    }


Lemma partial_derive_st_upd_in :
  forall l F st v,
    List.In v l
    -> partial_derive_st (fun s => F (upd_state_var s v (s (KAssignVar v)))) l st
       = 0.
Proof.
  induction l; introv h; simpl in *; auto; tcsp; repndors; subst.

  {

Lemma partial_derive_st_upd_same :
  forall F v r s l,
    partial_derive_st
      (fun s => F (upd_state_var s v (s (KAssignVar v))))
      l
      (upd_state_var s v r)
    = partial_derive_st
        (fun s => F (upd_state_var s v r))
        l
        s.
Proof.
  induction l; introv; simpl; auto.

  {
    rewrite upd_state_var_same.
    rewrite upd_state_var_twice; auto.
  }

  {
    apply Derive_ext; introv.
    rewrite upd_state_var_swap.
    dest_cases w.
  }
Qed.
Hint Rewrite partial_derive_st_upd_same : core.
    erewrite Derive_ext;
      [|introv;rewrite partial_derive_st_upd_same;reflexivity].
    apply Derive_const.
  }

  {
    match goal with
    | [ H : _ = _ |- _ ] => apply inj_pair2_eq_dec in H
    end; subst; tcsp; try (apply deq_nat).
    erewrite Derive_ext;
      [|introv;apply IHl;auto].
    apply Derive_const.
  }
Qed.

    eapply ex_derive_ext;[introv;symmetry;apply partial_derive_st_upd_in;auto|].
    apply ex_derive_const.
  }

  {
    eapply ex_derive_ext;[introv;apply partial_derive_st_add_upd;auto|].
    eapply ex_derive_ext;[introv;rewrite upd_state_var_swap;reflexivity|].
    dest_cases w; subst.
    { apply ex_derive_const. }
    { apply d.  }
  }
Qed.
       *)

Lemma length_removelast_cons :
  forall {T} (v : T) l,
    List.length (removelast (v :: l)) = List.length l.
Proof.
  induction l; simpl in *; auto.
  rewrite <- IHl.
  destruct l; simpl; auto.
Qed.
Hint Rewrite @length_removelast_cons.

Lemma ex_nth_partial_derive_st_mult :
  forall (L R : state -> R) n,
    (forall k, (k <= n)%nat -> ex_nth_partial_derive_st k L)
    -> (forall k, (k <= n)%nat -> ex_nth_partial_derive_st k R)
    -> ex_nth_partial_derive_st n (fun st => (L st * R st)%R).
Proof.
  introv dL dR; simpl.
  revert L R dL dR.
  induction n as [n IHn] using comp_ind; introv dL dR len.
  destruct n.

  {
    destruct l; simpl in *; ginv.
    apply ex_derive_mult.
    { apply (dL 0%nat (le_n 0) st []); simpl; auto. }
    { apply (dR 0%nat (le_n 0) st []); simpl; auto. }
  }

  {
    eapply ex_derive_ext;
      [introv;symmetry;apply partial_derive_st_S;omega
      |].
    simpl.

    eapply ex_derive_ext; simpl;
      [introv; symmetry;
       apply partial_derive_st_ext;
       introv;apply Derive_mult
      |].

    { apply (dL 0%nat (Peano.le_0_n _) s []); tcsp. }
    { apply (dR 0%nat (Peano.le_0_n _) s []); tcsp. }

    {
      simpl.
      eapply ex_derive_ext; simpl;
        [introv; symmetry;apply partial_derive_st_plus;simpl
        |];[| |].

      {
        introv h.
        rewrite length_removelast in h.
        apply IHn; clear IHn; try omega.
        { introv w; apply ex_nth_partial_derive_st_add_Derive; auto.
          apply dL; try omega. }
        { introv w; simpl.
          eapply ex_nth_partial_derive_st_ext;
            [introv;symmetry;rewrite upd_state_ext;reflexivity|].
          apply dR; try omega. }
      }

      {
        introv h; simpl.
        rewrite length_removelast in h.
        apply IHn; clear IHn; try omega.
        { introv w.
          eapply ex_nth_partial_derive_st_ext;
            [introv;symmetry;rewrite upd_state_ext;reflexivity|].
          apply dL; try omega. }
        { introv w; apply ex_nth_partial_derive_st_add_Derive; auto.
          apply dR; try omega. }
      }

      simpl.
      apply @ex_derive_plus; simpl.

      {
        destruct l as [|k l]; simphyps; try omega; ginv.
        pose proof (IHn (List.length l)) as q; autodimp q hyp.
        apply (q (fun s =>
                    Derive
                      (fun x0 =>
                         L (upd_state s (lastv (k :: l)) x0))
                      (s (lastv (k :: l))))
                 (fun s =>
                    R
                      (upd_state s (lastv (k :: l))
                                 (s (lastv (k :: l))))));
          autorewrite with core in *; auto.
        { introv w; apply ex_nth_partial_derive_st_add_Derive; auto.
          apply dL; try omega. }
        { introv w.
          eapply ex_nth_partial_derive_st_ext;
            [introv;symmetry;rewrite upd_state_ext;reflexivity|].
          apply dR; try omega. }
      }

      {
        destruct l as [|k l]; simphyps; try omega; ginv.
        pose proof (IHn (List.length l)) as q; autodimp q hyp.
        apply (q (fun s =>
                    L (upd_state s (lastv (k :: l))
                                 (s (lastv (k :: l)))))
                 (fun s =>
                    Derive
                      (fun x0 =>
                         R (upd_state s (lastv (k :: l)) x0))
                      (s (lastv (k :: l)))));
          autorewrite with core in *; auto.
        { introv w.
          eapply ex_nth_partial_derive_st_ext;
            [introv;symmetry;rewrite upd_state_ext;reflexivity|].
          apply dL; try omega. }
        { introv w; apply ex_nth_partial_derive_st_add_Derive; auto.
          apply dR; try omega. }
      }
    }
  }
Qed.

Lemma ex_all_partial_derive_st_read :
  forall x, ex_all_partial_derive_st (fun S => S x).
Proof.
  introv; introv.
  induction n; introv len; unfold ex_partial_derive_st_l.

  { destruct l; simpl in *; ginv.
    unfold upd_state_var, upd_state.
    dest_cases w; subst;
      [apply @ex_derive_id|apply @ex_derive_const].
  }

  { eapply ex_derive_ext;
      [introv;symmetry;apply partial_derive_st_S;omega|].
    simpl.
    unfold upd_state_var, upd_state at 1.
    dest_cases w; subst.

    { eapply ex_derive_ext;
        [introv;symmetry;apply partial_derive_st_ext;introv;apply Derive_id|].
      simpl.
      destruct (deq_nat n 0); subst; simpl.
      { repeat (destruct l; simpl in *; ginv).
        apply @ex_derive_const. }
      eapply ex_derive_ext;
        [introv;symmetry;apply partial_derive_st_const;rewrite length_removelast;omega|].
      apply @ex_derive_const.
    }

    { eapply ex_derive_ext;
        [introv; symmetry;apply partial_derive_st_ext;introv;apply Derive_const|].
      simpl.
      destruct (deq_nat n 0); subst; simpl.
      { repeat (destruct l; simpl in *; ginv).
        apply @ex_derive_const. }
      eapply ex_derive_ext;
        [introv;symmetry;apply partial_derive_st_const;rewrite length_removelast;omega|].
      apply @ex_derive_const.
    }
  }
Qed.

Lemma partial_derive_st_KAssignVar_prop1 :
  forall F l st v,
    ~ List.In v l
    -> partial_derive (fun s => Derive (F s) (s v)) l st
       = partial_derive (fun s => Derive (F s) (st v)) l st.
Proof.
  induction l; introv nin; simpl in *; auto.
  apply not_or in nin; repnd.
  apply Derive_ext; introv.
  rewrite (IHl (upd_state st a t) v); auto; clear IHl.
  apply partial_derive_st_ext; introv.
  rewrite upd_state_eq2.
  dest_cases w.
Qed.

Lemma ex_all_partial_derive_st_differential :
  forall vs T,
    ex_all_partial_derive_st T
    -> ex_all_partial_derive_st
         (fun v : state =>
            big_sum
              vs
              (fun x : KAssignable =>
                 (v (KD x)
                  *
                  Derive (fun X => T (upd_state v x X)) (v x)))%R).
Proof.
  introv dT; introv.
  apply ex_nth_partial_derive_st_big_sum; introv w i.

  apply ex_nth_partial_derive_st_mult.

  {
    introv lk.
    apply ex_all_partial_derive_st_read.
  }

  introv lk len; simpl.
  pose proof (dT (S k0) st (snoc l v) v0) as h; simpl in h.
  autorewrite with core in *; autodimp h hyp;[].
  eapply ex_derive_ext in h;
    [|introv;apply partial_derive_st_S; autorewrite with core; try omega].
  simpl in *; autorewrite with core in *.
  auto.
Qed.

Lemma ex_all_partial_derive_st_constant :
  forall c, ex_all_partial_derive_st (fun _ => c).
Proof.
  introv len; unfold ex_partial_derive_st_l; simpl.
  destruct l.
  { simpl; apply @ex_derive_const. }
  { apply (@ex_derive_ext
             Hierarchy.R_AbsRing
             Hierarchy.R_NormedModule
             (fun _ => 0%R)).
    { introv.
      rewrite partial_derive_st_const; simpl; try omega; auto. }
    { simpl; apply @ex_derive_const. }
  }
Qed.

Lemma ex_all_partial_derive_st_plus :
  forall (L R : state -> R),
    ex_all_partial_derive_st L
    -> ex_all_partial_derive_st R
    -> ex_all_partial_derive_st (fun st => (L st + R st)%R).
Proof.
  introv d1 d2 len; simpl in *.
  eapply ex_derive_ext;
    [introv;symmetry;apply partial_derive_st_plus; auto|].
  apply @ex_derive_plus;[apply (d1 n)|apply (d2 n)];auto.
Qed.

(*
   This shows that [ex_partial_derive_st_func] might not be that bogus after all.
 *)
Lemma ex_partial_derive_st_func_plus_vector : ex_partial_derive_st_func plus_vector.
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
                        | @Vector.nil _ => (G s h + G s h0)%R
                        | @Vector.cons _ _ _ _ => 0%R
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

  apply ex_all_partial_derive_st_plus; auto.
Qed.

Lemma ex_partial_derive_st_l_pt_plus :
  forall (L R : state -> R) v l,
    (forall w l', sublist (w :: l') (v :: l) -> ex_partial_derive L w l')
    -> (forall w l', sublist (w :: l') (v :: l) -> ex_partial_derive R w l')
    -> ex_partial_derive (fun st => (L st + R st)%R) v l.
Proof.
  introv d1 d2; introv; simpl in *.
  eapply ex_derive_ext;
    [introv;symmetry;apply partial_derive_st_plus_sublist; auto|].
  simpl.
  apply @ex_derive_plus; simpl;[apply d1|apply d2];apply sublist_refl.
Qed.

(*
  Similar to [ex_partial_derive_st_func_plus_vector].  We show that
  [ex_partial_derive_st_func] make at least sense for Rplus.
 *)
Lemma ex_partial_derive_st_func_sub_plus_vector :
  smooth_fun_T plus_vector.
Proof.
  introv d cond.
  unfold plus_vector; simpl.
  revert cond.
  apply (Vector.caseS' ts).
  introv; simpl.
  apply (Vector.caseS' t).
  introv; simpl.

  clear ts t.
  apply (@Vector.case0
                T
                (fun t0 =>
                   (forall t w l',
                       Vector.In t (Vector.cons T h 1 (Vector.cons T h0 0 t0)) ->
                       sublist (w :: l') (v :: l) ->
                       ex_partial_derive (fun s : state => G s t) w l') ->
                   ex_partial_derive
                     (fun s : state =>
                        match Vector.map (G s) t0 return R with
                        | @Vector.nil _ => (G s h + G s h0)%R
                        | @Vector.cons _ _ _ _ => 0%R
                        end) v l)).
  simpl.
  clear t0.
  introv ih.
  rename h into x.
  rename h0 into y.

  pose proof (ih x) as h1.
  pose proof (ih y) as h2.
  clear ih.

  apply ex_partial_derive_st_l_pt_plus; auto; introv ss;
    [apply h1|apply h2]; auto; repeat constructor.
Qed.

(* This is a generalization of plus_vector *)
Definition bin2vec (f : R -> R -> R) : Vector.t R 2%nat -> R :=
  fun v : Vector.t R 2%nat =>
    match v with
    | Vector.cons x 1 (Vector.cons y 0 Vector.nil) => f x y
    | _ => R0
    end.

(* This is a generalization of ex_partial_derive_st_func_plus_vector *)
Lemma ex_partial_derive_st_func_bin2vec :
  forall f,
    (forall (L R : state -> R),
        ex_all_partial_derive_st L
        -> ex_all_partial_derive_st R
        -> ex_all_partial_derive_st (fun st => f (L st) (R st)))
    -> ex_partial_derive_st_func (bin2vec f).
Proof.
  introv cond d; introv.
  unfold bin2vec; simpl.
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
                        | @Vector.nil _ => f (G s h) (G s h0)
                        | @Vector.cons _ _ _ _ => 0%R
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
  autodimp h2 hyp.
  repeat constructor.
Qed.

Lemma partial_derive_st_opp :
  forall l st L,
    (forall k, (k <= List.length l)%nat -> ex_nth_partial_derive_st k L)
    -> partial_derive (fun s => - (L s)) l st
       = - partial_derive L l st.
Proof.
  induction l; introv dL; simpl in *; auto.
  erewrite Derive_ext;[|introv;apply IHl;auto].
  rewrite Derive_opp; auto.
Qed.

Lemma partial_derive_st_opp_sublist :
  forall l st L,
    (forall v k, sublist (v :: k) l -> ex_partial_derive L v k)
    -> partial_derive (fun s => - L s) l st
       = - partial_derive L l st.
Proof.
  induction l; introv dL; simpl in *; auto.
  erewrite Derive_ext;[|introv;apply IHl;auto].
  rewrite Derive_opp; auto.
Qed.

Lemma ex_all_partial_derive_st_neg :
  forall L,
    ex_all_partial_derive_st L
    -> ex_all_partial_derive_st (fun s => - (L s)).
Proof.
  introv dL len.
  eapply ex_derive_ext;[introv;symmetry;apply partial_derive_st_opp;auto|];[].
  apply @ex_derive_opp.
  apply (dL n); auto.
Qed.

Lemma partial_derive_st_minus :
  forall l st L R,
    (forall k, (k <= List.length l)%nat -> ex_nth_partial_derive_st k L)
    -> (forall k, (k <= List.length l)%nat -> ex_nth_partial_derive_st k R)
    -> partial_derive (fun s => (L s - R s)%R) l st
       = (partial_derive L l st
          - partial_derive R l st)%R.
Proof.
  induction l; introv dL dR; simpl in *; auto.
  erewrite Derive_ext;[|introv;apply IHl;auto].
  rewrite Derive_minus; auto;[apply (dL (List.length l))|apply (dR (List.length l))];try omega.
Qed.

Lemma ex_all_partial_derive_st_minus :
  forall L R,
    ex_all_partial_derive_st L
    -> ex_all_partial_derive_st R
    -> ex_all_partial_derive_st (fun s => (L s - R s)%R).
Proof.
  introv d1 d2 len; simpl in *.
  eapply ex_derive_ext;[introv;symmetry;apply partial_derive_st_minus; auto|].
  apply @ex_derive_minus;[apply (d1 n)|apply (d2 n)]; auto.
Qed.

Lemma ex_all_partial_derive_st_mult :
  forall (L R : state -> R),
    ex_all_partial_derive_st L
    -> ex_all_partial_derive_st R
    -> ex_all_partial_derive_st (fun st => (L st * R st)%R).
Proof.
  introv dL dR; introv; simpl.
  apply ex_nth_partial_derive_st_mult; introv w; auto.
Qed.

Lemma ex_derive_all_n_implies_ex_derive :
  forall F,
    ex_derive_all_n F
    -> ex_derive_all F.
Proof.
  introv h; introv.
  pose proof (h 1%nat pt) as w; auto.
Qed.

Lemma implies_ex_derive_all_n_Derive :
  forall F,
    ex_derive_all_n F
    -> ex_derive_all_n (Derive F).
Proof.
  introv h; introv.
  pose proof (h (S n) pt) as q.
  apply ex_derive_n_S_implies in q; auto.
  pose proof (h 1%nat pt) as w; auto.
Qed.

Lemma ex_derive_partial_derive_st_comp :
  forall (F : R -> R) (A : state -> R) st v l,
    ex_all_partial_derive_st A
    -> ex_derive_all_n F
    -> ex_derive_R
         (fun X =>
            partial_derive
              (fun s => F (A s))
              l
              (upd_state st v X))
         (st v).
Proof.
  introv.
  remember (List.length l) as n.
  revert F A st v l Heqn.
  induction n as [n IHn] using comp_ind; introv e dA dF; subst.
  destruct l as [|k l].

  {
    simpl.
    apply @ex_derive_comp.
    { apply ex_derive_all_n_implies_ex_derive in dF; apply dF. }
    apply (dA 0%nat st []); simpl; auto.
  }

  {
    eapply ex_derive_ext;
      [introv;symmetry;
       apply (partial_derive_st_S (fun s : state => F (A s)));
       simpl; try omega|].
    remember (k :: l) as L.
    simpl.

    eapply ex_derive_ext; simpl;
      [introv; symmetry;
       apply partial_derive_st_ext;
       introv;apply Derive_comp
      |].

    { apply ex_derive_all_n_implies_ex_derive in dF; apply dF. }

    { apply (dA 0%nat s []); simpl; auto. }

    {
      simpl.
      apply (ex_nth_partial_derive_st_mult _ _ (List.length (removelast L)));auto.
      { introv w; apply ex_nth_partial_derive_st_add_Derive; auto. }
      { introv w len.
        rewrite HeqL in w; autorewrite with core in *.
        apply (IHn k0);auto;[subst; simpl; try omega| |].

        { eapply ex_all_partial_derive_st_ext;
            [introv;symmetry;rewrite upd_state_ext;reflexivity|]; auto. }

        { apply implies_ex_derive_all_n_Derive; auto. }
      }
    }
  }
Qed.

Lemma ex_partial_derive_st_func_l_plus_vector : ex_partial_derive_st_func_l plus_vector.
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
                       ex_partial_derive_st_l (fun s : state => G s t) st l v) ->
                   ex_partial_derive_st_l
                     (fun s : state =>
                        match Vector.map (G s) t0 return R with
                        | @Vector.nil _ => (G s h + G s h0)%R
                        | @Vector.cons _ _ _ _ => 0%R
                        end) st l v)).
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

  pose proof (ex_all_partial_derive_st_plus (fun s => G s x) (fun s => G s y)) as h.
  repeat (autodimp h hyp);[| |eapply h; eauto].

Abort.

Lemma ex_all_partial_derive_st_funcOf :
  forall f m (args : Vector.t Term m) (I : interpretation),
    (forall t I,
        Vector.In t args
        -> ex_all_partial_derive_st (fun s => dynamic_semantics_term I s t))
    -> ex_all_partial_derive_st
         (fun s =>
            interp_fun_f
              m
              (I (SymbolFunction f m))
              (Vector.map (dynamic_semantics_term I s) args)).
Proof.
  introv ih.
  remember (I (SymbolFunction f m)) as pF; simpl in pF.
  destruct pF as [F sm]; simpl.
  clear dependent f.
  introv len; subst.
  apply sm; clear sm; try (exact (KTdot 0)); auto.
  introv i ss; introv; simpl in *.
  pose proof (ih t I i (length l') (upd_state s w pt) l' w eq_refl) as q.
  unfold ex_partial_derive_st_l in q; simpl in q.
  autorewrite with core in q.
  eapply ex_derive_ext;[|exact q];clear q; simpl; introv.
  autorewrite with core; auto.
Qed.

Lemma ex_all_partial_derive_st_dynamic_semantics_term :
  forall (t : Term) (I : interpretation),
    ex_all_partial_derive_st (fun s => dynamic_semantics_term I s t).
Proof.
  term_ind t Case; introv; simpl.

  { Case "KTdot".
    apply ex_all_partial_derive_st_constant.
  }

  { Case "KTfuncOf".
    apply ex_all_partial_derive_st_funcOf; auto.
  }

  { Case "KTnumber".
    apply ex_all_partial_derive_st_constant.
  }

  { Case "KTread".
    apply ex_all_partial_derive_st_read.
  }

  { Case "KTneg".
    apply ex_all_partial_derive_st_neg;auto.
  }

  { Case "KTplus".
    apply ex_all_partial_derive_st_plus;auto.
  }

  { Case "KTminus".
    apply ex_all_partial_derive_st_minus;auto.
  }

  { Case "KTtimes".
    apply ex_all_partial_derive_st_mult;auto.
  }

  { Case "KTdivide".
    apply ex_all_partial_derive_st_constant;auto.
  }

  { Case "KTpower".
    apply ex_all_partial_derive_st_constant;auto.
  }

  { Case "KTdifferential".
    apply (ex_all_partial_derive_st_differential _ (fun s => dynamic_semantics_term I s t)); auto.
  }
Qed.
Hint Resolve ex_all_partial_derive_st_dynamic_semantics_term : core.

Lemma ex_partial_derive_st_pt_dynamic_semantics_term :
  forall (t : Term) (I : interpretation),
    ex_partial_derive_st_pt (fun s => dynamic_semantics_term I s t).
Proof.
  introv.
  apply ex_partial_derive_st_pt_eq_all; eauto 3 with core.
Qed.
Hint Resolve ex_partial_derive_st_pt_dynamic_semantics_term : core.
