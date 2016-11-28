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


Require Export Omega.
Require Export terms_util.


(**

   This file contains some useful tactics we used in our proves.

 *)

Tactic Notation "prog_ind" ident(h) ident(c) :=
  induction h;
  [ Case_aux c "KPconstant"
  | Case_aux c "KPassign"
  | Case_aux c "KPassignAny"
  | Case_aux c "KPtest"
  | Case_aux c "KPchoice"
  | Case_aux c "KPcompose"
  | Case_aux c "KPloop"
  | Case_aux c "KPodeSystem"
  ].

Tactic Notation "form_ind" ident(h) ident(c) :=
  induction h;
  [ Case_aux c "KFdot"
  | Case_aux c "KFtrue"
  | Case_aux c "KFfalse"
  | Case_aux c "KFequal"
  | Case_aux c "KFnotequal"
  | Case_aux c "KFgreaterEqual"
  | Case_aux c "KFgreater"
  | Case_aux c "KFlessEqual"
  | Case_aux c "KFless"
  | Case_aux c "KFpredOf"
  | Case_aux c "KFquantifier"
  | Case_aux c "KFnot"
  | Case_aux c "KFand"
  | Case_aux c "KFor"
  | Case_aux c "KFimply"
  | Case_aux c "KFequiv"
  | Case_aux c "KFforallVars"
  | Case_aux c "KFexistsVars"
  | Case_aux c "KFbox"
  | Case_aux c "KFdiamond"
  ].

Tactic Notation "sp_term_ind" ident(h) ident(c) :=
  induction h;
  [ Case_aux c "KTdot"
(*  | Case_aux c "KTanything"*)
  | Case_aux c "KTfuncOf"
  | Case_aux c "KTnumber"
  | Case_aux c "KTread"
  | Case_aux c "KTneg"
  | Case_aux c "KTplus"
  | Case_aux c "KTminus"
  | Case_aux c "KTtimes"
  | Case_aux c "KTdifferential"
  ].

Tactic Notation "term_dest" ident(h) ident(c) :=
  destruct h;
  [ Case_aux c "KTdot"
(*  | Case_aux c "KTanything"*)
  | Case_aux c "KTfuncOf"
  | Case_aux c "KTnumber"
  | Case_aux c "KTread"
  | Case_aux c "KTneg"
  | Case_aux c "KTplus"
  | Case_aux c "KTminus"
  | Case_aux c "KTtimes"
  | Case_aux c "KTdifferential"
  ].


(** size of a term *)
Fixpoint term_size (t : Term) : nat :=
  match t with
  | KTdot _ => 1%nat
  | KTfuncOf f m args => S (Vector.fold_left (fun n t => (n + term_size t)%nat) 0%nat args)
  | KTnumber r   => 1%nat
  | KTread   x   => 1%nat
  | KTneg    l   => S (term_size l)
  | KTplus   l r => S (term_size l + term_size r)
  | KTminus  l r => S (term_size l + term_size r)
  | KTtimes  l r => S (term_size l + term_size r)
  | KTdifferential t => S (term_size t)
  end.

Lemma better_Term_ind :
  forall P : Term -> Prop,
    (forall n, P (KTdot n))
    -> (forall (f      : FunctionSymbol)
               (n      : nat)
               (args   : Vector.t Term n)
               (IHargs : forall t, Vector.In t args -> P t),
           P (KTfuncOf f n args))
    -> (forall r : KTnum, P (KTnumber r))
    -> (forall var : KAssignable, P (KTread var))
    -> (forall child : Term, P child -> P (KTneg child))
    -> (forall l r : Term, P l -> P r -> P (KTplus   l r))
    -> (forall l r : Term, P l -> P r -> P (KTminus  l r))
    -> (forall l r : Term, P l -> P r -> P (KTtimes  l r))
    -> (forall t : Term, P t -> P (KTdifferential t))
    -> forall t : Term, P t.
Proof.
 intros P hdot hfunc hnum hread hneg hplus hminus htimes hdiff.

 assert (forall n t, term_size t = n -> P t) as Hass;
   [|introv;eapply Hass; reflexivity].

 induction n as [n Hind] using comp_ind; introv s.

 term_dest t Case; simpl in *; ginv.

 { Case "KTfuncOf".

   apply hfunc; introv i.
   destruct n; ginv.
   eapply Hind;[|reflexivity].
   apply le_lt_n_Sm.
   apply vec_fold_left_greater_F; auto.
 }

 { Case "KTneg".
   destruct n; ginv.
   apply hneg.
   eapply Hind;[|eauto]; omega.
 }

 { Case "KTplus".
   destruct n; ginv.
   apply hplus.
   { eapply Hind;[|eauto]; omega. }
   { eapply Hind;[|eauto]; omega. }
 }

 { Case "KTminus".
   destruct n; ginv.
   apply hminus.
   { eapply Hind;[|eauto]; omega. }
   { eapply Hind;[|eauto]; omega. }
 }

 { Case "KTtimes".
   destruct n; ginv.
   apply htimes.
   { eapply Hind;[|eauto]; omega. }
   { eapply Hind;[|eauto]; omega. }
 }

 { Case "KTdifferential".
   destruct n; ginv.
   apply hdiff.
   eapply Hind;[|eauto]; omega.
 }
Qed.

Lemma better_Term_rec_o :
  forall P : Term -> Type,
    (forall n, P (KTdot n))
    -> (forall (f      : FunctionSymbol)
               (n      : nat)
               (args   : Vector.t Term n)
               (IHargs : forall t, Vector.In t args -> P t),
           P (KTfuncOf f n args))
    -> (forall r : KTnum, P (KTnumber r))
    -> (forall var : KAssignable, P (KTread var))
    -> (forall child : Term, P child -> P (KTneg child))
    -> (forall l r : Term, P l -> P r -> P (KTplus   l r))
    -> (forall l r : Term, P l -> P r -> P (KTminus  l r))
    -> (forall l r : Term, P l -> P r -> P (KTtimes  l r))
    -> (forall t : Term, P t -> P (KTdifferential t))
    -> forall t : Term, P t.
Proof.
 intros P hdot hfunc hnum hread hneg hplus hminus htimes hdiff.

 assert (forall n t, term_size t = n -> P t) as Hass;
   [|introv;eapply Hass; reflexivity].

 induction n as [n Hind] using comp_ind_type; introv s.

 term_dest t Case; simpl in *; ginv.

 { Case "KTfuncOf".

   apply hfunc; introv i.
   destruct n; ginv.
   eapply Hind;[|reflexivity].
   apply le_lt_n_Sm.
   apply vec_fold_left_greater_F; auto.
 }

 { Case "KTneg".
   destruct n; ginv.
   apply hneg.
   eapply Hind;[|eauto]; omega.
 }

 { Case "KTplus".
   destruct n; ginv.
   apply hplus.
   { eapply Hind;[|eauto]; omega. }
   { eapply Hind;[|eauto]; omega. }
 }

 { Case "KTminus".
   destruct n; ginv.
   apply hminus.
   { eapply Hind;[|eauto]; omega. }
   { eapply Hind;[|eauto]; omega. }
 }

 { Case "KTtimes".
   destruct n; ginv.
   apply htimes.
   { eapply Hind;[|eauto]; omega. }
   { eapply Hind;[|eauto]; omega. }
 }

 { Case "KTdifferential".
   destruct n; ginv.
   apply hdiff.
   eapply Hind;[|eauto]; omega.
 }
Defined.

Lemma le_n_S2 : forall n m : nat, n <= m -> S n <= S m.
Proof.
  induction 1; constructor; trivial.
Defined.

Lemma le_lt_n_Sm2 : forall n m : nat, n <= m -> n < S m.
Proof.
  introv h; apply le_n_S2; auto.
Defined.

Lemma ge0 :
  forall a : nat, 0 <= a.
Proof.
  induction a; simpl; introv; auto.
Defined.

Lemma ge_plus_weak_left :
  forall a c : nat, a <= a + c.
Proof.
  induction a; simpl; introv; auto.
  { apply ge0. }
  { apply le_n_S2; auto. }
Defined.

Lemma ge_plus_weak_right :
  forall a c : nat, a <= c + a.
Proof.
  induction c; simpl; introv; auto.
Defined.

Lemma implies_ge_plus_weak :
  forall a b c : nat, a <= b -> a <= b + c.
Proof.
  induction 1; auto.
  { apply ge_plus_weak_left. }
  { simpl; constructor; auto. }
Defined.

Lemma vec_fold_left_greater2 :
  forall {T : Type} {n} (v : Vector.t T n) (F : T -> nat) a b,
    (a <= b)%nat
    -> (a <= Vector.fold_left (fun n u => n + F u) b v)%nat.
Proof.
  induction v; introv lab; simpl in *; auto.
  apply IHv.
  apply implies_ge_plus_weak; auto.
Defined.

Lemma vec_fold_left_greater_F2 :
  forall {T : Type} t {n} (v : Vector.t T n) (F : T -> nat) m,
    Vector.In t v
    -> (F t <= Vector.fold_left (fun n u => n + F u) m v)%nat.
Proof.
  induction v; simpl; introv i.

  { inversion i. }

  { inversion i as [|? ? ? j]; subst; clear i; eqDepDec; subst; simpl in *; auto.
    apply vec_fold_left_greater2; apply ge_plus_weak_right. }
Defined.

Lemma le_S_implies_or :
  forall n m, n <= S m -> n = S m \/ n <= m.
Proof.
  induction n; introv h.
  { right; apply ge0. }
  { inversion h; subst; auto. }
Defined.

Lemma not_lt0 : forall n, n < 0 -> False.
Proof.
  introv h; inversion h.
Defined.

Lemma comp_ind_type2 :
  forall P: nat -> Type,
    (forall n: nat, (forall m: nat, m < n -> P m) -> P n)
    -> forall n:nat, P n.
Proof.
 introv imp; introv.
 assert (forall n m, m < n -> P m) as q;[|eapply q; eauto].
 intro k; induction k as [| n']; introv h; auto.
 { apply not_lt0 in h; tcsp. }
 { destruct (deq_nat m n'); subst; auto.
   apply IHn'.
   unfold lt in *.
   apply le_S_implies_or in h; destruct h as [h|h]; auto.
   destruct n0; auto. }
Defined.

Lemma better_Term_rec :
  forall P : Term -> Type,
    (forall n, P (KTdot n))
    -> (forall (f      : FunctionSymbol)
               (n      : nat)
               (args   : Vector.t Term n)
               (IHargs : forall t, Vector.In t args -> P t),
           P (KTfuncOf f n args))
    -> (forall r : KTnum, P (KTnumber r))
    -> (forall var : KAssignable, P (KTread var))
    -> (forall child : Term, P child -> P (KTneg child))
    -> (forall l r : Term, P l -> P r -> P (KTplus   l r))
    -> (forall l r : Term, P l -> P r -> P (KTminus  l r))
    -> (forall l r : Term, P l -> P r -> P (KTtimes  l r))
    -> (forall t : Term, P t -> P (KTdifferential t))
    -> forall t : Term, P t.
Proof.
 intros P hdot hfunc hnum hread hneg hplus hminus htimes hdiff.

 assert (forall n t, term_size t = n -> P t) as Hass;
   [|introv;eapply Hass; reflexivity].

 induction n as [n Hind] using comp_ind_type2; introv s.

 term_dest t Case; simpl in *; ginv.

 { Case "KTfuncOf".

   apply hfunc; introv i.
   destruct n; ginv.
   apply (Hind (term_size t));[|reflexivity].
   apply le_lt_n_Sm2.
   apply vec_fold_left_greater_F2; auto.
 }

 { Case "KTneg".
   destruct n; ginv.
   apply hneg.
   apply (Hind (term_size t)); auto.
 }

 { Case "KTplus".
   destruct n; ginv.
   apply hplus.
   { apply (Hind (term_size t1)); auto; apply le_n_S2; apply ge_plus_weak_left. }
   { apply (Hind (term_size t2)); auto; apply le_n_S2; apply ge_plus_weak_right. }
 }

 { Case "KTminus".
   destruct n; ginv.
   apply hminus.
   { apply (Hind (term_size t1)); auto; apply le_n_S2; apply ge_plus_weak_left. }
   { apply (Hind (term_size t2)); auto; apply le_n_S2; apply ge_plus_weak_right. }
 }

 { Case "KTtimes".
   destruct n; ginv.
   apply htimes.
   { apply (Hind (term_size t1)); auto; apply le_n_S2; apply ge_plus_weak_left. }
   { apply (Hind (term_size t2)); auto; apply le_n_S2; apply ge_plus_weak_right. }
 }

 { Case "KTdifferential".
   destruct n; ginv.
   apply hdiff.
   apply (Hind (term_size t)); auto.
 }
Defined.

Tactic Notation "term_ind" ident(h) ident(c) :=
  induction h using better_Term_ind;
  [ Case_aux c "KTdot"
(*  | Case_aux c "KTanything"*)
  | Case_aux c "KTfuncOf"
  | Case_aux c "KTnumber"
  | Case_aux c "KTread"
  | Case_aux c "KTneg"
  | Case_aux c "KTplus"
  | Case_aux c "KTminus"
  | Case_aux c "KTtimes"
  | Case_aux c "KTdifferential"
  ].

Tactic Notation "term_rec" ident(h) ident(c) :=
  induction h using better_Term_rec;
  [ Case_aux c "KTdot"
(*  | Case_aux c "KTanything"*)
  | Case_aux c "KTfuncOf"
  | Case_aux c "KTnumber"
  | Case_aux c "KTread"
  | Case_aux c "KTneg"
  | Case_aux c "KTplus"
  | Case_aux c "KTminus"
  | Case_aux c "KTtimes"
  | Case_aux c "KTdifferential"
  ].


(*
 Is there a way to generate that automatically?
 [Combined Scheme] only seems to work for Prop...
 *)
Lemma Formula_Program_rec_2 :
  forall (P : Formula -> Type)
         (P0 : Program -> Type),
    P KFdot ->
    P KFtrue ->
    P KFfalse ->
    (forall left right : Term, P (KFequal left right)) ->
    (forall left right : Term, P (KFnotequal left right)) ->
    (forall left right : Term, P (KFgreaterEqual left right)) ->
    (forall left right : Term, P (KFgreater left right)) ->
    (forall left right : Term, P (KFlessEqual left right)) ->
    (forall left right : Term, P (KFless left right)) ->
    (forall (f : PredicateSymbol) n (args : Vector.t Term n), P (KFpredOf f n args)) ->
    (forall (f : QuantifierSymbol) (a : Formula), P a -> P (KFquantifier f a)) ->
    (forall child : Formula, P child -> P (KFnot child)) ->
    (forall left : Formula,
        P left -> forall right : Formula, P right -> P (KFand left right)) ->
    (forall left : Formula,
        P left -> forall right : Formula, P right -> P (KFor left right)) ->
    (forall left : Formula,
        P left -> forall right : Formula, P right -> P (KFimply left right)) ->
    (forall left : Formula,
        P left -> forall right : Formula, P right -> P (KFequiv left right)) ->
    (forall (vars : list KVariable) (child : Formula),
        P child -> P (KFforallVars vars child)) ->
    (forall (vars : list KVariable) (child : Formula),
        P child -> P (KFexistsVars vars child)) ->
    (forall prog : Program,
        P0 prog -> forall child : Formula, P child -> P (KFbox prog child)) ->
    (forall prog : Program,
        P0 prog -> forall child : Formula, P child -> P (KFdiamond prog child)) ->
    (forall name : ProgramConstName, P0 (KPconstant name)) ->
    (forall (x : KAssignable) (e : Term), P0 (KPassign x e)) ->
    (forall x : KAssignable, P0 (KPassignAny x)) ->
    (forall cond : Formula, P cond -> P0 (KPtest cond)) ->
    (forall left : Program,
        P0 left -> forall right : Program, P0 right -> P0 (KPchoice left right)) ->
    (forall left : Program,
        P0 left -> forall right : Program, P0 right -> P0 (KPcompose left right)) ->
    (forall child : Program, P0 child -> P0 (KPloop child)) ->
    (forall (ode : ODE) (constraint : Formula),
        P constraint -> P0 (KPodeSystem ode constraint)) ->
    (forall f : Formula, P f) * (forall f : Program, P0 f).
Proof.
  intros.
  dands; introv.
  { apply (Formula_rec_2 P P0); auto. }
  { apply (Program_rec_2 P P0); auto. }
Defined.

Tactic Notation "form_prog_ind" ident(c) :=
  apply Formula_Program_multind;
  [ Case_aux c "KFdot"
  | Case_aux c "KFtrue"
  | Case_aux c "KFfalse"
  | Case_aux c "KFequal"
  | Case_aux c "KFnotequal"
  | Case_aux c "KFgreaterEqual"
  | Case_aux c "KFgreater"
  | Case_aux c "KFlessEqual"
  | Case_aux c "KFless"
  | Case_aux c "KFpredOf"
  | Case_aux c "KFquantifier"
  | Case_aux c "KFnot"
  | Case_aux c "KFand"
  | Case_aux c "KFor"
  | Case_aux c "KFimply"
  | Case_aux c "KFequiv"
  | Case_aux c "KFforallVars"
  | Case_aux c "KFexistsVars"
  | Case_aux c "KFbox"
  | Case_aux c "KFdiamond"

  | Case_aux c "KPconstant"
  | Case_aux c "KPassign"
  | Case_aux c "KPassignAny"
  | Case_aux c "KPtest"
  | Case_aux c "KPchoice"
  | Case_aux c "KPcompose"
  | Case_aux c "KPloop"
  | Case_aux c "KPodeSystem"
  ].

Tactic Notation "form_prog_rec" ident(c) :=
  apply Formula_Program_rec_2;
  [ Case_aux c "KFdot"
  | Case_aux c "KFtrue"
  | Case_aux c "KFfalse"
  | Case_aux c "KFequal"
  | Case_aux c "KFnotequal"
  | Case_aux c "KFgreaterEqual"
  | Case_aux c "KFgreater"
  | Case_aux c "KFlessEqual"
  | Case_aux c "KFless"
  | Case_aux c "KFpredOf"
  | Case_aux c "KFquantifier"
  | Case_aux c "KFnot"
  | Case_aux c "KFand"
  | Case_aux c "KFor"
  | Case_aux c "KFimply"
  | Case_aux c "KFequiv"
  | Case_aux c "KFforallVars"
  | Case_aux c "KFexistsVars"
  | Case_aux c "KFbox"
  | Case_aux c "KFdiamond"

  | Case_aux c "KPconstant"
  | Case_aux c "KPassign"
  | Case_aux c "KPassignAny"
  | Case_aux c "KPtest"
  | Case_aux c "KPchoice"
  | Case_aux c "KPcompose"
  | Case_aux c "KPloop"
  | Case_aux c "KPodeSystem"
  ].
