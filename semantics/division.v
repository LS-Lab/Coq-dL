(*

  Copyright 2016 University of Luxembourg

  This file is part of our formalization of Platzer's
    "A Complete Uniform Substitution Calculus for Differential Dynamic Logic"
  available here: http://arxiv.org/pdf/1601.06183.pdf.
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

Require Export deriv_util.
Require Export multiplication.


(**

  This file introduces lemma which checks if nth derivative of division of two functions exists.

 *)

(* Regarding division:
https://www.physicsforums.com/threads/quotient-rule-for-higher-order-derivatives.289320/
 *)

(** does derivative of two functions exists *)
Lemma ex_derive_n_div :
  forall (n : nat) (f g : R -> R) (pt : R),
    (forall pt, g pt <> 0)
    -> (forall pt k, (k <= n)%nat -> ex_derive_n f k pt)
    -> (forall pt k, (k <= n)%nat -> ex_derive_n g k pt)
    -> ex_derive_n (fun x => (f x) / (g x)) n pt.
Proof.
  induction n as [n IHn] using comp_ind; introv d loc1 loc2; destruct n;[simpl;auto|].
  simpl.

  apply ex_derive_n_S_if; auto.

  {
    apply ex_derive_div; auto.
    { pose proof (loc1 pt 1%nat) as q1; simpl in q1; apply q1; try omega. }
    { pose proof (loc2 pt 1%nat) as q2; simpl in q2; apply q2; try omega. }
  }

  {
    apply (@ex_derive_n_ext (fun x => (Derive f x * g x - f x * Derive g x) / g x ^ 2) _).

    { introv.
      rewrite (Derive_div f g); auto; simpl.
      { pose proof (loc1 t 1%nat) as q1; simpl in q1; apply q1; try omega. }
      { pose proof (loc2 t 1%nat) as q2; simpl in q2; apply q2; try omega. }
    }

    {
      pose proof (IHn n) as h; clear IHn.
      repeat (autodimp h hyp).
      pose proof (h (fun x => (Derive f x * g x - f x * Derive g x))
                    (fun x => g x ^ 2)
                    pt) as q; clear h.
      repeat (autodimp q hyp).

      {
        introv.
        apply pow_nonzero; auto.
      }

      {
        introv w.
        apply ex_derive_n_minus.

        {
          exists R1pos; introv w1 w2.
          apply ex_derive_n_mult_gen; introv w3.

          {
            pose proof (loc1 y0 (S k1)) as q.
            autodimp q hyp; try omega.
            apply ex_derive_n_S_implies; auto.
            pose proof (loc1 y0 1%nat) as z; apply z; try omega.
          }

          {
            pose proof (loc2 y0 k1) as q.
            autodimp q hyp; try omega.
          }
        }

        {
          exists R1pos; introv w1 w2.
          apply ex_derive_n_mult_gen; introv w3.

          {
            pose proof (loc1 y0 k1) as q.
            autodimp q hyp; try omega.
          }

          {
            pose proof (loc2 y0 (S k1)) as q.
            autodimp q hyp; try omega; auto.
            apply ex_derive_n_S_implies; auto.
            pose proof (loc2 y0 1%nat) as z; apply z; try omega.
          }
        }
      }

      {
        introv w.
        apply ex_derive_n_pow.
        introv w1.
        apply loc2; try omega.
      }
    }
  }
Qed.
