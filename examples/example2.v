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


Require Export checker.


(*
  This is similar to example 1, but assumes A>0 instead A≥0
*)

(* v≥0∧A>0 → [{x'=v,v'=A}&true}] v≥0 *)

Definition Example2 : Formula :=
  KFimply
    (KFand
       (KFgreaterEqual termv term0)
       (KFgreater termA term0)
    )
    (KFbox
       (KPodeSystem
          (ODEprod
             (ODEsing varx termv)
             (ODEsing varv termA))
          KFtrue
       )
       (KFgreaterEqual termv term0)
    ).

Lemma Example2_sequent_true : sequent_true (MkSeq emHyps Example2).
Proof.
  unfold Example2.
  apply sequent_true_as_sound_proof_state.

  apply (apply_script_preserves_soundness
           [
             step_imply_right "x",
             step_and_left "x" "y",
             step_OC
               "z"
               [USE_quant qsP KFtrue,
                USE_quant qsQ (KFgreaterEqual termv term0),
                USE_ode odec (ODEsing varx termv),
                USE_ode oded (ODEsing varv termA)]
               [],
             step_equiv_left "z" "w",
             step_clear "z",
             step_imply_left "w",
             step_focus 1,
             step_assumption "w",
             step_DIge
               "z"
               [USE_function funcg 1 (KTdot 0),
                USE_function funch 1 term0,
                USE_function funcf 1 termA,
                USE_pred predp 1 KFtrue,
                USE_ode odec (ODEsing varv tvarx)]
               [MkSwapping varv varx],
             step_imply_left "z",
             step_imply_right "w",
             step_assumption "x",
             step_imply_left "z",
             step_focus 1,
             step_assumption "z",
             step_DEsch
               "z"
               varv
               termA
               (ODEsing varx varv)
               KFtrue
               (KFgreaterEqual (KTdifferential varv) (KTdifferential term0)),
             step_equiv_left "z" "w",
             step_clear "z",
             step_imply_left "w",
             step_focus 1,
             step_assumption "w",
             step_K
               "z"
               [USE_constant consta (KPodeSystem (ODEprod (ODEsing varv termA) (ODEsing varx varv)) KFtrue),
                USE_quant qsP (KFgreaterEqual termA term0),
                USE_quant qsQ (KFbox (KPassign (KD varv) termA) (KFgreaterEqual (KTdifferential varv) (KTdifferential term0)))],
             step_imply_left "z",
             step_focus 1,
             step_imply_left "z",
             step_V
               "z"
               [
                 USE_constant consta (KPodeSystem (ODEprod (ODEsing varv termA) (ODEsing varx varv)) KFtrue),
                 USE_pred predp 0 (KFgreaterEqual termA term0)
               ],
             step_imply_left "z",
             step_GE2GT,
             step_assumption "y",
             step_assumption "z",
             step_assumption "z",
             step_GE2GT,
             step_assumption "y",
             step_clear "x",
             step_clear "y",
             step_G
               "x"
               [USE_constant consta (KPodeSystem (ODEprod (ODEsing varv termA) (ODEsing varx varv)) KFtrue),
                USE_quant qsQ (KFimply (KFgreaterEqual termA term0)
                                       (KFbox (KPassign (KD varv) termA)
                                              (KFgreaterEqual (KTdifferential varv) (KTdifferential term0))))],
             step_focus 1,
             step_assumption "x",
             step_imply_right "x",
             step_K
               "z"
               [USE_constant consta (KPassign (KD varv) termA),
                USE_quant qsP (KFgreaterEqual termA term0),
                USE_quant qsQ (KFgreaterEqual (KTdifferential varv) (KTdifferential term0))],
             step_imply_left "z",
             step_focus 1,
             step_imply_left "z",
             step_V
               "z"
               [
                 USE_constant consta (KPassign (KD varv) termA),
                 USE_pred predp 0 (KFgreaterEqual termA term0)
               ],
             step_imply_left "z",
             step_assumption "x",
             step_assumption "z",
             step_assumption "z",
             step_CE
               "z"
               (KFimply (KFgreaterEqual termA term0) (KFgreaterEqual (KTdifferential varv) (KTdifferential 0)))
               (KFimply (KFgreaterEqual termA term0) (KFgreaterEqual (KD varv) 0))
               (KFbox (KPassign (KD varv) termA) KFdot),
             step_equiv_right,
             step_imply_right "x",
             step_imply_right "y",
             step_imply_left "x",
             step_assumption "y",
             step_clear "y",
             step_PXP
               "z"
               [USE_pred predp 1 (KFgreaterEqual (KTdot 0) 0)]
               [MkSwapping varv varx],
             step_equiv_left "z" "w",
             step_clear "w",
             step_imply_left "z",
             step_focus 1,
             step_assumption "z",
             step_DRN
               "z"
               [USE_pred predp 1 (KFgreaterEqual (KTdifferential varv) (KTdot 0))]
               []
               0,
             step_equiv_left "z" "w",
             step_clear "w",
             step_imply_left "z",
             step_assumption "x",
             step_assumption "x",
             step_assumption "z",
             step_imply_right "x",
             step_imply_right "y",
             step_imply_left "x",
             step_assumption "y",
             step_clear "y",
             step_PXP
               "z"
               [USE_pred predp 1 (KFgreaterEqual (KTdot 0) (KTdifferential 0))]
               [MkSwapping varv varx],
             step_equiv_left "z" "w",
             step_clear "z",
             step_imply_left "w",
             step_focus 1,
             step_assumption "w",
             step_DRN
               "z"
               [USE_pred predp 1 (KFgreaterEqual (KD varv) (KTdot 0))]
               []
               0,
             step_equiv_left "z" "w",
             step_clear "z",
             step_imply_left "w",
             step_assumption "x",
             step_assumption "w",
             step_equiv_left "z" "w",
             step_clear "z",
             step_imply_left "w",
             step_focus 1,
             step_assumption "w",
             step_assignp
               "z"
               [
                 USE_function funcf 0 termA,
                 USE_pred predp 1 (KFimply
                                     (KFgreaterEqual (KTfuncOf funcA 0 (Vector.nil Term))
                                                     (KTnumber (KTNnat 0)))
                                     (KFgreaterEqual (KTdot 0) (KTnumber (KTNnat 0))))
               ]
               [MkSwapping varv varx],
             step_equiv_left "z" "w",
             step_clear "z",
             step_imply_left "w",
             step_focus 1,
             step_assumption "w",
             step_imply_right "w",
             step_assumption "w"
         ]
        ).
  simpl.
  eauto with core.
Qed.
