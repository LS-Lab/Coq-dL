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



(**

  DI for \/

  P1 -> [c & H]P2 -> [c & H]P1       Q1 -> [c & H]Q2 -> [c & H]Q1
  ---------------------------------------------------------------
         (P1 | Q1) -> [c & H](P2 & Q2) -> [c & H](P1 | Q1)

 *)

Definition DI_or_quant_rule H : Rule :=
  MkRULE
    [DI_box_seq H quantP1 quantP2,
     DI_box_seq H quantQ1 quantQ2]
    (DI_box_seq H (KFor quantP1 quantQ1) (KFand quantP2 quantQ2)).

Lemma DI_or_quant_rule_true : Rule_true (DI_or_quant_rule emHyps).
Proof.
  introv hprem; simpl in *.
  dLin_hyp prem.
  unfold DI_box_seq in *.
  unfold DI_box_sch in *.

  apply sequent_true_as_sound_proof_state.

  apply (apply_script_preserves_soundness
           [
             step_imply_right "x",
             step_imply_right "y",

             step_cut
               "imp1"
               (KFimply quantQ1
                        (KFimply (KFbox (KPodeSystem (ODEconst odec) quantH) quantQ2)
                                 (KFbox (KPodeSystem (ODEconst odec) quantH) quantQ1))),
             step_clear "x",
             step_clear "y",
             step_clear "z",
             step_focus 1,

             step_cut
               "imp2"
               (KFimply quantP1
                        (KFimply (KFbox (KPodeSystem (ODEconst odec) quantH) quantP2)
                                 (KFbox (KPodeSystem (ODEconst odec) quantH) quantP1))),
             step_clear "x",
             step_clear "y",
             step_clear "z",
             step_clear "imp1",
             step_focus 1,

             step_or_left "x",

             step_clear "imp1",
             step_imply_left "imp2",
             step_assumption "x",

             step_imply_left "imp2",
             step_K
               "w"
               [USE_constant consta (KPodeSystem (ODEconst odec) quantH),
                USE_quant qsP (KFand quantP2 quantQ2),
                USE_quant qsQ quantP2],
             step_imply_left "w",
             step_G
               "w"
               [USE_constant consta (KPodeSystem (ODEconst odec) quantH),
                USE_quant qsQ (KFimply (KFand (KFquantifier qsP2 KFtrue) (KFquantifier qsQ2 KFtrue))
                                       (KFquantifier qsP2 KFtrue))],
             step_imply_right "w",
             step_and_left "w" "z",
             step_assumption "w",
             step_assumption "w",
             step_imply_left "w",
             step_assumption "y",
             step_assumption "w",

             step_K
               "w"
               [USE_constant consta (KPodeSystem (ODEconst odec) quantH),
                USE_quant qsP quantP1,
                USE_quant qsQ (KFor quantP1 quantQ1)],
             step_imply_left "w",
             step_G
               "w"
               [USE_constant consta (KPodeSystem (ODEconst odec) quantH),
                USE_quant qsQ (KFimply (KFquantifier qsP1 KFtrue)
                                       (KFor (KFquantifier qsP1 KFtrue) (KFquantifier qsQ1 KFtrue)))],
             step_imply_right "x",
             step_or_right1,
             step_assumption "x",
             step_assumption "w",
             step_imply_left "w",
             step_assumption "imp2",
             step_assumption "w",

             step_clear "imp2",
             step_imply_left "imp1",
             step_assumption "x",

             step_imply_left "imp1",
             step_K
               "w"
               [USE_constant consta (KPodeSystem (ODEconst odec) quantH),
                USE_quant qsP (KFand quantP2 quantQ2),
                USE_quant qsQ quantQ2],
             step_imply_left "w",
             step_G
               "w"
               [USE_constant consta (KPodeSystem (ODEconst odec) quantH),
                USE_quant qsQ (KFimply (KFand (KFquantifier qsP2 KFtrue) (KFquantifier qsQ2 KFtrue))
                                       (KFquantifier qsQ2 KFtrue))],
             step_imply_right "w",
             step_and_left "w" "z",
             step_assumption "z",
             step_assumption "w",
             step_imply_left "w",
             step_assumption "y",
             step_assumption "w",

             step_K
               "w"
               [USE_constant consta (KPodeSystem (ODEconst odec) quantH),
                USE_quant qsP quantQ1,
                USE_quant qsQ (KFor quantP1 quantQ1)],
             step_imply_left "w",
             step_G
               "w"
               [USE_constant consta (KPodeSystem (ODEconst odec) quantH),
                USE_quant qsQ (KFimply (KFquantifier qsQ1 KFtrue)
                                       (KFor (KFquantifier qsP1 KFtrue) (KFquantifier qsQ1 KFtrue)))],
             step_imply_right "x",
             step_or_right2,
             step_assumption "x",
             step_assumption "w",
             step_imply_left "w",
             step_assumption "imp1",
             step_assumption "w"
           ]
        ).
  simpl.
  allrw sound_proof_state_cons; tcsp.
Qed.
