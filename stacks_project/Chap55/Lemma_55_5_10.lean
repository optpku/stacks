/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

/- Local erratum for tag 0C8F, approved 2026-10-01: the right endpoint bound is
   m₄ ≤ 2m₅, correcting the printed m₃ ≤ 2m₅. No hypotheses are added.
   The uploaded source remains unchanged; evidence is in local-error-records/0C8F. -/

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.ForkedSix

/- Lemma 55.5.10: six distinct `(-2)`-indices forming the specified forked chain
in a numerical type with more than six indices have the displayed common weight,
intersection matrix, and multiplicity inequalities, with the right endpoint bound
m₄ ≤ 2m₅ as recorded in the approved local erratum. -/
@[stacks 0C8F] #check (NumericalType.forkedSixClassification :
  ∀ (T : NumericalType) (hn : 6 < T.n) (v : Fin 6 ↪ Fin T.n)
    (hminusTwo : ∀ r,
      NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r))
    (h₁₂ : T.intersection (v 0) (v 1) ≠ 0)
    (h₂₃ : T.intersection (v 1) (v 2) ≠ 0)
    (h₃₄ : T.intersection (v 2) (v 3) ≠ 0)
    (h₄₅ : T.intersection (v 3) (v 4) ≠ 0)
    (h₃₆ : T.intersection (v 2) (v 5) ≠ 0),
    NumericalType.IsForkedSixConfiguration T v)
