/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.LinearAlgebra.Matrix.Notation
import StacksCheckRecall
public import stacks_project.Chap55.Definition_55_3_1_NumericalType
public import stacks_project.Chap55.Definition_55_3_16_MinusTwoIndex
public import ReasLib.AlgebraicGeometry.NumericalType.ForkedFour

@[expose] public section

namespace NumericalType

/- Lemma 55.5.4 (1) -/
@[stacks 0C80] #check (NumericalType.forkedFourClassification :
  (T : NumericalType) → 4 < T.n → (v : Fin 4 ↪ Fin T.n) →
    (∀ r : Fin 4,
      NumericalType.IsMinusTwoIndex T.componentGenus T.weight T.intersection (v r)) →
    T.intersection (v 0) (v 1) ≠ 0 →
    T.intersection (v 0) (v 2) ≠ 0 →
    T.intersection (v 0) (v 3) ≠ 0 →
    NumericalType.IsForkedFourConfiguration T v)

/- Lemma 55.5.4 (2) -/
@[stacks 0C80] #check (NumericalType.IsForkedFourConfiguration.leafMax_le_center :
  {T : NumericalType} → {v : Fin 4 ↪ Fin T.n} →
    NumericalType.IsForkedFourConfiguration T v →
    max (T.multiplicity (v 1))
      (max (T.multiplicity (v 2)) (T.multiplicity (v 3))) ≤
      T.multiplicity (v 0))

end NumericalType
