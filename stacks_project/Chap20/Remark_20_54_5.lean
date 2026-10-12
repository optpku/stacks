/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula.BaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Projection formulas and derived base change

The reusable compatibility square is stated for monoidal functors and a monoidal square in
`ReasLib`; this file records its source interpretation.
-/

/- Remark 20.54.5: canonical projection-formula mates commute with canonical derived base-change
mates for a commutative monoidal square. -/
@[stacks 0B6B]
#check @CategoryTheory.leftProjectionFormulaMate_baseChange_commSq

/- Companion with specified base-change components satisfying the canonical mate condition. -/
#check @CategoryTheory.leftProjectionFormulaMate_baseChange_commSq_of_isDerivedBaseChangeMap

/- Companion for the opposite tensor order. -/
#check @CategoryTheory.projectionFormulaMate_baseChange_commSq
