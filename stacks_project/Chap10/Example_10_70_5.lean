/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Coordinate
import StacksCheckRecall

/-!
# Example 10.70.5

The coordinate quotient presentation is owned by the neutral
`AffineBlowupChart.Presentation.Coordinate` API.  This chapter file keeps the
source tag and recalls the canonical map, its equivalence, and the variable
evaluation formula.

@stack 0G8R
-/

@[expose] public section

open scoped AffineBlowupChart

/- Example 10.70.5 (Stacks tag `0G8R`): for a polynomial ring in `n` variables,
the quotient by `t₀ X i - tᵢ₊₁` presents the first affine blowup chart.  The
zero-based `Fin` indices formalize the source's `t₁, ..., tₙ` as `t₀, ..., tₙ₋₁`. -/
#check @AffineBlowupChart.Presentation.Coordinate.base
#check @AffineBlowupChart.Presentation.Coordinate.center
#check @AffineBlowupChart.Presentation.Coordinate.parameter
#check @AffineBlowupChart.Presentation.Coordinate.numerator
#check @AffineBlowupChart.Presentation.Coordinate.quotient
#check @AffineBlowupChart.Presentation.Coordinate.chart
#check @AffineBlowupChart.Presentation.Coordinate.map
#check @AffineBlowupChart.Presentation.Coordinate.map_surjective
#check @AffineBlowupChart.Presentation.Coordinate.map_injective
#check @AffineBlowupChart.Presentation.Coordinate.map_bijective

/- The source's coordinate quotient equivalence. -/
@[stacks 0G8R] #check @AffineBlowupChart.Presentation.Coordinate.equiv

/- The source's formula sending a quotient variable to `tᵢ₊₁ / t₀`. -/
@[stacks 0G8R] #check @AffineBlowupChart.Presentation.Coordinate.equiv_apply_variable
