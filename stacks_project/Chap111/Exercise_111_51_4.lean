/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap111.Exercise_111_51_4_Curve
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exercise 111.51.4

The scheme-theoretic closure of `y³(x⁴ + 1) = x⁴ - 1` in `ℙ¹_ℂ ×_{Spec ℂ} ℙ¹_ℂ`
is a nonsingular projective curve of genus 6, contained in the first and last
product charts, and the first-factor projection is a degree-3 cover ramified
with index 3 exactly over the eighth roots of unity in the finite chart.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveLineProduct

/-- Exercise 111.51.4 (1): the curve is contained in the union of the first and last
product charts. -/
@[stacks 02FJ]
theorem subset_firstOpen_sup_lastOpen : ι ⁻¹ᵁ (firstOpen ⊔ lastOpen) = ⊤ := sorry

/-- Exercise 111.51.4 (2): the scheme-theoretic closure is a curve over `ℂ`. -/
@[stacks 02FJ, instance]
instance instCurve : Curve schemeOver := sorry

/-- Exercise 111.51.4 (3): the curve is nonsingular over `ℂ`. -/
@[stacks 02FJ, instance]
instance instSmooth : Smooth schemeOver.hom := sorry

/-- Exercise 111.51.4 (4): the curve is projective over `ℂ`. -/
@[stacks 02FJ, instance]
instance instProjective : Projective schemeOver.hom := sorry

/-- Exercise 111.51.4 (5): the first-factor projection has degree 3. -/
@[stacks 02FJ]
theorem xProjection_degree_eq_three : xProjection.inducedFunctionFieldDegree = 3 := sorry

/-- Exercise 111.51.4 (6): the first-factor projection is ramified of index 3 exactly
over the eighth roots of unity in the finite chart, and is unramified of index 1
at every other closed point. -/
@[stacks 02FJ]
theorem ramificationIndexAt_xProjection (x : closedPoints scheme) {n : ℕ} :
    xProjection.ramificationIndexAt x.1 = n ↔
      n = 3 ∧ (∃ a : ℂ, a ^ 8 = 1 ∧
          xProjection.base x.1 = (xChartPoint a).base (IsLocalRing.closedPoint ℂ)) ∨
      n = 1 ∧ (∀ a : ℂ, a ^ 8 = 1 →
          xProjection.base x.1 ≠ (xChartPoint a).base (IsLocalRing.closedPoint ℂ)) := sorry

/-- Exercise 111.51.4 (7): the genus of the curve is 6. -/
@[stacks 02FJ]
theorem genus_eq_six : Curve.genus schemeOver = 6 := sorry

end AlgebraicGeometry.ProjectiveLineProduct
