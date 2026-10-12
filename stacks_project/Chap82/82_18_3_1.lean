/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap82.«82_18_3_1_ZeroCycle»

/-!
# Equality of zero-section cycles with component sums on algebraic spaces

This file records the equality of `k`-cycles
`[Z(s)]_k = ∑ n_i [Z(s_i)]_k` on a good algebraic space, in the setting of
Situation 82.7.1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- 82.18.3.1: In Situation 82.7.1, let `Y / B` be good, let `ℒ` be an invertible
`𝒪_Y`-module, and let `s` be a regular section of `ℒ` with
`δ_{Y/B}(y) ≤ k + 1` for all `y`. Writing `[Y]_{k+1} = ∑ n_i [Y_i]` over the
irreducible components `Y_i = integralComponent η` of `δ`-dimension `k + 1`, with
`s_i = sectionsPullback (integralComponent η).ι ℒ s` and
`n_i = genericMultiplicity η`, one has the equality of `k`-cycles
`[Z(s)]_k = ∑ n_i [Z(s_i)]_k` on `Y`. -/
@[stacks 0EQM]
theorem relativeZeroCycle_eq_sum_components
    {S : Scheme.{u}} {B Y : AlgebraicSpace S} [UniversallyCatenary B]
    (p : Y ⟶ B) [QuasiSeparated p] [LocallyOfFiniteType p]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (ℒ : Y.Modules) [isInvertibleObject ℒ] (s : ℒ.sections)
    [IsRegularSection ℒ s] (k : ℤ)
    (hY : ∀ y : Points Y, p.relativeDimensionFunction δ y ≤ k + 1) :
    relativeZeroCycle p δ ℒ s k = relativeZeroCycleComponentSum p δ ℒ s k :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
