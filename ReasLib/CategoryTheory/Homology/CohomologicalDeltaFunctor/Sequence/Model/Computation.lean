/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Sequence
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Components of Exact-Window Model Maps

This leaf exposes the six components of the map of exact windows induced by
a morphism of cohomological delta functors.  Downstream code can use these
statements without unfolding `ComposableArrows.homMk₅`.
-/

universe vA uA vB uB

namespace CategoryTheory.CohomologicalDeltaFunctor.exactWindowMap

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]
variable {F G : CohomologicalDeltaFunctor A B} (τ : Hom F G)
variable {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ)

/-- The `Fⁿ(X₁)` component of an exact-window model map. -/
@[simp]
theorem app_zero :
    (exactWindowMap τ hS n).app 0 = (τ.app n).app S.X₁ := sorry

/-- The `Fⁿ(X₂)` component of an exact-window model map. -/
@[simp]
theorem app_one :
    (exactWindowMap τ hS n).app 1 = (τ.app n).app S.X₂ := sorry

/-- The `Fⁿ(X₃)` component of an exact-window model map. -/
@[simp]
theorem app_two :
    (exactWindowMap τ hS n).app 2 = (τ.app n).app S.X₃ := sorry

/-- The `Fⁿ⁺¹(X₁)` component of an exact-window model map. -/
@[simp]
theorem app_three :
    (exactWindowMap τ hS n).app 3 = (τ.app (n + 1)).app S.X₁ := sorry

/-- The `Fⁿ⁺¹(X₂)` component of an exact-window model map. -/
@[simp]
theorem app_four :
    (exactWindowMap τ hS n).app 4 = (τ.app (n + 1)).app S.X₂ := sorry

/-- The `Fⁿ⁺¹(X₃)` component of an exact-window model map. -/
@[simp]
theorem app_five :
    (exactWindowMap τ hS n).app 5 = (τ.app (n + 1)).app S.X₃ := sorry

end CategoryTheory.CohomologicalDeltaFunctor.exactWindowMap
