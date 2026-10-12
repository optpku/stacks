/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Homology
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Tower
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cohomology of the Lower Derived-Truncation Tower

This leaf specializes the general lower-truncation cohomology invariance
theorem to the canonical tower `n ↦ τ≥(-n) K`. It keeps the numerical range
condition explicit, so downstream eventual-stability arguments can use it
without unfolding the tower.
-/

open CategoryTheory

universe w v u

namespace CategoryTheory.DerivedCategory.Truncation.Lower

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- Stacks 0H72: at every degree at least the stage index, the canonical map
from `K` to that lower truncation stage induces an isomorphism on cohomology. -/
@[stacks 0H72]
theorem homologyMap_isIso
    (K : DerivedCategory 𝒜) (i : ℤ) (n : ℕ) (h : index n ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor 𝒜 i).map (toStage K n)) := sorry

end CategoryTheory.DerivedCategory.Truncation.Lower
