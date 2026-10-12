/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern

open CategoryTheory
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 42.25.2 (1): intersection by the first Chern class sends the tensor product of two
invertible modules to the sum of their intersection operations. -/
@[stacks 02SP] #check
  (AlgebraicGeometry.Scheme.Modules.firstChernClassCap_tensor :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S)
      [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
      (ℒ 𝒩 : X.Modules) [Invertible ℒ] [Invertible 𝒩]
      (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)),
      firstChernClassCap p δ ℒ k α + firstChernClassCap p δ 𝒩 k α =
        firstChernClassCap p δ (ℒ ⊗ 𝒩) k α)

/- Lemma 42.25.2 (2): intersection by the first Chern class of the structure module is zero. -/
@[stacks 02SP] #check
  (AlgebraicGeometry.Scheme.Modules.firstChernClassCap_tensorUnit :
    ∀ {S X : Scheme.{u}} (p : X ⟶ S)
      [UniversallyCatenary S] [LocallyOfFiniteType p]
      (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)
      (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)),
      firstChernClassCap p δ (𝟙_ X.Modules) k α = 0)

end AlgebraicGeometry.Scheme.Modules
