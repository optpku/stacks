/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernCycle.Tensor
import StacksCheckRecall

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

/- Lemma 82.18.2 (1): In Situation 82.2.1, for good `X / B` and invertible
`𝒪_X`-modules `L`, `N`, first-Chern cap is additive in the sheaf:
`firstChernClassCap f δ L k α + firstChernClassCap f δ N k α =
firstChernClassCap f δ (L ⊗ N) k α` in `chowGroup f δ k` for every
`α : cycleGroup f δ (k + 1)`. The degree follows the preceding definition
`Z_(k + 1) → CH_k`, resolving the printed lemma’s `k - 1` typo. -/
@[stacks 0EQK]
#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.firstChernClassCap_tensor :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
      [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
      [IsDimensionFunction δ] (L N : X.Modules) [isInvertibleObject L]
      [isInvertibleObject N] (k : ℤ) (α : cycleGroup f δ (k + 1)),
      firstChernClassCap f δ L k α + firstChernClassCap f δ N k α =
        firstChernClassCap f δ (L ⊗ N) k α)

/- Lemma 82.18.2 (2): In Situation 82.2.1, for good `X / B`, first-Chern cap
against the structure sheaf vanishes:
`firstChernClassCap f δ (𝟙_ X.Modules) k α = 0` in `chowGroup f δ k` for every
`α : cycleGroup f δ (k + 1)`. -/
@[stacks 0EQK]
#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.firstChernClassCap_tensorUnit :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
      [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
      [IsDimensionFunction δ] (k : ℤ) (α : cycleGroup f δ (k + 1)),
      firstChernClassCap f δ (𝟙_ X.Modules) k α = 0)
