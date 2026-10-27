/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap82.Definition_82_18_1_ChernCap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernCycle.Tensor

/-!
# Tensor and unit identities for first-Chern cap on algebraic spaces

These are properties of the canonical first-Chern cap with values in the Chow
group defined by locally finite rational equivalence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.firstChernClassCap_tensor :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
      [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
      [IsDimensionFunction δ] (L N : X.Modules) [isInvertibleObject L]
      [isInvertibleObject N] (k : ℤ) (α : cycleGroup f δ (k + 1)),
      firstChernClassCap f δ L k α + firstChernClassCap f δ N k α =
        firstChernClassCap f δ (L ⊗ N) k α)

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.firstChernClassCap_tensorUnit :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
      [QuasiSeparated f] [LocallyOfFiniteType f] (δ : Points B → ℤ)
      [IsDimensionFunction δ] (k : ℤ) (α : cycleGroup f δ (k + 1)),
      firstChernClassCap f δ (𝟙_ X.Modules) k α = 0)
