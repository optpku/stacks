/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Relative

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Rational-equivalence boundaries lie in the kernel of the reindexed first-Chern cap
map on cycles. -/
#check (AlgebraicGeometry.RationalEquivalence.firstChernClassCap_mem_ker :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (k : ℤ),
    @AlgebraicGeometry.RationalEquivalence.boundaries X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance k ≤
      ((Scheme.Modules.firstChernClassCap X.hom δ ℒ (k - 1)).comp
        (AlgebraicGeometry.CycleGroup.reindex (X.hom.relativeDimensionFunction δ)
          (sub_add_cancel k 1).symm)).ker)

/- Intersection with the first Chern class of an invertible module on relative Chow
groups. -/
#check (AlgebraicGeometry.ChowGroup.firstChernClassCap :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (k : ℤ),
    AlgebraicGeometry.RelativeChow δ X k →+
      AlgebraicGeometry.RelativeChow δ X (k - 1))

/- The Chow-level first-Chern cap map is computed on a representative by the reindexed
cycle-level first-Chern operation. -/
#check (AlgebraicGeometry.ChowGroup.firstChernClassCap_chowClass :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (k : ℤ)
    (α : AlgebraicGeometry.CycleGroup X.left (X.hom.relativeDimensionFunction δ) k),
    AlgebraicGeometry.ChowGroup.firstChernClassCap δ X ℒ k
        (@AlgebraicGeometry.chowClass X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) inferInstance k α) =
      Scheme.Modules.firstChernClassCap X.hom δ ℒ (k - 1)
        (AlgebraicGeometry.CycleGroup.reindex (X.hom.relativeDimensionFunction δ)
          (sub_add_cancel k 1).symm α))
