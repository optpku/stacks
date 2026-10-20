/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative
public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Over

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- The zero-scheme Gysin homomorphism on cycles sends rational boundaries to zero. -/
theorem gysin_mem_ker
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
    (k : ℤ) :
    @RationalEquivalence.boundaries X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction delta) inferInstance k ≤
      ((Scheme.Modules.gysin X.hom delta ℒ s (k - 1)).comp
        (CycleGroup.reindex (X.hom.relativeDimensionFunction delta)
          (Int.sub_add_cancel k 1).symm)).ker := sorry

/-- Gysin pullback on relative Chow groups for the zero scheme of a section of an
invertible module. -/
noncomputable def gysin
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
    (k : ℤ) :
    RelativeChow delta X k →+
      RelativeChow delta (Over.mk (Scheme.zeroSchemeι ℒ s ≫ X.hom)) (k - 1) :=
  QuotientAddGroup.lift
    (@RationalEquivalence.boundaries X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction delta) inferInstance k)
    ((Scheme.Modules.gysin X.hom delta ℒ s (k - 1)).comp
      (CycleGroup.reindex (X.hom.relativeDimensionFunction delta)
        (Int.sub_add_cancel k 1).symm))
    (gysin_mem_ker delta X ℒ s k)

/-- On a Chow class, relative Gysin pullback is induced by the zero-scheme Gysin map on
the chosen cycle representative. -/
theorem gysin_chowClass
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (ℒ : X.left.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections)
    (k : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction delta) k) :
    gysin delta X ℒ s k
        (@chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction delta) inferInstance k alpha) =
      Scheme.Modules.gysin X.hom delta ℒ s (k - 1)
        (CycleGroup.reindex (X.hom.relativeDimensionFunction delta)
          (Int.sub_add_cancel k 1).symm alpha) := sorry

end AlgebraicGeometry.ChowGroup
