/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction

/-!
# Proper pushforward on Chow groups

This file defines pushforward of relative Chow groups along proper morphisms.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

namespace RationalEquivalence

/-- Proper pushforward sends rational boundaries to rational boundaries in the relative
dimension grading over a universally catenary base. -/
theorem map_mem_boundaries_of_proper
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (k : ℤ) :
    @boundaries X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance k ≤
      (@boundaries Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
        (Y.hom.relativeDimensionFunction δ) inferInstance k).comap
        (CycleGroup.mapHom f.left (X.hom.relativeDimensionFunction δ)
          (Y.hom.relativeDimensionFunction δ) k) := sorry

end RationalEquivalence

namespace ChowGroup

/-- Proper pushforward on degree-`k` Chow groups over a universally catenary base. -/
noncomputable def map
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (k : ℤ) :
    @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance k →+
      @ChowGroup Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
        (Y.hom.relativeDimensionFunction δ) inferInstance k :=
  QuotientAddGroup.map
    (@RationalEquivalence.boundaries X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction δ) inferInstance k)
    (@RationalEquivalence.boundaries Y.left
      (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
      (Y.hom.relativeDimensionFunction δ) inferInstance k)
    (CycleGroup.mapHom f.left (X.hom.relativeDimensionFunction δ)
      (Y.hom.relativeDimensionFunction δ) k)
    (RationalEquivalence.map_mem_boundaries_of_proper δ X Y f k)

/-- Proper pushforward on Chow groups is computed on a cycle representative by cycle
pushforward followed by passage to its Chow class. -/
theorem map_chowClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (k : ℤ)
    (α : CycleGroup X.left (X.hom.relativeDimensionFunction δ) k) :
    map δ X Y f k
        (@chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) inferInstance k α) =
      @chowClass Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
        (Y.hom.relativeDimensionFunction δ) inferInstance k
        (CycleGroup.mapHom f.left (X.hom.relativeDimensionFunction δ)
          (Y.hom.relativeDimensionFunction δ) k α) := sorry

end ChowGroup

end AlgebraicGeometry
