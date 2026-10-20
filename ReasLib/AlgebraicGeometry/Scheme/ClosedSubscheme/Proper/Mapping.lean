/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper

/-!
# Mapping proper closed subsets

This file records how proper closed subsets behave under direct images and inverse images of
scheme morphisms over a fixed base.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace ClosedSubset

/-- The image of a closed subset proper over a base is closed when the target is separated over
the base. -/
theorem image_isClosed_of_isSeparated
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
    (hcomm : f ≫ pY = pX) [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    [IsSeparated pY] (Z : TopologicalSpace.Closeds X) [IsProperOver pX Z] :
    IsClosed (f '' (Z : Set X)) := sorry

/-- The image of a closed subset proper over a base is proper over that base when the target is
separated over the base. -/
theorem IsProperOver.image_of_isSeparated
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
    (hcomm : f ≫ pY = pX) [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    [IsSeparated pY] (Z : TopologicalSpace.Closeds X) [IsProperOver pX Z] :
    IsProperOver pY
      (⟨f '' (Z : Set X), image_isClosed_of_isSeparated pX pY f hcomm Z⟩ :
        TopologicalSpace.Closeds Y) := sorry

/-- The image of a closed subset proper over a base is proper over that base under a universally
closed morphism over the base. -/
theorem IsProperOver.image_of_universallyClosed
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
    (hcomm : f ≫ pY = pX) [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    [UniversallyClosed f] (Z : TopologicalSpace.Closeds X) [IsProperOver pX Z] :
    IsProperOver pY
      (⟨f '' (Z : Set X), f.isClosedMap (Z : Set X) Z.2⟩ :
        TopologicalSpace.Closeds Y) := sorry

/-- The inverse image of a closed subset proper over a base remains proper over that base under a
proper morphism over the base. -/
theorem IsProperOver.preimage_of_isProper
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
    (hcomm : f ≫ pY = pX) [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    [IsProper f] (Z : TopologicalSpace.Closeds Y) [IsProperOver pY Z] :
    IsProperOver pX (Z.preimage f.continuous) := sorry

end ClosedSubset

end AlgebraicGeometry
