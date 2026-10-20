/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper

/-!
# Mapping closed subsets proper over a base

Closed subsets of algebraic spaces that are proper over a base remain proper
under images into separated targets, universally closed images, and proper
inverse images over that base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubset

/-- The image of a closed subset proper over a base is closed when the target is
separated over the base. -/
theorem image_isClosed_of_isSeparated {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (pX : X ⟶ B) (pY : Y ⟶ B) (f : X ⟶ Y) (hcomm : f ≫ pY = pX)
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [Separated pY]
    (T : Closeds (Points X)) (hT : ProperOver pX T) :
    IsClosed (Points.map f '' (T : Set (Points X))) :=
  sorry

/-- The image of a closed subset proper over a base is proper over that base when
the target is separated over the base. -/
theorem ProperOver.image_of_isSeparated {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (pX : X ⟶ B) (pY : Y ⟶ B) (f : X ⟶ Y) (hcomm : f ≫ pY = pX)
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [Separated pY]
    (T : Closeds (Points X)) (hT : ProperOver pX T) :
    ProperOver pY
      ⟨Points.map f '' (T : Set (Points X)),
        image_isClosed_of_isSeparated pX pY f hcomm T hT⟩ :=
  sorry

/-- The image of a closed subset proper over a base is proper over that base under
a universally closed morphism over the base. -/
theorem ProperOver.image_of_universallyClosed {S : Scheme.{u}}
    {X Y B : AlgebraicSpace S} (pX : X ⟶ B) (pY : Y ⟶ B) (f : X ⟶ Y)
    (hcomm : f ≫ pY = pX) [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    [UniversallyClosed f] (T : Closeds (Points X)) (hT : ProperOver pX T) :
    ProperOver pY
      ⟨Points.map f '' (T : Set (Points X)),
        Closed.isClosedMap (f := f) (T : Set (Points X)) T.isClosed⟩ :=
  sorry

/-- The inverse image of a closed subset proper over a base remains proper over
that base under a proper morphism over the base. -/
theorem ProperOver.preimage_of_isProper {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (pX : X ⟶ B) (pY : Y ⟶ B) (f : X ⟶ Y) (hcomm : f ≫ pY = pX)
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [Proper f]
    (T : Closeds (Points Y)) (hT : ProperOver pY T) :
    ProperOver pX (T.preimage (Points.continuous_map f)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ClosedSubset
