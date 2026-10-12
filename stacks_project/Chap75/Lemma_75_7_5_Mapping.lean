/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_7_3_ProperOver

/-!
# Mapping closed subsets proper over a base

This file records how closed subsets of algebraic spaces that are proper over a
base behave under direct images and inverse images of morphisms over that base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubset

/-- The image of a closed subset proper over a base is closed when the target is
separated over the base. -/
theorem image_isClosed_of_isSeparated {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (pX : X ⟶ B) (pY : Y ⟶ B) (f : X ⟶ Y) (hcomm : f ≫ pY = pX)
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [Separated pY]
    (T : Closeds (Points X)) [IsProperOver pX T] :
    IsClosed (Points.map f '' (T : Set (Points X))) :=
  sorry

/-- The image of a closed subset proper over a base is proper over that base when
the target is separated over the base. -/
theorem IsProperOver.image_of_isSeparated {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (pX : X ⟶ B) (pY : Y ⟶ B) (f : X ⟶ Y) (hcomm : f ≫ pY = pX)
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [Separated pY]
    (T : Closeds (Points X)) [IsProperOver pX T] :
    IsProperOver pY
      ⟨Points.map f '' (T : Set (Points X)),
        image_isClosed_of_isSeparated pX pY f hcomm T⟩ :=
  sorry

/-- The image of a closed subset under a universally closed morphism of algebraic
spaces is closed. -/
theorem isClosed_image_of_universallyClosed {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [UniversallyClosed f] (T : Closeds (Points X)) :
    IsClosed (Points.map f '' (T : Set (Points X))) :=
  sorry

/-- The image of a closed subset proper over a base is proper over that base under
a universally closed morphism over the base. -/
theorem IsProperOver.image_of_universallyClosed {S : Scheme.{u}}
    {X Y B : AlgebraicSpace S} (pX : X ⟶ B) (pY : Y ⟶ B) (f : X ⟶ Y)
    (hcomm : f ≫ pY = pX) [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    [UniversallyClosed f] (T : Closeds (Points X)) [IsProperOver pX T] :
    IsProperOver pY
      ⟨Points.map f '' (T : Set (Points X)),
        isClosed_image_of_universallyClosed f T⟩ :=
  sorry

/-- The inverse image of a closed subset proper over a base remains proper over
that base under a proper morphism over the base. -/
theorem IsProperOver.preimage_of_isProper {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (pX : X ⟶ B) (pY : Y ⟶ B) (f : X ⟶ Y) (hcomm : f ≫ pY = pX)
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [Proper f]
    (T : Closeds (Points Y)) [IsProperOver pY T] :
    IsProperOver pX (T.preimage (Points.continuous_map f)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ClosedSubset
