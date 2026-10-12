/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.PointwiseRegular
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat

/-!
# Descent of geometric regularity

Geometric regularity over a field descends pointwise along flat morphisms between locally
Noetherian schemes, and globally along flat surjective morphisms.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of k))
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- Geometric regularity at a point descends along a morphism that is flat at that point. -/
theorem geometricallyRegularAt_of_comp_of_flatAt
    (x : X) (hx : IsGeometricallyRegularAt (f ≫ g) x) (hflat : flatAt f x) :
    IsGeometricallyRegularAt g (f x) := sorry

/-- Geometric regularity descends along a flat surjective morphism. -/
theorem isGeometricallyRegular_of_comp_of_flat_of_surjective
    [Flat f] [Surjective f] (hX : IsGeometricallyRegular (f ≫ g)) :
    IsGeometricallyRegular g := sorry

end AlgebraicGeometry.Scheme.Hom
