module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder

/-!
# Vanishing of the ideal sheaf of a first-order thickening

A first-order thickening is an isomorphism exactly when its ideal sheaf vanishes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- A first-order thickening of algebraic spaces is an isomorphism if and only
if its associated ideal sheaf vanishes. -/
theorem isZero_idealSheaf_iff_isIso {S : Scheme.{u}} {Z Z' : AlgebraicSpace S}
    (i : Z ⟶ Z') [IsFirstOrderThickening i] :
    IsZero (Hom.idealSheaf i) ↔ IsIso i :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
