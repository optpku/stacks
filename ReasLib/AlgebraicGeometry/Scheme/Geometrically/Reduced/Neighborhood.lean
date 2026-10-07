module

public import Mathlib.AlgebraicGeometry.SpreadingOut
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- A locally Noetherian scheme over a field that is geometrically reduced at a
point has a geometrically reduced open neighborhood of that point. -/
@[stacks 0360]
theorem existsOpenNeighborhood_geometricallyReduced_of_geometricallyReducedAt
    (X : Over (Spec (CommRingCat.of k))) [IsLocallyNoetherian X.left] (x : X.left)
    (hx : geometricallyReducedAt X x) :
    ∃ U : X.left.Opens, x ∈ U ∧
      geometricallyReduced (Over.mk (U.ι ≫ X.hom)) := sorry

end AlgebraicGeometry.SchemeOverField
