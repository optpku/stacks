module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
public import ReasLib.RingTheory.Algebra.TensorProduct.Reduced

/-!
# Products of geometrically reduced schemes

This file establishes reducedness and geometric reducedness properties of
fiber products of schemes over a field.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- A point of a fiber product has reduced local ring when the corresponding
local ring of the left factor is geometrically reduced and the right factor is reduced. -/
instance instIsReducedStalkPullbackOfGeometricallyReducedLeft
    (X Y : Over (Spec (CommRingCat.of k)))
    (z : (pullback X.hom Y.hom : Scheme))
    [Algebra.IsGeometricallyReduced k
      (X.left.presheaf.stalk (pullback.fst X.hom Y.hom z))]
    [IsReduced Y.left] :
    _root_.IsReduced ((pullback X.hom Y.hom : Scheme).presheaf.stalk z) := sorry

/-- The fiber product of a geometrically reduced scheme over a field with a
reduced scheme is reduced. -/
instance instIsReducedPullbackOfGeometricallyReducedLeft
    (X Y : Over (Spec (CommRingCat.of k)))
    [GeometricallyReduced X.hom] [IsReduced Y.left] :
    IsReduced (pullback X.hom Y.hom : Scheme) := sorry

/-- The fiber product over a field of two geometrically reduced schemes is
geometrically reduced over that field. -/
instance instGeometricallyReducedPullback
    (X Y : Over (Spec (CommRingCat.of k)))
    [GeometricallyReduced X.hom] [GeometricallyReduced Y.hom] :
    GeometricallyReduced (pullback.fst X.hom Y.hom ≫ X.hom) := sorry

/-- If a scheme over a field is geometrically reduced at a point and another
scheme over that field is reduced, every point of their fiber product above
the given point has reduced local ring. -/
theorem isReduced_stalk_pullback_of_geometricallyReducedAt_of_isReduced
    (X Y : Over (Spec (CommRingCat.of k)))
    (x : X.left) (hX : geometricallyReducedAt X x) [IsReduced Y.left] :
    ∀ z : (pullback X.hom Y.hom : Scheme), pullback.fst X.hom Y.hom z = x →
      _root_.IsReduced ((pullback X.hom Y.hom : Scheme).presheaf.stalk z) := sorry

/-- The fiber product over a field of a geometrically reduced scheme and a
reduced scheme is reduced. -/
theorem isReduced_pullback_of_geometricallyReduced_of_isReduced
    (X Y : Over (Spec (CommRingCat.of k)))
    (hX : geometricallyReduced X) [IsReduced Y.left] :
    IsReduced (pullback X.hom Y.hom : Scheme) := sorry

/-- The fiber product over a field of two geometrically reduced schemes is
geometrically reduced over the field. -/
theorem geometricallyReduced_pullback_of_geometricallyReduced
    (X Y : Over (Spec (CommRingCat.of k)))
    (hX : geometricallyReduced X) (hY : geometricallyReduced Y) :
    geometricallyReduced
      (Over.mk (pullback.fst X.hom Y.hom ≫ X.hom) :
        Over (Spec (CommRingCat.of k))) := sorry

/-- Over a perfect field, the fiber product of two reduced schemes is reduced. -/
theorem isReduced_pullback_of_isReduced_of_perfectField
    [PerfectField k]
    (X Y : Over (Spec (CommRingCat.of k))) [IsReduced X.left] [IsReduced Y.left] :
    IsReduced (pullback X.hom Y.hom : Scheme) := sorry

end AlgebraicGeometry.SchemeOverField
