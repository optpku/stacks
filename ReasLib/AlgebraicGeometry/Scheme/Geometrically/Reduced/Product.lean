/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
    IsReduced (pullback X.hom Y.hom : Scheme) := by
  have hX := (geometricallyReduced_iff_morphismGeometricallyReduced X).mpr
    (inferInstance : GeometricallyReduced X.hom)
  haveI (z : (pullback X.hom Y.hom : Scheme)) :
      _root_.IsReduced ((pullback X.hom Y.hom : Scheme).presheaf.stalk z) := by
    haveI : Algebra.IsGeometricallyReduced k
        (X.left.presheaf.stalk (pullback.fst X.hom Y.hom z)) :=
      (geometricallyReducedAt_iff_isGeometricallyReduced X _).mp (hX _)
    exact instIsReducedStalkPullbackOfGeometricallyReducedLeft X Y z
  exact isReduced_of_isReduced_stalk _

/-- The fiber product over a field of two geometrically reduced schemes is
geometrically reduced over that field. -/
instance instGeometricallyReducedPullback
    (X Y : Over (Spec (CommRingCat.of k)))
    [GeometricallyReduced X.hom] [GeometricallyReduced Y.hom] :
    GeometricallyReduced (pullback.fst X.hom Y.hom ≫ X.hom) := by
  rw [AlgebraicGeometry.geometricallyReduced_iff,
    geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ g
  let Y' : Over (Spec (CommRingCat.of k)) :=
    Over.mk (pullback.fst Y.hom g ≫ Y.hom)
  haveI : IsReduced Y'.left :=
    pullback_of_geometrically
      (GeometricallyReduced.geometrically_isReduced (f := Y.hom)) K g
  have h : IsReduced (pullback X.hom Y'.hom : Scheme) :=
    instIsReducedPullbackOfGeometricallyReducedLeft X Y'
  rw [pullback.condition]
  exact CategoryTheory.ObjectProperty.prop_of_iso (IsReduced ·)
    ((pullbackRightPullbackFstIso Y.hom g (pullback.snd X.hom Y.hom)).symm ≪≫
      pullbackLeftPullbackSndIso X.hom Y.hom (pullback.fst Y.hom g)).symm h

/-- If a scheme over a field is geometrically reduced at a point and another
scheme over that field is reduced, every point of their fiber product above
the given point has reduced local ring. -/
theorem isReduced_stalk_pullback_of_geometricallyReducedAt_of_isReduced
    (X Y : Over (Spec (CommRingCat.of k)))
    (x : X.left) (hX : geometricallyReducedAt X x) [IsReduced Y.left] :
    ∀ z : (pullback X.hom Y.hom : Scheme), pullback.fst X.hom Y.hom z = x →
      _root_.IsReduced ((pullback X.hom Y.hom : Scheme).presheaf.stalk z) := by
  intro z hz
  haveI : Algebra.IsGeometricallyReduced k
      (X.left.presheaf.stalk (pullback.fst X.hom Y.hom z)) := by
    rw [hz]
    exact (geometricallyReducedAt_iff_isGeometricallyReduced X x).mp hX
  exact instIsReducedStalkPullbackOfGeometricallyReducedLeft X Y z

/-- The fiber product over a field of a geometrically reduced scheme and a
reduced scheme is reduced. -/
theorem isReduced_pullback_of_geometricallyReduced_of_isReduced
    (X Y : Over (Spec (CommRingCat.of k)))
    (hX : geometricallyReduced X) [IsReduced Y.left] :
    IsReduced (pullback X.hom Y.hom : Scheme) := by
  haveI : GeometricallyReduced X.hom :=
    (geometricallyReduced_iff_morphismGeometricallyReduced X).mp hX
  exact instIsReducedPullbackOfGeometricallyReducedLeft X Y

/-- The fiber product over a field of two geometrically reduced schemes is
geometrically reduced over the field. -/
theorem geometricallyReduced_pullback_of_geometricallyReduced
    (X Y : Over (Spec (CommRingCat.of k)))
    (hX : geometricallyReduced X) (hY : geometricallyReduced Y) :
    geometricallyReduced
      (Over.mk (pullback.fst X.hom Y.hom ≫ X.hom) :
        Over (Spec (CommRingCat.of k))) := by
  haveI : GeometricallyReduced X.hom :=
    (geometricallyReduced_iff_morphismGeometricallyReduced X).mp hX
  haveI : GeometricallyReduced Y.hom :=
    (geometricallyReduced_iff_morphismGeometricallyReduced Y).mp hY
  exact (geometricallyReduced_iff_morphismGeometricallyReduced _).mpr
    (instGeometricallyReducedPullback X Y)

/-- Over a perfect field, the fiber product of two reduced schemes is reduced. -/
theorem isReduced_pullback_of_isReduced_of_perfectField
    [PerfectField k]
    (X Y : Over (Spec (CommRingCat.of k))) [IsReduced X.left] [IsReduced Y.left] :
    IsReduced (pullback X.hom Y.hom : Scheme) := by
  haveI (z : (pullback X.hom Y.hom : Scheme)) :
      _root_.IsReduced ((pullback X.hom Y.hom : Scheme).presheaf.stalk z) := by
    haveI : Algebra.IsGeometricallyReduced k
        (X.left.presheaf.stalk (pullback.fst X.hom Y.hom z)) :=
      Algebra.IsGeometricallyReduced.of_perfectField
    exact instIsReducedStalkPullbackOfGeometricallyReducedLeft X Y z
  exact isReduced_of_isReduced_stalk _

end AlgebraicGeometry.SchemeOverField
