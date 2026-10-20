/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.OverField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Geometrically
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced

/-!
# Pointwise geometric reducedness of algebraic spaces

Geometric reducedness of étale local rings characterizes geometric reducedness
pointwise, and agrees with the corresponding property for schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {k : Type u} [Field k]

/-- An algebraic space is geometrically reduced at a point if every étale local
ring at a geometric point over it is geometrically reduced over the ground field. -/
@[mk_iff]
class GeometricallyReducedAt (X : AlgebraicSpace (Spec (of k))) (x : Points X) : Prop where
  /-- Every geometric point above the given point has geometrically reduced étale local ring. -/
  isGeometricallyReduced_etaleLocalRing :
    ∀ xbar : GeometricPoint X, xbar.liesOver x →
      Algebra.IsGeometricallyReduced k (etaleLocalRing X xbar)

/-- Geometric reducedness at a point implies geometric reducedness of every
étale local ring at a geometric point above it. -/
theorem GeometricallyReducedAt.spec {X : AlgebraicSpace (Spec (of k))} {x : Points X}
    [GeometricallyReducedAt X x] (xbar : GeometricPoint X) (hx : xbar.liesOver x) :
    Algebra.IsGeometricallyReduced k (etaleLocalRing X xbar) :=
  GeometricallyReducedAt.isGeometricallyReduced_etaleLocalRing xbar hx

/-- Geometric reducedness of all étale local rings above a point implies geometric
reducedness at that point. -/
theorem GeometricallyReducedAt.of {X : AlgebraicSpace (Spec (of k))} {x : Points X}
    (h : ∀ xbar : GeometricPoint X, xbar.liesOver x →
      Algebra.IsGeometricallyReduced k (etaleLocalRing X xbar)) :
    GeometricallyReducedAt X x :=
  ⟨h⟩

/-- The étale local ring at a geometric point is geometrically reduced when the
algebraic space is geometrically reduced at its image. -/
instance etaleLocalRing.instIsGeometricallyReduced {X : AlgebraicSpace (Spec (of k))}
    (xbar : GeometricPoint X) [GeometricallyReducedAt X xbar.image] :
    Algebra.IsGeometricallyReduced k (etaleLocalRing X xbar) :=
  GeometricallyReducedAt.spec xbar rfl

/-- Geometric reducedness over a field is equivalent to geometric reducedness at
every point of the algebraic space. -/
theorem GeometricallyReduced.iff_forall_geometricallyReducedAt
    (X : AlgebraicSpace (Spec (of k))) :
    GeometricallyReduced X ↔ ∀ x : Points X, GeometricallyReducedAt X x :=
  sorry

/-- Geometric reducedness at every point implies geometric reducedness over the field. -/
theorem GeometricallyReduced.of {X : AlgebraicSpace (Spec (of k))}
    (h : ∀ x : Points X, GeometricallyReducedAt X x) : GeometricallyReduced X :=
  (GeometricallyReduced.iff_forall_geometricallyReducedAt X).mpr h

/-- A geometrically reduced algebraic space is geometrically reduced at each point. -/
instance instGeometricallyReducedAt_of_geometricallyReduced
    {X : AlgebraicSpace (Spec (of k))} [GeometricallyReduced X] (x : Points X) :
    GeometricallyReducedAt X x :=
  (GeometricallyReduced.iff_forall_geometricallyReducedAt X).mp inferInstance x

/-- The spectrum of a field, as an algebraic space over itself, is geometrically
reduced at every point. -/
instance instGeometricallyReducedAt_ofOver_id
    (x : Points (ofOver (Over.mk (𝟙 (Spec (of k)))))) :
    GeometricallyReducedAt (ofOver (Over.mk (𝟙 (Spec (of k))))) x :=
  instGeometricallyReducedAt_of_geometricallyReduced x

/-- Pointwise geometric reducedness of a represented scheme agrees with the
scheme-theoretic property at the corresponding point. -/
theorem geometricallyReducedAt_ofOver_iff (U : Over (Spec (of k))) (u : U.left) :
    GeometricallyReducedAt (ofOver U) (ofOver.pointsEquiv U u) ↔
      SchemeOverField.geometricallyReducedAt U u :=
  sorry

/-- A represented scheme is geometrically reduced as an algebraic space if and
only if it is geometrically reduced as a scheme over the field. -/
theorem geometricallyReduced_ofOver_iff (U : Over (Spec (of k))) :
    GeometricallyReduced (ofOver U) ↔ SchemeOverField.geometricallyReduced U :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
