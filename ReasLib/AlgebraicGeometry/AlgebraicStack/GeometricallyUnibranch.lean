/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyUnibranch
public import ReasLib.AlgebraicGeometry.AlgebraicStack.GeometricBranch

/-!
# Geometric unibranchness of algebraic stacks at a point

An algebraic stack is geometrically unibranch at a point when it has exactly
one geometric branch there.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack `X` is geometrically unibranch at a point `x` if the
number of geometric branches of `X` at `x` is `1`. -/
@[mk_iff]
class GeometricallyUnibranchAt {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) : Prop where
  /-- The number of geometric branches of `X` at `x` is one. -/
  eq_one : geometricBranchNumberAt X x = 1

namespace GeometricallyUnibranchAt

/-- Geometric unibranchness at `x` implies that the geometric branch number is
`1`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} [GeometricallyUnibranchAt X x] :
    geometricBranchNumberAt X x = 1 :=
  sorry

/-- The condition that the geometric branch number at `x` is `1` witnesses
geometric unibranchness at `x`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (h : geometricBranchNumberAt X x = 1) :
    GeometricallyUnibranchAt X x :=
  sorry

/-- Geometric unibranchness at `x` is equivalent to some smooth scheme chart
through `x` having stalkwise geometric branch number one at the source point. -/
theorem iff_hasGeometricBranchNumberAt {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} :
    GeometricallyUnibranchAt X x ↔ hasGeometricBranchNumberAt 1 X x :=
  sorry

/-- Geometric unibranchness at `x` is equivalent to every smooth scheme chart
through `x` having geometric branch number `1` at the source point. -/
theorem iff_forallSmoothAt {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} :
    GeometricallyUnibranchAt X x ↔
      forallSmoothAt (GermProperty.geometricBranchEq 1) X x :=
  sorry

/-- Geometric unibranchness at `x` is equivalent to every smooth scheme chart
through `x` being geometrically unibranch at the selected source point. -/
theorem iff_isGeometricallyUnibranchAt {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} :
    GeometricallyUnibranchAt X x ↔
      ∀ (U : Over S) (p : GroupoidsOver.slice U ⟶ X) (u : U.left),
        Groupoids.Hom.Smooth p → Points.mapSlice p u = x →
          U.left.isGeometricallyUnibranchAt u :=
  sorry

end GeometricallyUnibranchAt

/-- The canonical slice of a scheme over `S` is geometrically unibranch at a
point whenever the corresponding scheme stalk is geometrically unibranch. -/
instance instGeometricallyUnibranchAt_slice {S : Scheme.{u}} {U : Over S}
    {u : U.left} [h : _root_.IsGeometricallyUnibranch (U.left.presheaf.stalk u)] :
    GeometricallyUnibranchAt (GroupoidsOver.slice U) (Points.ofSlice u) :=
  sorry

/-- On a scheme over `S`, viewed as an algebraic stack, geometric unibranchness
at a point is the usual geometric unibranchness of the scheme at that point. -/
theorem geometricallyUnibranchAt_slice_iff {S : Scheme.{u}} (U : Over S)
    (u : U.left) :
    GeometricallyUnibranchAt (GroupoidsOver.slice U) (Points.ofSlice u) ↔
      U.left.isGeometricallyUnibranchAt u :=
  sorry

/-- An algebraic space, viewed as an algebraic stack, is geometrically unibranch
at a point whenever the algebraic space is geometrically unibranch there. -/
instance instGeometricallyUnibranchAt_toGroupoids {S : Scheme.{u}}
    {F : AlgebraicSpace S} {x : AlgebraicSpace.Points F}
    [AlgebraicSpace.GeometricallyUnibranchAt F x] :
    GeometricallyUnibranchAt F.toGroupoids (Points.ofAlgebraicSpace x) :=
  sorry

/-- On an algebraic space over `S`, viewed as an algebraic stack, geometric
unibranchness at a point is the algebraic-space geometric unibranchness at that
point. -/
theorem geometricallyUnibranchAt_toGroupoids_iff {S : Scheme.{u}}
    (F : AlgebraicSpace S) (x : AlgebraicSpace.Points F) :
    GeometricallyUnibranchAt F.toGroupoids (Points.ofAlgebraicSpace x) ↔
      AlgebraicSpace.GeometricallyUnibranchAt F x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
