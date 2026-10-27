/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Setoid.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Comparison

/-!
# Points of a quotient stack of a groupoid in algebraic spaces

A groupoid `(U, R, s, t, c)` in algebraic spaces induces a pair map
`|R| → |U| × |U|` whose image is a relation on `|U|`. When `s` and `t` are
flat and locally of finite presentation, and `X = [U / R]` is an algebraic
stack, that relation is an equivalence relation and `|X|` is the quotient of
`|U|` by the kernel of the atlas map `|U| → |X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The map on points `|R| → |U| × |U|` induced by the target and source maps of
a groupoid in algebraic spaces. -/
def pointsProdMap (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.Points G.R.left → AlgebraicSpace.Points G.U.left × AlgebraicSpace.Points G.U.left :=
  fun r ↦ (AlgebraicSpace.Points.map G.t.left r, AlgebraicSpace.Points.map G.s.left r)

/-- The pair map on points sends a point of `|R|` to the pair of its images under
the target and source maps. -/
theorem pointsProdMap_apply (G : GroupoidAlgebraicSpace B)
    (r : AlgebraicSpace.Points G.R.left) :
    G.pointsProdMap r =
      (AlgebraicSpace.Points.map G.t.left r,
        AlgebraicSpace.Points.map G.s.left r) := sorry

/-- The map on points `|U| → |X|` induced by the atlas of `[U / R]`. -/
def pointsMap (G : GroupoidAlgebraicSpace B) [AlgebraicStack (SmallQuotient.quotientStack G)] :
    AlgebraicSpace.Points G.U.left → AlgebraicStack.Points (SmallQuotient.quotientStack G) :=
  AlgebraicStack.Points.mapSpace (SmallQuotient.atlas G)

/-- The atlas map on points is `AlgebraicStack.Points.mapSpace` of the atlas `1`-morphism. -/
theorem pointsMap_apply (G : GroupoidAlgebraicSpace B) [AlgebraicStack (SmallQuotient.quotientStack G)]
    (u : AlgebraicSpace.Points G.U.left) :
    G.pointsMap u = AlgebraicStack.Points.mapSpace (SmallQuotient.atlas G) u := sorry

/-- The image relation of `|R| → |U| × |U|` on the points of `|U|`. -/
def pointsRel (G : GroupoidAlgebraicSpace B) :
    AlgebraicSpace.Points G.U.left → AlgebraicSpace.Points G.U.left → Prop :=
  fun u v ↦
    ∃ r : AlgebraicSpace.Points G.R.left, AlgebraicSpace.Points.map G.t.left r = u ∧
      AlgebraicSpace.Points.map G.s.left r = v

/-- Two points of `|U|` are related by `pointsRel` exactly when they lie in the
image of the pair map `|R| → |U| × |U|`. -/
theorem pointsRel_iff (G : GroupoidAlgebraicSpace B)
    (u v : AlgebraicSpace.Points G.U.left) :
    G.pointsRel u v ↔ ∃ r, G.pointsProdMap r = (u, v) := sorry

/-- The image of `|R| → |U| × |U|` is an equivalence relation on `|U|`. -/
theorem pointsRel_equivalence (G : GroupoidAlgebraicSpace B) [Flat G]
    [LocallyOfFinitePresentation G] [AlgebraicStack (SmallQuotient.quotientStack G)] :
    Equivalence G.pointsRel := sorry

/-- The image relation of `|R| → |U| × |U|` is the kernel of the atlas map
`|U| → |X|`. -/
theorem pointsRel_iff_map_eq (G : GroupoidAlgebraicSpace B) [Flat G]
    [LocallyOfFinitePresentation G] [AlgebraicStack (SmallQuotient.quotientStack G)]
    (u v : AlgebraicSpace.Points G.U.left) :
    G.pointsRel u v ↔ G.pointsMap u = G.pointsMap v := sorry

/-- The atlas of `[U / R]` is surjective on points. -/
theorem pointsMap_surjective (G : GroupoidAlgebraicSpace B) [Flat G]
    [LocallyOfFinitePresentation G] [AlgebraicStack (SmallQuotient.quotientStack G)] :
    Function.Surjective G.pointsMap := sorry

/-- The space of points `|X|` is the quotient of `|U|` by the image of
`|R| → |U| × |U|`. -/
theorem isPointsQuotient (G : GroupoidAlgebraicSpace B) [Flat G]
    [LocallyOfFinitePresentation G] [AlgebraicStack (SmallQuotient.quotientStack G)] :
    Function.Surjective G.pointsMap ∧
      ∀ u v, G.pointsRel u v ↔ G.pointsMap u = G.pointsMap v := sorry

/-- The canonical map from the quotient of `|U|` by the kernel of the atlas to
`|X|`. -/
def pointsQuotientLift (G : GroupoidAlgebraicSpace B) [AlgebraicStack (SmallQuotient.quotientStack G)] :
    Quotient (Setoid.ker G.pointsMap) → AlgebraicStack.Points (SmallQuotient.quotientStack G) :=
  Setoid.kerLift G.pointsMap

/-- The kernel lift of the atlas sends the class of a point of `|U|` to its
image in `|X|`. -/
theorem pointsQuotientLift_mk (G : GroupoidAlgebraicSpace B)
    [AlgebraicStack (SmallQuotient.quotientStack G)] (u : AlgebraicSpace.Points G.U.left) :
    pointsQuotientLift G (Quotient.mk _ u) = G.pointsMap u := sorry

/-- The kernel lift of the atlas identifies the quotient of `|U|` by that kernel
with `|X|`. -/
theorem pointsQuotientLift_bijective (G : GroupoidAlgebraicSpace B) [Flat G]
    [LocallyOfFinitePresentation G] [AlgebraicStack (SmallQuotient.quotientStack G)] :
    Function.Bijective (pointsQuotientLift G) := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
