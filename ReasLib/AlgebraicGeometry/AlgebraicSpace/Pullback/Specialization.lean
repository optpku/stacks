/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison

/-!
# Specializations in scheme-valued base changes

A specialization in a scheme over an algebraic space, together with a point of a
base change above its generic endpoint, determines a pointed cartesian diagram.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A scheme-valued base change with a specialization whose special endpoint maps to
`y`, and a point of the base change above its generic endpoint. -/
structure SpecializationDiagram {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (y : Points Y) where
  /-- The scheme over the base in which the specialization occurs. -/
  T : Over S
  /-- The morphism from the chosen scheme to the target algebraic space. -/
  g : ofOver T ⟶ Y
  /-- The generic endpoint of the chosen specialization. -/
  genericPoint : T.left
  /-- The special endpoint of the chosen specialization. -/
  specialPoint : T.left
  /-- The generic endpoint specializes to the special endpoint. -/
  specializes : Specializes genericPoint specialPoint
  /-- The special endpoint maps to the prescribed target point. -/
  map_specialPoint : Points.map g (ofOver.pointsEquiv T specialPoint) = y
  /-- The chosen point of the canonical base change. -/
  point : Points (Limits.pullback f g)
  /-- The chosen pullback point lies above the generic endpoint. -/
  map_point : Points.map (Limits.pullback.snd f g) point =
    ofOver.pointsEquiv T genericPoint

namespace SpecializationDiagram

/-- Package a scheme-valued base change, a specialization over a prescribed point,
and a pullback point above its generic endpoint into a specialization diagram. -/
def of {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y)
    (T : Over S) (g : ofOver T ⟶ Y) (genericPoint specialPoint : T.left)
    (specializes : Specializes genericPoint specialPoint)
    (map_specialPoint : Points.map g (ofOver.pointsEquiv T specialPoint) = y)
    (point : Points (Limits.pullback f g))
    (map_point : Points.map (Limits.pullback.snd f g) point =
      ofOver.pointsEquiv T genericPoint) : SpecializationDiagram f y where
  T := T
  g := g
  genericPoint := genericPoint
  specialPoint := specialPoint
  specializes := specializes
  map_specialPoint := map_specialPoint
  point := point
  map_point := map_point

/-- A specialization diagram satisfies its specialization and point incidences,
and its canonical base-change square is cartesian. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {y : Points Y}
    (D : SpecializationDiagram f y) :
    Specializes D.genericPoint D.specialPoint ∧
      Points.map D.g (ofOver.pointsEquiv D.T D.specialPoint) = y ∧
      Points.map (Limits.pullback.snd f D.g) D.point =
        ofOver.pointsEquiv D.T D.genericPoint ∧
      IsPullback (Limits.pullback.fst f D.g) (Limits.pullback.snd f D.g) f D.g :=
  ⟨D.specializes, D.map_specialPoint, D.map_point, IsPullback.of_hasPullback f D.g⟩

end SpecializationDiagram

end AlgebraicGeometry.AlgebraicSpace
