/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap100.Lemma_100_9_10_Substack
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.ClosedImmersion

/-!
# Points of a closed substack

A closed substack `Z ⊂ X` determines a closed subset `|Z| ⊆ |X|`, namely the
image of the induced map on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.ClosedSubstack

/-- The underlying set of points of a closed substack, as the image of `|Z| → |X|`. -/
def pointsSet {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (Z : ClosedSubstack X) : Set (Points X) :=
  Set.range (Points.map Z.ι)

/-- `pointsSet Z` is the range of `Points.map Z.ι`. -/
theorem pointsSet_eq {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (Z : ClosedSubstack X) :
    Z.pointsSet = Set.range (Points.map Z.ι) :=
  rfl

/-- A point of `|X|` lies in `pointsSet Z` if and only if it is the image of a
point of `|Z|`. -/
theorem mem_pointsSet {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (Z : ClosedSubstack X) {x : Points X} :
    x ∈ Z.pointsSet ↔ ∃ y : Points Z.Y, Points.map Z.ι y = x :=
  Iff.rfl

/-- The image `|Z| ⊆ |X|` is closed in the canonical topology on `|X|`. -/
theorem isClosed_pointsSet {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (Z : ClosedSubstack X) :
    IsClosed (Z.pointsSet : Set (Points X)) :=
  Points.isClosed_range_of_closedImmersion Z.ι

end AlgebraicGeometry.AlgebraicStack.ClosedSubstack
