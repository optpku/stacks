/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Lemma_100_10_1_Points
public import stacks_project.Chap100.Definition_100_7_2_SmoothLocal
public import ReasLib.AlgebraicGeometry.Scheme.Reduced.Smooth

/-!
# Unique reduced closed substack on a closed set of points

A closed subset `T ⊂ |X|` of the points of an algebraic stack is the underlying
point-set of a unique reduced closed substack `Z ⊂ X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.ClosedSubstack

/-- Lemma 100.10.1: let `X` be an algebraic stack, and let `T ⊂ |X|` be a closed
subset. There exists a unique closed substack `Z ⊂ X` with `|Z| = T` in the
sense that `Z.pointsSet = T`, and with `Z` reduced, in the sense that
`hasSmoothLocal IsReduced` holds on `Z.Y`. Uniqueness is equality of
`objectProperty`, not of a unique morphism over `X`. -/
@[stacks 0509]
theorem exists_reduced {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (T : Set (Points X)) (hT : IsClosed T) :
    ∃ Z : ClosedSubstack X,
      Z.pointsSet = T ∧
        hasSmoothLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z.Y ∧
          ∀ Z' : ClosedSubstack X, Z'.pointsSet = T →
            hasSmoothLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z'.Y →
              Z'.objectProperty = Z.objectProperty :=
  sorry

/-- Any two reduced closed substacks of `X` with the same underlying point-set
determine the same strictly full subcategory of `X`. -/
theorem unique {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Z Z' : ClosedSubstack X} (h_eq : Z.pointsSet = Z'.pointsSet)
    (hZ : hasSmoothLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z.Y)
    (hZ' : hasSmoothLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z'.Y) :
    Z.objectProperty = Z'.objectProperty :=
  sorry

end AlgebraicGeometry.AlgebraicStack.ClosedSubstack
