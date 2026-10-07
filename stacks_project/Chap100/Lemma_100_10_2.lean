module

public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Lemma_100_9_10_Substack
public import stacks_project.Chap100.Lemma_100_11_2_Reduced

/-!
# Reduced algebraic stacks are determined by their closed substack of points

A closed substack of a reduced algebraic stack that contains every point of the
ambient stack is the whole stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.ClosedSubstack

/-- Lemma 100.10.2: Let `X` be an algebraic stack. If `Z` is a closed substack
of `X`, `X` is reduced, and `|Z.Y| = |X|` in the sense that
`Set.range (Points.map Z.ι) = Set.univ`, then `Z` is the whole stack, i.e.
`(toBasedFunctor Z.ι).IsEquivalence`. -/
@[stacks 050A]
theorem isEquivalence_of_isReduced {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsReduced X] (Z : ClosedSubstack X)
    (h : Set.range (Points.map Z.ι) = Set.univ) :
    (toBasedFunctor Z.ι).IsEquivalence :=
  sorry

/-- On a reduced algebraic stack, a closed substack containing every point has
the same `objectProperty` as the identity substack. -/
theorem objectProperty_eq_of_isReduced {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsReduced X] (Z : ClosedSubstack X)
    (h : Set.range (Points.map Z.ι) = Set.univ) :
    Z.objectProperty = (toFunctor (𝟙 X)).essImage :=
  sorry

/-- A closed substack of a reduced algebraic stack is the whole stack if and
only if its image of points is all of `|X|`. -/
theorem isEquivalence_iff_range_eq_univ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsReduced X] (Z : ClosedSubstack X) :
    (toBasedFunctor Z.ι).IsEquivalence ↔
      Set.range (Points.map Z.ι) = Set.univ :=
  sorry

end AlgebraicGeometry.AlgebraicStack.ClosedSubstack
