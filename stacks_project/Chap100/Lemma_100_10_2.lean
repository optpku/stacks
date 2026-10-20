module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced.ClosedImmersion
import StacksCheckRecall

/-!
# Reduced algebraic stacks are determined by their closed substack of points

A closed substack of a reduced algebraic stack that contains every point of the
ambient stack is the whole stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 100.10.2: A closed substack containing every point of a reduced
algebraic stack is the whole stack. -/
@[stacks 050A] #check
  (AlgebraicGeometry.Groupoids.Hom.ClosedImmersion.isEquivalence_of_isReduced :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack.IsReduced X]
      (i : Y ⟶ X) [Groupoids.Hom.ClosedImmersion i],
      Set.range (AlgebraicStack.Points.map i) = Set.univ →
        (toBasedFunctor i).IsEquivalence)

#check
  (AlgebraicGeometry.Groupoids.Hom.ClosedImmersion.essImage_eq_of_isReduced :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack.IsReduced X]
      (i : Y ⟶ X) [Groupoids.Hom.ClosedImmersion i],
      Set.range (AlgebraicStack.Points.map i) = Set.univ →
        (toFunctor i).essImage = (toFunctor (𝟙 X)).essImage)

#check
  (AlgebraicGeometry.Groupoids.Hom.ClosedImmersion.isEquivalence_iff_range_eq_univ :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack.IsReduced X]
      (i : Y ⟶ X) [Groupoids.Hom.ClosedImmersion i],
      (toBasedFunctor i).IsEquivalence ↔
        Set.range (AlgebraicStack.Points.map i) = Set.univ)
