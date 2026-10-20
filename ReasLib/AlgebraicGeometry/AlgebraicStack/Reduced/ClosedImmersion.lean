module

public import Mathlib.CategoryTheory.EssentialImage
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Surjective
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic

/-!
# Reduced closed immersions of algebraic stacks

Every closed subset of an algebraic stack has a reduced closed-substack
structure, unique as an essential-image object property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (toFunctor toBasedFunctor)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Reduced closed immersions with the same range on points have the same
essential-image object property. -/
theorem reduced_closedImmersion_essImage_eq {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack Z] (i : Y ⟶ X) (j : Z ⟶ X)
    [Groupoids.Hom.ClosedImmersion i] [Groupoids.Hom.ClosedImmersion j]
    (hY : IsReduced Y) (hZ : IsReduced Z)
    (h_eq : Set.range (Points.map i) = Set.range (Points.map j)) :
    (toFunctor i).essImage = (toFunctor j).essImage :=
  sorry

/-- Every closed subset of the points of an algebraic stack is the range of a
fully faithful reduced closed immersion, unique as an essential-image object
property. -/
theorem exists_reduced_closedImmersion {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (T : Set (Points X)) (hT : IsClosed T) :
    ∃ (Y : GroupoidsOver S) (_ : AlgebraicStack Y) (i : Y ⟶ X),
      Groupoids.Hom.ClosedImmersion i ∧
        (toFunctor i).Full ∧ (toFunctor i).Faithful ∧
          Set.range (Points.map i) = T ∧ IsReduced Y ∧
            ∀ (Z : GroupoidsOver S) [AlgebraicStack Z] (j : Z ⟶ X),
              Groupoids.Hom.ClosedImmersion j → Set.range (Points.map j) = T →
                IsReduced Z → (toFunctor j).essImage = (toFunctor i).essImage :=
  sorry

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.Groupoids.Hom.ClosedImmersion

/-- A closed immersion into a reduced algebraic stack whose range on points is
the whole space is an equivalence over the base. -/
theorem isEquivalence_of_isReduced {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack.IsReduced X]
    (i : Y ⟶ X) [ClosedImmersion i]
    (h : Set.range (AlgebraicStack.Points.map i) = Set.univ) :
    (toBasedFunctor i).IsEquivalence :=
  sorry

/-- A closed immersion into a reduced algebraic stack whose range on points is
the whole space has the same essential image as the identity. -/
theorem essImage_eq_of_isReduced {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack.IsReduced X]
    (i : Y ⟶ X) [ClosedImmersion i]
    (h : Set.range (AlgebraicStack.Points.map i) = Set.univ) :
    (toFunctor i).essImage = (toFunctor (𝟙 X)).essImage :=
  sorry

/-- A closed immersion into a reduced algebraic stack is an equivalence over
the base if and only if its range on points is the whole space. -/
theorem isEquivalence_iff_range_eq_univ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack.IsReduced X]
    (i : Y ⟶ X) [ClosedImmersion i] :
    (toBasedFunctor i).IsEquivalence ↔
      Set.range (AlgebraicStack.Points.map i) = Set.univ :=
  sorry

/-- A surjective closed immersion into a reduced algebraic stack is an
equivalence over the base. -/
instance isEquivalence_of_surjective_of_isReduced {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack.IsReduced X] (i : Y ⟶ X) [ClosedImmersion i] [Surjective i] :
    (toBasedFunctor i).IsEquivalence :=
  sorry

end AlgebraicGeometry.Groupoids.Hom.ClosedImmersion
