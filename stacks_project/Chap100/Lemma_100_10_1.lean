module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced.ClosedImmersion
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
open FiberedCategoryOver.Groupoids (toFunctor)

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 100.10.1: Every closed subset of the points of an algebraic stack
has a unique reduced closed-substack structure. -/
@[stacks 0509] #check (AlgebraicGeometry.AlgebraicStack.exists_reduced_closedImmersion :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (T : Set (Points X)) (hT : IsClosed T),
    ∃ (Y : GroupoidsOver S) (_ : AlgebraicStack Y) (i : Y ⟶ X),
      Groupoids.Hom.ClosedImmersion i ∧
        (toFunctor i).Full ∧ (toFunctor i).Faithful ∧
          Set.range (Points.map i) = T ∧ IsReduced Y ∧
            ∀ (Z : GroupoidsOver S) [AlgebraicStack Z] (j : Z ⟶ X),
              Groupoids.Hom.ClosedImmersion j → Set.range (Points.map j) = T →
                IsReduced Z → (toFunctor j).essImage = (toFunctor i).essImage)

namespace ClosedSubstack

/-- Let `X` be an algebraic stack, and let `T ⊂ |X|` be a closed
subset. There exists a unique closed substack `Z ⊂ X` with `|Z| = T` in the
sense that `Z.pointsSet = T`, and with `Z` reduced, in the sense that
`hasSmoothLocal IsReduced` holds on `Z.Y`. Uniqueness is equality of
`objectProperty`, not of a unique morphism over `X`. -/
theorem exists_reduced {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (T : Set (Points X)) (hT : IsClosed T) :
    ∃ Z : ClosedSubstack X,
      Z.pointsSet = T ∧
        hasSmoothLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z.Y ∧
          ∀ Z' : ClosedSubstack X, Z'.pointsSet = T →
            hasSmoothLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z'.Y →
              Z'.objectProperty = Z.objectProperty := by
  obtain ⟨Y, hY, i, hi, hfull, hfaithful, hpoints, hred, huniq⟩ :=
    exists_reduced_closedImmersion T hT
  let Z : ClosedSubstack X :=
    { Y := Y
      ι := i
      isAlgebraicStack := hY
      isClosedImmersion := hi
      isStrictlyFull := ⟨hfull, hfaithful⟩ }
  refine ⟨Z, hpoints, ?_, ?_⟩
  · exact (isReduced_iff_existsSurjectiveSmooth Y).mp hred
  · intro Z' hZ' hred'
    exact huniq Z'.Y Z'.ι Z'.isClosedImmersion hZ'
      ((isReduced_iff_existsSurjectiveSmooth Z'.Y).mpr hred')

/-- Any two reduced closed substacks of `X` with the same underlying point-set
determine the same strictly full subcategory of `X`. -/
theorem unique {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Z Z' : ClosedSubstack X} (h_eq : Z.pointsSet = Z'.pointsSet)
    (hZ : hasSmoothLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z.Y)
    (hZ' : hasSmoothLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z'.Y) :
    Z.objectProperty = Z'.objectProperty := by
  exact reduced_closedImmersion_essImage_eq Z.ι Z'.ι
    ((isReduced_iff_existsSurjectiveSmooth Z.Y).mpr hZ)
    ((isReduced_iff_existsSurjectiveSmooth Z'.Y).mpr hZ') h_eq

end ClosedSubstack

end AlgebraicGeometry.AlgebraicStack
