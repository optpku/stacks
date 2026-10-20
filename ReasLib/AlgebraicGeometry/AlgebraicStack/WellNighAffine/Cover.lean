module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Inertia.Comparison.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.WellNighAffine

/-!
# Étale-local well-nigh affine covers of algebraic stacks with finite inertia

Algebraic stacks with finite inertia admit stabilizer-preserving, separated,
étale covers by well-nigh affine algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Every point of an algebraic stack with finite inertia lies in the image of
an étale, separated morphism representable by algebraic spaces from a well-nigh
affine algebraic stack, whose canonical inertia comparison is an equivalence. -/
theorem existsEtaleLocalWellNighAffineChartAt {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] (x : Points X) :
    ∃ (Xi : GroupoidsOver S) (hXi : AlgebraicStack Xi) (g : Xi ⟶ X)
      (xi : Points Xi),
      Points.map g xi = x ∧ IsWellNighAffine Xi ∧
        (toBasedFunctor (Inertia.comparison g)).IsEquivalence ∧
        relativelyRepresentableByAlgebraicSpaces g ∧ Separated g ∧
          Groupoids.Hom.Etale g :=
  sorry

/-- An algebraic stack with finite inertia admits a set-indexed covering by
well-nigh affine algebraic stacks through morphisms representable by algebraic
spaces, separated, and étale, whose canonical inertia comparisons are
equivalences. -/
@[stacks 0DUE]
theorem existsEtaleLocalWellNighAffineCover_of_isFinite_inertia
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsFinite (forget.{u + 1, u, u, u + 1} X)] :
    ∃ (I : Type (u + 1)) (Xi : I → GroupoidsOver S)
        (hXi : ∀ i, AlgebraicStack (Xi i)) (g : ∀ i, Xi i ⟶ X),
      (⋃ i, Set.range (Points.map (g i))) = Set.univ ∧
        ∀ i, IsWellNighAffine (Xi i) ∧
          (toBasedFunctor (Inertia.comparison (g i))).IsEquivalence ∧
          relativelyRepresentableByAlgebraicSpaces (g i) ∧ Separated (g i) ∧
            Groupoids.Hom.Etale (g i) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
