/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fixed.Inverse.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Equivalence.Construction
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Equivalence
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Fibered.Closure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibred relative-inertia comparison equivalence

This leaf owns the canonical equivalence and its forward and inverse `1`-morphisms.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.RelativeInertia

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

section FixedOwner

variable {X Y :
  FiberedCategoryOver.{u, v, max w (max u v), v} C}

/-- The canonical bicategorical equivalence between relative inertia and the
self-two-fibre-product of the relative diagonal. -/
@[stacks 034H "fibred relative-inertia diagonal-comparison equivalence"]
noncomputable def diagonalComparisonEquivalence (F : X ⟶ Y) :
    relativeInertia F ≌
      LocallyInduced.TwoFibreProduct.apex
        (RelativeInertia.relativeDiagonal F)
        (RelativeInertia.relativeDiagonal F) :=
  Bicategory.LocallyInducedBicategory.equivalenceMk
    (BasedFunctor.RelativeInertia.diagonalComparison.quasiInverse
      (FiberedCategoryOver.toBasedFunctor F)).toEquivalence
    (RelativeInertia.diagonalComparison.preservesStronglyCartesian F)
    (RelativeInertia.diagonalComparison.inverse.preservesStronglyCartesian F)

/-- The forward `1`-morphism of the canonical relative-inertia comparison equivalence is the
canonical comparison. -/
@[simp]
theorem diagonalComparisonEquivalence.hom (F : X ⟶ Y) :
    (RelativeInertia.diagonalComparisonEquivalence F).hom =
      RelativeInertia.diagonalComparison F := sorry

/-- The inverse `1`-morphism of the canonical relative-inertia comparison equivalence is the
explicit recovered comparison inverse. -/
@[simp]
theorem diagonalComparisonEquivalence.inv (F : X ⟶ Y) :
    (RelativeInertia.diagonalComparisonEquivalence F).inv =
      RelativeInertia.diagonalComparison.inverse F := sorry

/-- Lemma 4.34.1 (1) (Stacks 034H): relative inertia occurs as the source of an equivalence to the
self-two-fibre-product of the relative diagonal whose forward morphism is the canonical
comparison. This proposition-valued bridge is retained for existential consumers;
`RelativeInertia.diagonalComparisonEquivalence` owns the canonical data. -/
@[stacks 034H "relative inertia as a self-two-fibre-product"]
theorem exists_diagonalComparisonEquivalence (F : X ⟶ Y) :
    ∃ e :
        relativeInertia F ≌
          LocallyInduced.TwoFibreProduct.apex
            (RelativeInertia.relativeDiagonal F)
            (RelativeInertia.relativeDiagonal F),
      e.hom = RelativeInertia.diagonalComparison F := sorry
/- Proof strategy: use `RelativeInertia.diagonalComparisonEquivalence F` and
`RelativeInertia.diagonalComparisonEquivalence.hom F`. -/

end FixedOwner

end FiberedCategoryOver.RelativeInertia
end CategoryTheory
