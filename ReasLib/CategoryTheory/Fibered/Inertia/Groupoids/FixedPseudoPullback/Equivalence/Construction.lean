module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.FixedPseudoPullback.Inverse.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Equivalence.Construction
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed groupoid-fibred relative-inertia comparison equivalence

This leaf owns the canonical equivalence and its forward and inverse `1`-morphisms.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Groupoids.RelativeInertia

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

section FixedPseudoPullbackOwner

variable {X Y :
  FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}

/-- The canonical bicategorical equivalence between relative inertia and the
self-two-fibre-product of the relative diagonal in groupoid fibrations. -/
@[stacks 034H "groupoid-fibred relative inertia as a self-two-fibre-product"]
noncomputable def diagonalComparisonEquivalence (F : X ⟶ Y) :
    relativeInertia F ≌
      CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F) :=
  ObjectProperty.FullSubbicategory.equivalenceOfAmbient
    (BasedFunctor.RelativeInertia.diagonalComparison.quasiInverse
      (FiberedCategoryOver.Groupoids.toBasedFunctor F)).toEquivalence

/-- The forward `1`-morphism of the groupoid-fibration relative-inertia equivalence is the
canonical comparison. -/
@[simp]
theorem diagonalComparisonEquivalence.hom (F : X ⟶ Y) :
    (diagonalComparisonEquivalence F).hom = diagonalComparison F := sorry

/-- The inverse `1`-morphism of the groupoid-fibration relative-inertia equivalence is the
explicit recovered comparison inverse. -/
@[simp]
theorem diagonalComparisonEquivalence.inv (F : X ⟶ Y) :
    (diagonalComparisonEquivalence F).inv = diagonalComparison.inverse F := sorry

/-- Lemma 4.34.1 (1) (Stacks 034H): groupoid-fibred relative inertia occurs as the source of
an equivalence to the self-two-fibre-product of the relative diagonal. The canonical equivalence
above remains the sole data owner; this proposition-valued bridge serves existential consumers. -/
@[stacks 034H "groupoid-fibred relative inertia as a self-two-fibre-product"]
theorem exists_diagonalComparisonEquivalence (F : X ⟶ Y) :
    ∃ e :
        relativeInertia F ≌
          CategoryTheory.TwoFibreProduct.apex
            (relativeDiagonal F) (relativeDiagonal F),
      e.hom = diagonalComparison F := sorry

end FixedPseudoPullbackOwner

end FiberedCategoryOver.Groupoids.RelativeInertia
end CategoryTheory
