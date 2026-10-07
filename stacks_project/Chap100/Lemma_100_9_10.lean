module

public import stacks_project.Chap100.Lemma_100_9_10_Substack

/-!
# Image of an immersion of algebraic stacks

An immersion of algebraic stacks factors uniquely through a locally closed
substack of the target, namely the essential image of the underlying total
functor. Closed and open immersions yield closed and open substacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {Z X : GroupoidsOver S}

/-- Lemma 100.9.10 (1): For any immersion `i : Z ⟶ X` there exists a unique
locally closed substack `X' ⊂ X` such that `i` factors as the composition of
an equivalence `i' : Z ⟶ X'` followed by the inclusion `X' ⟶ X`. The
canonical such substack is `image i`, with equivalence `imageLift i`.
Uniqueness is equality of `objectProperty`, not of a bundled pair `(Y, ι)`. -/
@[stacks 0506]
theorem existsUnique_image [AlgebraicStack Z] [AlgebraicStack X]
    (i : Z ⟶ X) [Immersion i] :
    (toBasedFunctor (LocallyClosedSubstack.imageLift i)).IsEquivalence ∧
      LocallyClosedSubstack.imageLift i ≫
          (LocallyClosedSubstack.image i).ι = i ∧
        ∀ {X' : LocallyClosedSubstack X} {i' : Z ⟶ X'.Y},
          (toBasedFunctor i').IsEquivalence →
            i' ≫ X'.ι = i →
              X'.objectProperty = LocallyClosedSubstack.imageObjects i := sorry

/-- Lemma 100.9.10 (2): If `i` is a closed immersion, then the unique locally
closed image of `i` is a closed substack of `X`. -/
@[stacks 0506]
theorem image_isClosed [AlgebraicStack Z] [AlgebraicStack X]
    (i : Z ⟶ X) [ClosedImmersion i] :
    (ClosedSubstack.image i).toLocallyClosed =
        LocallyClosedSubstack.image i ∧
      ClosedImmersion (LocallyClosedSubstack.image i).ι := sorry

/-- Lemma 100.9.10 (3): If `i` is an open immersion, then the unique locally
closed image of `i` is an open substack of `X`. -/
@[stacks 0506]
theorem image_isOpen [AlgebraicStack Z] [AlgebraicStack X]
    (i : Z ⟶ X) [OpenImmersion i] :
    (OpenSubstack.image i).toLocallyClosed =
        LocallyClosedSubstack.image i ∧
      OpenImmersion (LocallyClosedSubstack.image i).ι := sorry

end AlgebraicGeometry.AlgebraicStack
