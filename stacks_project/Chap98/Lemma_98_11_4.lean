module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Diagonal.FiniteType
import StacksCheckRecall

/-!
# Diagonals of limit-preserving categories fibred in groupoids

If a category fibred in groupoids over `(Sch/S)_fppf` is limit preserving and
its absolute diagonal is representable by algebraic spaces, then that diagonal
is locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids

/- Lemma 98.11.4: let `S` be a scheme and let `X` be a category fibred in
groupoids over `(Sch/S)_fppf`. If the diagonal `Δ : X ⟶ X × X` is
representable by algebraic spaces and `X` is limit preserving, then `Δ` is
locally of finite type. -/
@[stacks 0CXI] #check (AlgebraicGeometry.Groupoids.locallyOfFiniteType_diagonal :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [LimitPreserving X],
      relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) →
      Hom.LocallyOfFiniteType
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))

end AlgebraicGeometry.Groupoids
