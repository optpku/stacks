module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Decent.Representable
import StacksCheckRecall

/-!
# Decent algebraic stacks along representable morphisms

If `Y` is a decent algebraic stack and `f : X ⟶ Y` is representable by
schemes, or representable by algebraic spaces and quasi-separated, then `X` is
decent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.48.3 (1): Let `f : X ⟶ Y` be a morphism of algebraic stacks.
If `Y` is decent and `f` is representable by schemes, then `X` is decent.
Stacks-project representability by schemes is
`FiberedCategoryOver.Groupoids.relativelyRepresentable`. -/
@[stacks 0GW3]
#check (AlgebraicGeometry.AlgebraicStack.IsDecent.of_relativelyRepresentable :
    ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (hf : FiberedCategoryOver.Groupoids.relativelyRepresentable f)
    [IsDecent Y], IsDecent X)

/- Lemma 101.48.3 (2): Let `f : X ⟶ Y` be a morphism of algebraic stacks.
If `Y` is decent and `f` is representable by algebraic spaces and
quasi-separated, then `X` is decent. -/
@[stacks 0GW3]
#check (AlgebraicGeometry.AlgebraicStack.IsDecent.of_relativelyRepresentableByAlgebraicSpaces :
    ∀ {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (hf : relativelyRepresentableByAlgebraicSpaces f)
    [IsDecent Y] [QuasiSeparated f], IsDecent X)

end AlgebraicGeometry.AlgebraicStack
