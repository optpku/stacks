module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Gerbe.Decent
import StacksCheckRecall

/-!
# Descent of decency along gerbes

If `f : X ⟶ Y` is a gerbe morphism of algebraic stacks and `X` is decent, then
`Y` is decent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.48.5: Let `f : X ⟶ Y` be a morphism of algebraic stacks. If `X`
is a gerbe over `Y` and `X` is decent, then `Y` is decent. -/
@[stacks 0GW5] #check
  (AlgebraicGeometry.AlgebraicStack.IsDecent.of_gerbe :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Gerbe f]
      [IsDecent X], IsDecent Y)

end AlgebraicGeometry.AlgebraicStack
