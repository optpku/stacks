module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Decent.Surjective
import StacksCheckRecall

/-!
# Descent of decency along quasi-compact surjections

If `f : X ⟶ Y` is a quasi-compact surjective morphism of algebraic stacks and
`X` is decent, then `Y` is decent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.48.4: Let `f : X ⟶ Y` be a morphism of algebraic stacks. If `f`
is quasi-compact and surjective and `X` is decent, then `Y` is decent. -/
@[stacks 0GW4] #check
  (AlgebraicGeometry.AlgebraicStack.IsDecent.of_quasiCompact_surjective :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      [QuasiCompact f] [Surjective f] [IsDecent X], IsDecent Y)

end AlgebraicGeometry.AlgebraicStack
