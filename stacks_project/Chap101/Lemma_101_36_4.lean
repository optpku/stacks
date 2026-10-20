module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale.Unramified
import StacksCheckRecall

/-!
# Étale morphisms of algebraic stacks are unramified
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.36.4: An étale morphism of algebraic stacks is unramified. -/
@[stacks 0CIW] #check (AlgebraicGeometry.AlgebraicStack.unramified_of_etale :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Etale f], Unramified f)

end AlgebraicGeometry.AlgebraicStack
