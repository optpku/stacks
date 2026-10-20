module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage.Existence
import StacksCheckRecall

/-!
# Existence of scheme-theoretic images of morphisms of algebraic stacks

Every morphism of algebraic stacks has a scheme-theoretic image: a least
strictly full closed substack of the target through which it factors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.38.3: Let `f : 𝒴 ⟶ 𝒳` be a morphism of algebraic stacks.
Then the scheme-theoretic image of `f` exists. -/
@[stacks 0CPU] #check (AlgebraicGeometry.AlgebraicStack.hasSchemeTheoreticImage :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y), HasSchemeTheoreticImage f)

end AlgebraicGeometry.AlgebraicStack
