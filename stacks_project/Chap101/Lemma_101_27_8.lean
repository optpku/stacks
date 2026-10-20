module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.OpenImmersion
import StacksCheckRecall

/-!
# Open immersions of algebraic stacks are locally of finite presentation
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.27.8: An open immersion of algebraic stacks is locally of finite
presentation. -/
@[stacks 06Q7] #check
  (AlgebraicGeometry.AlgebraicStack.locallyOfFinitePresentation_of_openImmersion :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y) [AlgebraicGeometry.Groupoids.Hom.OpenImmersion f],
      AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation f)

end AlgebraicGeometry.AlgebraicStack
