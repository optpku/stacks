module

import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism
import StacksCheckRecall

/-!
# Composition of universal homeomorphisms of algebraic stacks

The composition of a pair of universal homeomorphisms of algebraic stacks is a
universal homeomorphism.
-/

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.15.4: The composition of a pair of universal homeomorphisms of
algebraic stacks is a universal homeomorphism. -/
@[stacks 0CI9] #check
  (AlgebraicGeometry.AlgebraicStack.UniversalHomeomorphism.comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicStack.UniversalHomeomorphism f] [AlgebraicStack.UniversalHomeomorphism g],
    AlgebraicStack.UniversalHomeomorphism (f ≫ g))
