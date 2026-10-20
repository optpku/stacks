module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.Immersion
import StacksCheckRecall

/-!
# Immersions of algebraic stacks are locally of finite type
-/

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.17.4. An immersion of algebraic stacks is locally of finite type. -/
@[stacks 06FV] #check
  (AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType.of_immersion :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Groupoids.Hom.Immersion f],
      AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType f)
