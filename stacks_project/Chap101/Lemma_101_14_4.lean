module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective.Composition
import StacksCheckRecall

/-!
# Composition of universally injective morphisms of algebraic stacks

The composition of a pair of universally injective morphisms of algebraic
stacks is universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.14.4: The composition of a pair of universally injective
morphisms of algebraic stacks is universally injective. -/
@[stacks 0CI4] #check
  (AlgebraicGeometry.AlgebraicStack.UniversallyInjective.comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.AlgebraicStack.UniversallyInjective f]
    [AlgebraicGeometry.AlgebraicStack.UniversallyInjective g],
    AlgebraicGeometry.AlgebraicStack.UniversallyInjective (f ≫ g))
