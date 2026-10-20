module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat.Composition
import StacksCheckRecall

/-!
# Composition of flat morphisms of algebraic stacks

The composition of a pair of flat morphisms of algebraic stacks is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.25.2: The composition of flat morphisms of algebraic stacks is flat. -/
@[stacks 06PX] #check (AlgebraicGeometry.AlgebraicStack.Flat.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicStack.Flat f] [AlgebraicStack.Flat g],
    AlgebraicStack.Flat (f ≫ g))
