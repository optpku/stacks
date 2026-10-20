module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
import StacksCheckRecall

/-!
# Composition of quasi-compact morphisms of algebraic stacks

The composition of a pair of quasi-compact morphisms of algebraic stacks is
quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.7.4: The composition of a pair of quasi-compact morphisms of
algebraic stacks is quasi-compact. -/
@[stacks 050W] #check (AlgebraicGeometry.AlgebraicStack.quasiCompact_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicGeometry.AlgebraicStack.QuasiCompact f]
    [AlgebraicGeometry.AlgebraicStack.QuasiCompact g],
    AlgebraicGeometry.AlgebraicStack.QuasiCompact (f ≫ g))
