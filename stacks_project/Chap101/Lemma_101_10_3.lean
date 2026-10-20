module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Finite.Composition
import StacksCheckRecall

/-!
# Composition of integral and finite morphisms of algebraic stacks

The composition of a pair of integral morphisms of algebraic stacks is
integral, and the composition of a pair of finite morphisms of algebraic
stacks is finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.10.3 (1): compositions of integral morphisms of algebraic stacks
are integral. -/
@[stacks 0CHW] #check (AlgebraicGeometry.AlgebraicStack.IsIntegralHom.comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegralHom f] [IsIntegralHom g],
    IsIntegralHom (f ≫ g))

/- Lemma 101.10.3 (2): compositions of finite morphisms of algebraic stacks
are finite. -/
@[stacks 0CHW] #check (AlgebraicGeometry.AlgebraicStack.IsFinite.comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsFinite f] [IsFinite g],
    IsFinite (f ≫ g))

end AlgebraicGeometry.AlgebraicStack
