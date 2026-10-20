module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyOpen
import StacksCheckRecall

/-!
# Composition of open morphisms of algebraic stacks

The composition of a pair of open morphisms of algebraic stacks is open,
and the composition of a pair of universally open morphisms of algebraic
stacks is universally open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.11.4 (1): The composition of a pair of open morphisms of
algebraic stacks is open. -/
@[stacks 06U4] #check (AlgebraicGeometry.AlgebraicStack.Open.comp.{u} :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Open f] [Open g],
    Open (f ≫ g))

/- Lemma 101.11.4 (2): The composition of a pair of universally open
morphisms of algebraic stacks is universally open. -/
@[stacks 06U4] #check (AlgebraicGeometry.AlgebraicStack.UniversallyOpen.comp.{u} :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyOpen f] [UniversallyOpen g],
    UniversallyOpen (f ≫ g))

end AlgebraicGeometry.AlgebraicStack
