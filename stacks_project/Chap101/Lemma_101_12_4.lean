module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Submersive.Composition
import StacksCheckRecall

/-!
# Composition of submersive morphisms of algebraic stacks

The composition of a pair of submersive morphisms of algebraic stacks is
submersive, and the composition of a pair of universally submersive morphisms
of algebraic stacks is universally submersive.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.12.4 (1): The composition of a pair of submersive morphisms of
algebraic stacks is submersive. -/
@[stacks 0CHZ]
#check (AlgebraicGeometry.AlgebraicStack.Submersive.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Submersive f] [Submersive g],
    Submersive (f ≫ g))

/- Lemma 101.12.4 (2): The composition of a pair of universally submersive
morphisms of algebraic stacks is universally submersive. -/
@[stacks 0CHZ]
#check (AlgebraicGeometry.AlgebraicStack.UniversallySubmersive.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallySubmersive f] [UniversallySubmersive g],
    UniversallySubmersive (f ≫ g))

end AlgebraicGeometry.AlgebraicStack
