module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FinitePresentation.Composition
import StacksCheckRecall

/-!
# Composition of finite presentation morphisms of algebraic stacks

The composition of a pair of finite presentation morphisms of algebraic stacks
is of finite presentation, and the same holds for morphisms locally of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.27.2 (1): The composition of finitely presented morphisms of
algebraic stacks is of finite presentation. -/
@[stacks 06Q3] #check (AlgebraicGeometry.AlgebraicStack.finitePresentation_comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z), [FinitePresentation f] → [FinitePresentation g] →
    FinitePresentation (f ≫ g))

/- Lemma 101.27.2 (2): The composition of morphisms of algebraic stacks which
are locally of finite presentation is locally of finite presentation. -/
@[stacks 06Q3] #check (AlgebraicGeometry.AlgebraicStack.locallyOfFinitePresentation_comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z),
    [LocallyOfFinitePresentation f] → [LocallyOfFinitePresentation g] →
    LocallyOfFinitePresentation (f ≫ g))

end AlgebraicGeometry.AlgebraicStack
