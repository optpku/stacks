module

public import stacks_project.Chap101.Lemma_101_27_3_BaseChange

/-!
# Base change of finite presentation morphisms of algebraic stacks

A base change of a finitely presented morphism of algebraic stacks is of
finite presentation. The same holds for morphisms which are locally of
finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.FinitePresentation

/-- Lemma 101.27.3 (1): A base change of a finitely presented morphism of
algebraic stacks is of finite presentation.

Stacks writes the base change as `Y' ×_Y X ⟶ Y'`; the Lean projection is
`TwoFibreProduct.snd f g` of a finitely presented morphism `f : X ⟶ Y` along
a test morphism `g : Z ⟶ Y`. -/
@[stacks 06Q4]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [FinitePresentation f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    FinitePresentation (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.FinitePresentation

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-- Lemma 101.27.3 (2): A base change of a morphism of algebraic stacks which
is locally of finite presentation is locally of finite presentation.

Stacks writes the base change as `Y' ×_Y X ⟶ Y'`; the Lean projection is
`TwoFibreProduct.snd f g` of a locally of finite presentation morphism
`f : X ⟶ Y` along a test morphism `g : Z ⟶ Y`. -/
@[stacks 06Q4]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [LocallyOfFinitePresentation f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    LocallyOfFinitePresentation
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
