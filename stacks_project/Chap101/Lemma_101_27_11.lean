module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.Descent
import StacksCheckRecall

/-!
# Descent of local finite presentation for morphisms of algebraic stacks

If the base change of a morphism of algebraic stacks along a surjective, flat,
locally of finite presentation morphism is locally of finite presentation, then
the original morphism is locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

open AlgebraicGeometry.AlgebraicStack

/- Lemma 101.27.11: Let `f : X ⟶ Y` be a morphism of algebraic stacks. Let
`g : Z ⟶ Y` be a surjective, flat, locally of finite presentation morphism of
algebraic stacks. If the base change `TwoFibreProduct.snd f g` is locally of
finite presentation, then `f` is locally of finite presentation.

Stacks writes the base change as `Z ×_Y X ⟶ Z`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 06Q8]
#check (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.of_twoFibreProduct_snd :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [LocallyOfFinitePresentation (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)],
    LocallyOfFinitePresentation f)

#check (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.of_isBilimit_snd :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y}
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [LocallyOfFinitePresentation c.snd],
    LocallyOfFinitePresentation f)

#check (AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation.twoFibreProduct_snd_iff :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g],
    LocallyOfFinitePresentation (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) ↔
      LocallyOfFinitePresentation f)
