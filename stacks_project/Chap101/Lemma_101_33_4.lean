module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth.Descent
import StacksCheckRecall

/-!
# Descent of smoothness for morphisms of algebraic stacks

If the base change of a morphism of algebraic stacks along a surjective, flat,
locally of finite presentation morphism is smooth, then the original morphism
is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

open AlgebraicGeometry.AlgebraicStack

/- Lemma 101.33.4: Smoothness descends along a surjective, flat, locally
finitely presented morphism of algebraic stacks. The projection
`TwoFibreProduct.snd f g` is the base change of `f` to `Z`. -/
@[stacks 0DN7] #check (AlgebraicGeometry.AlgebraicStack.Smooth.of_twoFibreProduct_snd :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [Smooth (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)], Smooth f)

#check (AlgebraicGeometry.AlgebraicStack.Smooth.of_isBilimit_snd :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y}
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [Smooth c.snd], Smooth f)

#check (AlgebraicGeometry.AlgebraicStack.Smooth.twoFibreProduct_snd_iff :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g],
    Smooth (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) ↔ Smooth f)
