module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite.BaseChange
import StacksCheckRecall

/-!
# Base change of locally quasi-finite morphisms of algebraic stacks

A base change of a locally quasi-finite morphism of algebraic stacks is
locally quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

/- Lemma 101.23.3: A base change of a locally quasi-finite morphism is
locally quasi-finite.

Stacks writes the base change as `Y' ×_Y X ⟶ Y'`; the Lean projection is
`TwoFibreProduct.snd f g` of a locally quasi-finite morphism `f : X ⟶ Y`
along a test morphism `g : Z ⟶ Y`. -/
@[stacks 06UB] #check
  (AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite.twoFibreProduct_snd :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicStack.LocallyQuasiFinite f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
    AlgebraicStack.LocallyQuasiFinite
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

#check (AlgebraicGeometry.AlgebraicStack.discreteFieldFibers.of_isBilimit :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} (hf : AlgebraicStack.discreteFieldFibers f)
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit),
    AlgebraicStack.discreteFieldFibers c.snd)

#check (AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite.of_isBilimit :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [AlgebraicStack.LocallyQuasiFinite f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit),
    AlgebraicStack.LocallyQuasiFinite c.snd)

#check (AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite.twoFibreProduct_fst :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicStack.LocallyQuasiFinite g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
    AlgebraicStack.LocallyQuasiFinite
      (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g))
