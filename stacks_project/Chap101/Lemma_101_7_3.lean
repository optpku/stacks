module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact.BaseChange
import StacksCheckRecall

/-!
# Base change of quasi-compact morphisms of algebraic stacks

The base change of a quasi-compact morphism of algebraic stacks by any
morphism of algebraic stacks is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

/- Lemma 101.7.3: The base change of a quasi-compact morphism of algebraic
stacks by any morphism of algebraic stacks is quasi-compact. -/
@[stacks 050V] #check
  (AlgebraicGeometry.AlgebraicStack.QuasiCompact.twoFibreProduct_snd :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Z ⟶ Y)
      [AlgebraicGeometry.AlgebraicStack.QuasiCompact f]
      [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
      AlgebraicGeometry.AlgebraicStack.QuasiCompact
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))
