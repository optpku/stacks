module

import ReasLib.AlgebraicGeometry.AlgebraicStack.Monomorphism
import StacksCheckRecall

/-!
# Base change of monomorphisms of algebraic stacks

Monomorphisms of algebraic stacks are stable under arbitrary 2-fibre-product
base change.
-/

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 100.8.2: if `f : X ⟶ Y` is a morphism of algebraic stacks and
`g : Z ⟶ Y` is a monomorphism, then the 2-fibre-product projection
`TwoFibreProduct.snd g f : Z ×_Y X ⟶ X` is a monomorphism. -/
@[stacks 04ZX] #check (AlgebraicGeometry.Groupoids.Hom.Mono.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicGeometry.Groupoids.Hom.Mono g],
    AlgebraicGeometry.Groupoids.Hom.Mono
      (TwoFibreProduct.snd.{u + 1, u, u + 1, u} g f))
