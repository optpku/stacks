/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_8_1_Mono
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

/-!
# Base change of monomorphisms of algebraic stacks

Monomorphisms of algebraic stacks are stable under arbitrary 2-fibre-product
base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace Mono

/-- Lemma 100.8.2: if `f : X ⟶ Y` is a morphism of algebraic stacks and
`g : Z ⟶ Y` is a monomorphism, then the 2-fibre-product projection
`TwoFibreProduct.snd g f : Z ×_Y X ⟶ X` is a monomorphism. -/
@[stacks 04ZX, instance]
instance pullback_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Mono g] :
    Mono (TwoFibreProduct.snd.{u + 1, u, u + 1, u} g f) :=
  sorry

end Mono

end AlgebraicGeometry.Groupoids.Hom
