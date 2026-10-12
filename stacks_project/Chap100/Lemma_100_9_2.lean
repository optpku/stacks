/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

/-!
# Base change of immersions of algebraic stacks

Closed immersions and open immersions of algebraic stacks are stable under
arbitrary 2-fibre-product base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace ClosedImmersion

/-- Lemma 100.9.2 (1): if `f : X ⟶ Y` is a morphism of algebraic stacks and
`i : Z ⟶ Y` is a closed immersion, then the 2-fibre-product projection
`TwoFibreProduct.snd i f : Z ×_Y X ⟶ X` is a closed immersion. -/
@[stacks 0501]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (i : Z ⟶ Y) [ClosedImmersion i] :
    ClosedImmersion (TwoFibreProduct.snd.{u + 1, u, u + 1, u} i f) :=
  sorry

end ClosedImmersion

namespace OpenImmersion

/-- Lemma 100.9.2 (2): if `f : X ⟶ Y` is a morphism of algebraic stacks and
`i : Z ⟶ Y` is an open immersion, then the 2-fibre-product projection
`TwoFibreProduct.snd i f : Z ×_Y X ⟶ X` is an open immersion. -/
@[stacks 0501]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (i : Z ⟶ Y) [OpenImmersion i] :
    OpenImmersion (TwoFibreProduct.snd.{u + 1, u, u + 1, u} i f) :=
  sorry

end OpenImmersion

end AlgebraicGeometry.Groupoids.Hom
