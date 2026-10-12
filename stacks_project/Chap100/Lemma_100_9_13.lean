/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Lemma_100_9_13_OpenImage

/-!
# Open image of an open in a smooth atlas

A surjective smooth atlas of an algebraic stack, restricted to an open
immersion of algebraic spaces, factors through a canonical open substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 100.9.13: Let `X` be an algebraic stack. Let `U` be an algebraic space
and `p : U.toGroupoids ⟶ X` a surjective smooth morphism. For an open immersion
`i : V ⟶ U`, there exists an algebraic stack `Y`, an open immersion `Y ⟶ X`,
and a surjective smooth morphism `V.toGroupoids ⟶ Y`. The canonical such
substack is `openImage p i`, with atlas `openImageHom p i`. -/
@[stacks 05UP]
theorem exists_openSubstack_of_openImmersion {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {U V : AlgebraicSpace S}
    (p : U.toGroupoids ⟶ X) (i : V ⟶ U) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [AlgebraicSpace.IsOpenImmersion i] :
    Groupoids.Hom.Smooth (openImageHom p i) ∧
      Groupoids.Hom.Surjective (openImageHom p i) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
