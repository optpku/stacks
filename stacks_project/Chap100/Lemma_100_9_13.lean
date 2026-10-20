/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.OpenImage
import StacksCheckRecall

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

/- Lemma 100.9.13: Let `X` be an algebraic stack. Let `U` be an algebraic space
and `p : U.toGroupoids ⟶ X` a surjective smooth morphism. For an open immersion
`i : V ⟶ U`, there exists an algebraic stack `Y`, an open immersion `Y ⟶ X`,
and a surjective smooth morphism `V.toGroupoids ⟶ Y` factoring the composite
`V ⟶ X`. -/
@[stacks 05UP] #check
  (AlgebraicGeometry.AlgebraicStack.exists_openSubstack_of_openImmersion :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {U V : AlgebraicSpace S}
    (p : U.toGroupoids ⟶ X) (i : V ⟶ U) [Groupoids.Hom.Smooth p]
    [Groupoids.Hom.Surjective p] [AlgebraicSpace.IsOpenImmersion i],
    ∃ (Y : GroupoidsOver S) (j : Y ⟶ X) (q : V.toGroupoids ⟶ Y),
      AlgebraicStack Y ∧ Groupoids.Hom.OpenImmersion j ∧
        Groupoids.Hom.Smooth q ∧ Groupoids.Hom.Surjective q ∧
          q ≫ j = AlgebraicSpace.toGroupoids.map i ≫ p)

