/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Isomorphism.BaseLocus
import StacksCheckRecall

/-!
# Where a morphism of algebraic spaces is an isomorphism

In a commutative triangle of algebraic spaces `X ⟶ Y` over `Z` with
`X ⟶ Z` locally of finite presentation, flat, and universally closed, and
`Y ⟶ Z` locally of finite type, closed, and separated, a test map into `Z`
factors through the isomorphism base locus if and only if the base-changed
map `X_{Z'} ⟶ Y_{Z'}` is an isomorphism.
-/

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Isomorphism

/- Lemma 76.49.6: A morphism to the base factors through the isomorphism
base locus exactly when the canonical base-changed morphism is an isomorphism. -/
@[stacks 05XD] #check (AlgebraicGeometry.AlgebraicSpace.Isomorphism.exists_lift_iff_overBaseChange :
    ∀ {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [LocallyOfFiniteType q]
    [Closed q] [Separated q],
    (∃ ℓ : Z' ⟶ (baseLocus f q).X, ℓ ≫ (baseLocus f q).ι = g) ↔
      IsIso (overBaseChange f q g))

end AlgebraicGeometry.AlgebraicSpace.Isomorphism
