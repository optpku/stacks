/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.SurjectiveFlat.BaseLocus
import StacksCheckRecall

/-!
# Where a morphism of algebraic spaces is surjective and flat

In a commutative triangle of algebraic spaces `X ⟶ Y` over `Z` with
`X ⟶ Z` locally of finite presentation, flat, and closed, and `Y ⟶ Z`
locally of finite type and closed, a test map into `Z` factors through
the surjective-and-flat base locus if and only if the base-changed map
`X_{Z'} ⟶ Y_{Z'}` is surjective and flat.
-/

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SurjectiveFlat

/- Lemma 76.49.5: A morphism to the base factors through the surjective-and-flat
base locus exactly when the canonical base-changed morphism is surjective
and flat. -/
@[stacks 05XC] #check (AlgebraicGeometry.AlgebraicSpace.SurjectiveFlat.exists_lift_iff_overBaseChange :
    ∀ {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)]
    [Closed (f ≫ q)] [LocallyOfFiniteType q] [Closed q],
    (∃ ℓ : Z' ⟶ (baseLocus f q).X, ℓ ≫ (baseLocus f q).ι = g) ↔
      Surjective (overBaseChange f q g) ∧ Flat (overBaseChange f q g))

end AlgebraicGeometry.AlgebraicSpace.SurjectiveFlat
