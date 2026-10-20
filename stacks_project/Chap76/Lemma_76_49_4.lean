/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseLocus
import StacksCheckRecall

/-!
# Where a morphism of algebraic spaces is flat

In a commutative triangle of algebraic spaces `X ⟶ Y` over `Z` with
`X ⟶ Z` locally of finite presentation, flat, and closed, and `Y ⟶ Z`
locally of finite type, a test map into `Z` factors through the flat
base locus if and only if the base-changed map `X_{Z'} ⟶ Y_{Z'}` is
flat.
-/

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flat

/- Lemma 76.49.4: Consider a commutative triangle of algebraic spaces over `S`
given by `f : X ⟶ Y` and `q : Y ⟶ Z`. Assume that `p = f ≫ q` is locally of
finite presentation, flat, and closed, and that `q` is locally of finite type.
Then a morphism `g : Z' ⟶ Z` factors through the open subspace
`baseLocus f q ⊂ Z` if and only if the base change
`overBaseChange f q g : X_{Z'} ⟶ Y_{Z'}` is flat. -/
@[stacks 05XB] #check
  (AlgebraicGeometry.AlgebraicSpace.Flat.exists_lift_iff_overBaseChange :
    ∀ {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
      (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
      [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)]
      [Closed (f ≫ q)] [LocallyOfFiniteType q],
      (∃ ℓ : Z' ⟶ (baseLocus f q).X, ℓ ≫ (baseLocus f q).ι = g) ↔
        Flat (overBaseChange f q g))

end AlgebraicGeometry.AlgebraicSpace.Flat
