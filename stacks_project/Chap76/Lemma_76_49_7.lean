/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection.BaseLocus
import StacksCheckRecall

/-!
# Where a morphism of algebraic spaces is a local complete intersection

In a commutative triangle of algebraic spaces `X ⟶ Y` over `Z` with
`X ⟶ Z` flat, locally of finite presentation, and closed, and `Y ⟶ Z`
flat and locally of finite presentation, a test map into `Z` factors
through the local complete intersection base locus if and only if the
base-changed map `X_{Z'} ⟶ Y_{Z'}` is a local complete intersection.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

/- Lemma 76.49.7: Consider a commutative triangle of algebraic spaces over `S`
given by `f : X ⟶ Y` and `q : Y ⟶ Z`. Assume that `p = f ≫ q` is flat,
locally of finite presentation, and closed, and that `q` is flat and locally
of finite presentation. Then a morphism `g : Z' ⟶ Z` factors through the
open subspace `W = baseLocus f q ⊂ Z` if and only if the base change
`f_{Z'} = overBaseChange f q g : X_{Z'} ⟶ Y_{Z'}` is a local complete
intersection morphism. -/
@[stacks 06CE] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection.exists_lift_iff_overBaseChange :
    ∀ {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [Flat (f ≫ q)] [LocallyOfFinitePresentation (f ≫ q)]
    [Closed (f ≫ q)] [Flat q] [LocallyOfFinitePresentation q],
    (∃ ℓ : Z' ⟶
      (AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection.baseLocus f q).X,
      ℓ ≫ (AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection.baseLocus f q).ι = g) ↔
      IsLocalCompleteIntersection (overBaseChange f q g))

