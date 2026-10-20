/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pullback.Subset
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits MonoidalCategory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.24.2: for morphisms of schemes over a field `k`, the pullback subset determined by
the closures of the two set-theoretic images equals the closure of the image of the induced
product morphism. -/
@[stacks 04Q0] #check
  (AlgebraicGeometry.Scheme.Pullback.subset_closure_range_eq_closure_range_tensor :
    ∀ {k : Type u} [Field k]
      {A X B Y : Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
      (f : A ⟶ X) (g : B ⟶ Y),
      AlgebraicGeometry.Scheme.Pullback.subset X.hom Y.hom
          (closure (Set.range f.left.base))
          (closure (Set.range g.left.base)) =
        (closure (Set.range ((f ⊗ₘ g).left.base)) :
          Set (pullback X.hom Y.hom : AlgebraicGeometry.Scheme)))
