/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Rigidified.PushforwardLine

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 44.6.2: for a smooth projective curve `X` over a field with section `σ`, the
subfunctor of rigidified Picard classes whose derived pushforward is a rank-one vector bundle in
degree `0` has inclusion representable by open immersions. -/
@[stacks 0B9V] #check
  (AlgebraicGeometry.RigidifiedPicard.pushforwardLineSubfunctor_isOpen :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
      [Smooth X.hom] [Projective X.hom]
      (σ : Spec (CommRingCat.of k) ⟶ X.left) (hσ : σ ≫ X.hom = 𝟙 _),
      (MorphismProperty.over (@IsOpenImmersion)).relative uliftYoneda.{u + 1}
        (AlgebraicGeometry.RigidifiedPicard.pushforwardLineSubfunctor X σ hσ).ι)
