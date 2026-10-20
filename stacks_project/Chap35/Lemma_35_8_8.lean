/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.FullyFaithful
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 35.8.8 (1): the associated-module functor from quasi-coherent modules on a
scheme to quasi-coherent modules on any of its five big standard sites is fully faithful. -/
@[stacks 0GN7] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.bigFunctor.fullyFaithful :
    ∀ (τ : StandardTopology) (S : Scheme.{u}),
      Nonempty (AlgebraicGeometry.Scheme.AssociatedModule.bigFunctor τ S).FullyFaithful)

/- Lemma 35.8.8 (2): the associated-module functor from quasi-coherent modules on a
scheme to quasi-coherent modules on its small Zariski or small étale site is fully faithful. -/
@[stacks 0GN7] #check
  (AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor.fullyFaithful :
    ∀ (σ : SmallStandardTopology) (S : Scheme.{u}),
      Nonempty (AlgebraicGeometry.Scheme.AssociatedModule.smallFunctor σ S).FullyFaithful)
