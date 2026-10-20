/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap47.Definition_47_4_1
import StacksCheckRecall

@[expose] public section

universe u v w x

/- Lemma 47.4.2: Any two projective covers of an `R`-module `M` are linearly
isomorphic by an isomorphism compatible with their maps to `M`. -/
@[stacks 08XZ] #check
  (LinearMap.IsProjectiveCover.exists_linearEquiv :
    ∀ {R : Type u} [Ring R]
      {P : Type v} [AddCommGroup P] [Module R P]
      {P' : Type w} [AddCommGroup P'] [Module R P']
      {M : Type x} [AddCommGroup M] [Module R M]
      {f : P →ₗ[R] M} {g : P' →ₗ[R] M},
      f.IsProjectiveCover → g.IsProjectiveCover →
        ∃ e : P ≃ₗ[R] P', g.comp e.toLinearMap = f)
