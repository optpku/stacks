/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifting maps from finitely presented modules to flat modules

This leaf characterizes flatness by the lifting property of maps from
finitely presented modules along surjective linear maps.

@stack 058F
-/

@[expose] public section

universe u v w x

namespace Module.Flat

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.81.3: `M` is flat exactly when maps from finitely presented
modules to `M` lift along every surjective linear map onto `M`. -/
@[stacks 058F]
theorem iff_postcomp_surjective_finitePresentation :
    Module.Flat R M ↔
      ∀ {P : Type w} [AddCommGroup P] [Module R P]
        [Module.FinitePresentation R P]
        {N : Type x} [AddCommGroup N] [Module R N]
        (π : N →ₗ[R] M), Function.Surjective π →
          Function.Surjective (fun f : P →ₗ[R] N ↦ π.comp f) := sorry

end Module.Flat
