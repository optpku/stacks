/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Stagewise exactness of adic completion

This leaf records the map-level criteria for the canonical module completion
`AdicCompletion I`.  They only use the ideal-power quotient system, so no
Noetherian or finiteness hypotheses are imposed.
-/

@[expose] public section

universe u v w x

namespace AdicCompletion

variable {R : Type u} [CommRing R]
variable {K : Type v} [AddCommGroup K] [Module R K]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type x} [AddCommGroup N] [Module R N]

/-- Surjectivity of a map of `I`-adic completions is detected by its first quotient stage. -/
@[stacks 0315 "completion-map surjectivity from the first quotient stage"]
theorem map_surjective_of_reduceModIdeal_surjective
    (I : Ideal R) (f : M →ₗ[R] N)
    (hf : Function.Surjective (f.reduceModIdeal I)) :
    Function.Surjective (map I f) := sorry

/-- A map of `I`-adic completions is injective when all of its ideal-power quotient-stage maps
are injective. -/
@[stacks 0315 "completion-map injectivity from all quotient stages"]
theorem map_injective_of_reduceModIdeal_injective
    (I : Ideal R) (f : K →ₗ[R] M)
    (hf : ∀ n : ℕ, Function.Injective (f.reduceModIdeal (I ^ n))) :
    Function.Injective (map I f) := sorry

/-- Exactness and injectivity at every ideal-power quotient stage lift to exactness after
`I`-adic completion. -/
@[stacks 0315 "completion exactness from quotient-stage exactness"]
theorem map_exact_of_stagewise_exact_of_injective
    (I : Ideal R) {f : K →ₗ[R] M} {g : M →ₗ[R] N}
    (hexact : ∀ n : ℕ,
      Function.Exact (f.reduceModIdeal (I ^ n)) (g.reduceModIdeal (I ^ n)))
    (hinjective : ∀ n : ℕ, Function.Injective (f.reduceModIdeal (I ^ n))) :
    Function.Exact (map I f) (map I g) := sorry

end AdicCompletion
