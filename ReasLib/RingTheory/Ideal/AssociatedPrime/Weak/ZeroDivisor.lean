/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Weakly associated primes and zero divisors

This leaf owns the zero-divisor characterization for weakly associated primes.
Unlike the exact-associated-prime analogue, it does not require the base ring
to be Noetherian.
-/

@[expose] public section

universe u v

namespace weaklyAssociatedPrimes

variable {R : Type u} {M : Type v}
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- The union of the weakly associated primes of `M` is exactly the set of elements of `R` that
annihilate a nonzero element of `M`. -/
@[stacks 05C3]
theorem biUnion_eq_zero_divisors :
    ⋃ 𝔮 ∈ weaklyAssociatedPrimes R M, 𝔮 =
      {f : R | ∃ m : M, m ≠ 0 ∧ f • m = 0} := by
  ext f
  constructor
  · simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    rintro ⟨𝔮, ⟨h𝔮, hf⟩⟩
    obtain ⟨m, hm⟩ := h𝔮
    obtain ⟨y, hy, hfy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hm hf
    refine ⟨y • m, ?_, ?_⟩
    · exact fun hym ↦ hy ((Ideal.mem_torsionOf_iff m y).mpr hym)
    · rw [smul_smul]
      exact (Ideal.mem_torsionOf_iff m (f * y)).mp hfy
  · rintro ⟨m, hm, hfm⟩
    let I := Ideal.torsionOf R M m
    have hI : I ≠ ⊤ := by
      simpa [I, Ideal.torsionOf_eq_top_iff] using hm
    let 𝔮 : I.minimalPrimes := Classical.choice (Ideal.nonempty_minimalPrimes hI)
    exact Set.mem_iUnion₂_of_mem (show (𝔮 : Ideal R) ∈ weaklyAssociatedPrimes R M from
      ⟨m, 𝔮.2⟩) (𝔮.2.1.2 ((Ideal.mem_torsionOf_iff m f).mpr hfm))

end weaklyAssociatedPrimes
