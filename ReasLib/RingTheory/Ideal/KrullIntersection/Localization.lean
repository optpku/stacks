/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Support
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of Krull intersections

This file isolates two forms of the local vanishing of an adic intersection.  The first is the
prime-local algebraic statement; the second descends that vanishing to a principal open
neighborhood.  Both use Mathlib's existing ideal-power and localized-submodule representations.
@stack 00IQ
@stack 00IR
-/

@[expose] public section

universe u v

open scoped Pointwise

namespace Ideal

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- If `I` is contained in a prime `p`, then the localization at `p` of the `I`-adic
intersection of a finite module over a Noetherian ring is zero. -/
@[stacks 00IQ "prime-local vanishing of a Krull intersection"]
theorem iInf_pow_smul_localized_eq_bot_of_le
    (I p : Ideal R) [p.IsPrime] (hp : I ≤ p) :
    (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M)).localized p.primeCompl = ⊥ := sorry

/-- If `I` is contained in a prime `p`, the `I`-adic intersection of a finite module vanishes
after localization on some principal open neighborhood of `p`. -/
@[stacks 00IQ "principal-open vanishing of a Krull intersection"]
theorem exists_notMem_iInf_pow_smul_localized_eq_bot
    (I p : Ideal R) [p.IsPrime] (hp : I ≤ p) :
    ∃ f ∉ p,
      (⨅ n : ℕ, I ^ n • (⊤ : Submodule R M)).localized (Submonoid.powers f) = ⊥ := sorry

/-- Remark 10.51.6: if an element belongs to every power of an ideal contained in a prime, then
it vanishes after localization on some principal open neighborhood of that prime. -/
@[stacks 00IR "principal-open vanishing of an element in an adic intersection"]
theorem exists_notMem_and_algebraMap_eq_zero_of_mem_iInf_pow
    (I p : Ideal R) [p.IsPrime] (hp : I ≤ p) (x : R)
    (hx : x ∈ ⨅ n : ℕ, (I ^ n : Ideal R)) :
    ∃ f ∉ p, algebraMap R (Localization.Away f) x = 0 := sorry

end Ideal
