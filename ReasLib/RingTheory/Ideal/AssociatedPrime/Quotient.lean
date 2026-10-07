module

public import Mathlib.RingTheory.Spectrum.Prime.Defs
public import Mathlib.RingTheory.QuotSMulTop
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Exact associated primes under quotient maps
-/

universe u v

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module (R ⧸ I) M] [Module R M]
variable [IsScalarTower R (R ⧸ I) M]

namespace associatedPrimesOfModule.Quotient

/-- Exact associated primes of a quotient-ring module, contracted to the base ring, are exactly
its exact associated primes after restriction of scalars. -/
@[stacks 05BY]
theorem image_comap_eq :
    Ideal.comap (Ideal.Quotient.mk I) '' associatedPrimesOfModule (R ⧸ I) M =
      associatedPrimesOfModule R M := sorry

end associatedPrimesOfModule.Quotient

/-- Exact associated primes of a quotient-ring module, contracted to the base ring, are exactly
its exact associated primes after restriction of scalars. -/
@[deprecated associatedPrimesOfModule.Quotient.image_comap_eq (since := "2026-08-07")]
theorem associatedPrimesOfModule_quotient_image_comap_eq :
    Ideal.comap (Ideal.Quotient.mk I) '' associatedPrimesOfModule (R ⧸ I) M =
      associatedPrimesOfModule R M := sorry

end

section PrimeQuotient

variable {R : Type u} [CommRing R]

namespace associatedPrimesOfModule

/-- The exact associated-prime set of a quotient by a prime ideal is the singleton containing
that prime. -/
theorem quotient_prime_eq_singleton (p : PrimeSpectrum R) :
    associatedPrimesOfModule R (R ⧸ p.asIdeal) = {p.asIdeal} := by
  ext q
  constructor
  · intro hq
    change Ideal.IsAssociatedToModule R (R ⧸ p.asIdeal) q at hq
    rcases hq with ⟨hqPrime, x, hx⟩
    rw [Set.mem_singleton_iff]
    apply le_antisymm
    · intro r hr
      have hrx : r • x = 0 := by
        exact (Ideal.mem_torsionOf_iff x r).mp (hx ▸ hr)
      have hx_ne : x ≠ 0 := by
        intro hx_zero
        have htop : q = ⊤ := by rw [hx, hx_zero, Ideal.torsionOf_zero]
        exact hqPrime.ne_top htop
      have hmul : Ideal.Quotient.mk p.asIdeal r * x = 0 := by
        simpa [Algebra.smul_def] using hrx
      exact Ideal.Quotient.eq_zero_iff_mem.mp
        ((mul_eq_zero.mp hmul).resolve_right hx_ne)
    · intro r hr
      rw [hx, Ideal.mem_torsionOf_iff, Algebra.smul_def]
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    change Ideal.IsAssociatedToModule R (R ⧸ p.asIdeal) p.asIdeal
    refine ⟨p.isPrime, 1, ?_⟩
    ext r
    rw [Ideal.mem_torsionOf_iff, Algebra.smul_def]
    simp [Ideal.Quotient.eq_zero_iff_mem]

end associatedPrimesOfModule

end PrimeQuotient

namespace associatedPrimes

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- If `p` is associated to `M` and `q` is minimal over `p ⊔ Ideal.span {x}`, then `q` is
associated to `M / x ^ n M` for some positive `n`. -/
@[stacks 0CN5]
theorem exists_quotSMulTop_pow_of_mem_minimalPrimes_sup
    (x : R) (p q : Ideal R) (hp : p ∈ associatedPrimes R M)
    (hq : q ∈ (p ⊔ Ideal.span {x}).minimalPrimes) :
    ∃ n : ℕ, 0 < n ∧ q ∈ associatedPrimes R (QuotSMulTop (x ^ n) M) := sorry

end associatedPrimes
