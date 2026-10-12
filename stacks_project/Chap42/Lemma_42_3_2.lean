/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Module.Multiplicity
import StacksCheckRecall

@[expose] public section

open scoped BigOperators

universe u v

namespace Module.CohenMacaulay

/- Lemma 42.3.2 (1): if a Cohen–Macaulay module `M` has support dimension one and
`M / xM` has support dimension zero, its quotient length is the sum of the lengths of
`R / (x, q)` weighted by the lengths of `M` localized at the minimal support primes. -/
@[stacks 02QG]
#check
  (Module.CohenMacaulay.length_quotSMulTop_eq_sum_minimalPrimes :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      (M : Type v) [AddCommGroup M] [Module R M] [Module.CohenMacaulay R M]
      (x : R) (hM : Module.supportDim R M = 1)
      (hMx : Module.supportDim R (QuotSMulTop x M) = 0) {t : ℕ}
      (q : Fin t → PrimeSpectrum R) (hq_injective : Function.Injective q)
      (hq_minimal : ∀ i, Minimal (· ∈ Module.support R M) (q i))
      (hq_complete : ∀ p, Minimal (· ∈ Module.support R M) p → ∃ i, q i = p),
      Module.length R (QuotSMulTop x M) =
        ∑ i, Module.length R (R ⧸ ((q i).asIdeal ⊔ Ideal.span {x})) *
          Module.length (Localization.AtPrime (q i).asIdeal)
            (LocalizedModule.AtPrime (q i).asIdeal M))

end Module.CohenMacaulay

namespace Ideal.Quotient

/- Lemma 42.3.2 (2): if `x` acts regularly on `R / I` and `R / I` has dimension one,
the length of `R / (x, I)` is the sum of the lengths of `R / (x, q)` weighted by the
lengths of `(R / I)` localized at the minimal primes over `I`. -/
@[stacks 02QG]
#check
  (Ideal.Quotient.length_sup_span_eq_sum_minimalPrimes :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      (I : Ideal R) (x : R) (hx : IsSMulRegular (R ⧸ I) x)
      (hdim : ringKrullDim (R ⧸ I) = 1) {n : ℕ}
      (q : Fin n → PrimeSpectrum R) (hq_injective : Function.Injective q)
      (hq_minimal : ∀ i, (q i).asIdeal ∈ I.minimalPrimes)
      (hq_complete : ∀ p : PrimeSpectrum R,
        p.asIdeal ∈ I.minimalPrimes → ∃ i, q i = p),
      Module.length R (R ⧸ (I ⊔ Ideal.span {x})) =
        ∑ i, Module.length R (R ⧸ ((q i).asIdeal ⊔ Ideal.span {x})) *
          Module.length (Localization.AtPrime (q i).asIdeal)
            (LocalizedModule.AtPrime (q i).asIdeal (R ⧸ I)))

end Ideal.Quotient
