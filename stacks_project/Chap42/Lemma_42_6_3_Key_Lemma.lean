module

public import ReasLib.RingTheory.LocalRing.TameSymbol.Reciprocity
import StacksCheckRecall

open scoped BigOperators

universe u v

/- Lemma 42.6.3 (Key Lemma): if `q : Fin t → PrimeSpectrum.HeightOne A` enumerates
exactly the height-one primes where either `f` or `g` is not a local unit, then the sum of
the corresponding local tame-symbol orders is zero. -/
@[stacks 0EAX] #check
  (TameSymbol.sum_orderAt_eq_zero :
    ∀ (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
      [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
      (hdim : ringKrullDim A = 2) (f g : Kˣ) {t : ℕ}
      (q : Fin t → PrimeSpectrum.HeightOne A) (hq_injective : Function.Injective q)
      (hq_complete : ∀ p, (¬ p.IsUnitAt K f ∨ ¬ p.IsUnitAt K g) ↔ ∃ i, q i = p),
      ∑ i, TameSymbol.orderAt A K hdim (q i) f g = 0)

/- Every complete exceptional-prime enumeration computes the global finsum. -/
#check
  (TameSymbol.sum_orderAt_eq_finsum :
    ∀ (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
      [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
      (hdim : ringKrullDim A = 2) (f g : Kˣ) {t : ℕ}
      (q : Fin t → PrimeSpectrum.HeightOne A) (hq_injective : Function.Injective q)
      (hq_complete : ∀ p, (¬ p.IsUnitAt K f ∨ ¬ p.IsUnitAt K g) ↔ ∃ i, q i = p),
      ∑ i, TameSymbol.orderAt A K hdim (q i) f g =
        ∑ᶠ p : PrimeSpectrum.HeightOne A, TameSymbol.orderAt A K hdim p f g)

/- The global finsum of all local tame-symbol orders vanishes. -/
#check
  (TameSymbol.finsum_orderAt_eq_zero :
    ∀ (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
      [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
      (hdim : ringKrullDim A = 2) (f g : Kˣ),
      ∑ᶠ p : PrimeSpectrum.HeightOne A, TameSymbol.orderAt A K hdim p f g = 0)

/- If both arguments are local units at a height-one prime, their local tame symbol is
`1`. -/
#check
  (TameSymbol.valueAt_eq_one_of_isUnitAt :
    ∀ (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsNoetherianRing A]
      [Field K] [Algebra A K] [IsFractionRing A K]
      (p : PrimeSpectrum.HeightOne A) (f g : Kˣ)
      (hf : p.IsUnitAt K f) (hg : p.IsUnitAt K g),
      TameSymbol.valueAt A K p f g = 1)
