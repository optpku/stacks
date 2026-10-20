/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.TameSymbol.Reciprocity
import StacksCheckRecall

open scoped BigOperators

universe u v

/- Lemma 42.68.46 (Key Lemma): if `q : Fin t → PrimeSpectrum.HeightOne A` enumerates
exactly the height-one primes where either `f` or `g` is not a local unit, then the sum of
the corresponding local tame-symbol orders is zero. -/
@[stacks 02QJ] #check
  (TameSymbol.sum_orderAt_eq_zero :
    ∀ (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
      [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
      (hdim : ringKrullDim A = 2) (f g : Kˣ) {t : ℕ}
      (q : Fin t → PrimeSpectrum.HeightOne A) (hq_injective : Function.Injective q)
      (hq_complete : ∀ p, (¬ p.IsUnitAt K f ∨ ¬ p.IsUnitAt K g) ↔ ∃ i, q i = p),
      ∑ i, TameSymbol.orderAt A K hdim (q i) f g = 0)

/- The global finsum of all local tame-symbol orders vanishes. -/
#check
  (TameSymbol.finsum_orderAt_eq_zero :
    ∀ (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
      [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
      (hdim : ringKrullDim A = 2) (f g : Kˣ),
      ∑ᶠ p : PrimeSpectrum.HeightOne A, TameSymbol.orderAt A K hdim p f g = 0)

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
