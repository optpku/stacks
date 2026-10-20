/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.TameSymbol.HeightOne
import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Localization.Multiplicity

/-!
# Reciprocity for tame symbols at height-one primes

This file relates the global finitely supported sum of local tame-symbol orders to finite
enumerations of the exceptional height-one primes.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe u v

namespace TameSymbol

/-- The sum of the local tame-symbol orders over all height-one primes of a two-dimensional
Noetherian local domain vanishes. -/
theorem finsum_orderAt_eq_zero
    (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hdim : ringKrullDim A = 2) (f g : Kˣ) :
    ∑ᶠ p : PrimeSpectrum.HeightOne A, orderAt A K hdim p f g = 0 := sorry

/-- An injective finite enumeration of exactly the primes where one argument is not a local
unit computes the global sum of local tame-symbol orders. -/
theorem sum_orderAt_eq_finsum
    (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hdim : ringKrullDim A = 2) (f g : Kˣ) {t : ℕ}
    (q : Fin t → PrimeSpectrum.HeightOne A) (hq_injective : Function.Injective q)
    (hq_complete : ∀ p, (¬ p.IsUnitAt K f ∨ ¬ p.IsUnitAt K g) ↔ ∃ i, q i = p) :
    ∑ i, orderAt A K hdim (q i) f g =
      ∑ᶠ p : PrimeSpectrum.HeightOne A, orderAt A K hdim p f g := sorry

/-- If an injective finite enumeration contains exactly the primes where one argument is not
a local unit, then the sum of the corresponding local tame-symbol orders is zero. -/
theorem sum_orderAt_eq_zero
    (A : Type u) (K : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hdim : ringKrullDim A = 2) (f g : Kˣ) {t : ℕ}
    (q : Fin t → PrimeSpectrum.HeightOne A) (hq_injective : Function.Injective q)
    (hq_complete : ∀ p, (¬ p.IsUnitAt K f ∨ ¬ p.IsUnitAt K g) ↔ ∃ i, q i = p) :
    ∑ i, orderAt A K hdim (q i) f g = 0 := sorry

end TameSymbol
