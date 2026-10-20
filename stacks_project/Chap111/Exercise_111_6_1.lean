/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.RingTheory.Spectrum.Prime.Integers
import StacksCheckRecall

/- Exercise 111.6.1 (1): as a set, `PrimeSpectrum ℤ` consists of the generic point `⊥`
corresponding to the zero ideal, together with the points whose ideals are
`Ideal.span {(p : ℤ)}` for a prime number `p`. -/
@[stacks 02CY]
#check (PrimeSpectrum.eq_bot_or_span_natPrime :
  ∀ x : PrimeSpectrum ℤ,
    x = ⊥ ∨ ∃ p : ℕ, Nat.Prime p ∧ x.asIdeal = Ideal.span {(p : ℤ)})

/- Exercise 111.6.1 (2): a subset of `PrimeSpectrum ℤ` is Zariski closed if and only if it is
the whole space or a finite set of closed points. -/
@[stacks 02CY]
#check (PrimeSpectrum.isClosed_int_iff :
  ∀ {s : Set (PrimeSpectrum ℤ)},
    IsClosed s ↔ s = Set.univ ∨ s.Finite ∧ s ⊆ closedPoints (PrimeSpectrum ℤ))

/- Companion: prime ideals of `ℤ` are `⊥` or `Ideal.span {(p : ℤ)}` for `Nat.Prime p`. -/
#check @Ideal.isPrime_int_iff

/- Companion: a singleton in `PrimeSpectrum` is closed iff the prime is maximal. -/
#check @PrimeSpectrum.isClosed_singleton_iff_isMaximal

/- Companion: `x ∈ closedPoints X` iff `IsClosed {x}`. -/
#check mem_closedPoints_iff
