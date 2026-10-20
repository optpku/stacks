/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.DirectLimit
import StacksCheckRecall

@[expose] public section

universe u v

/- Exercise 111.2.4: for a directed system of commutative rings `(A i, φ)` with
colimit `Ring.DirectLimit A (φ · · ·)`, there is a bijection
`PrimeSpectrum (Ring.DirectLimit A (φ · · ·)) ≃ inverseLimit A φ`, where
`inverseLimit A φ` is the subset of `∀ i, PrimeSpectrum (A i)` consisting of
families `p` with `p i = comap (φ i j hij) (p j)` whenever `i ≤ j`. This
subset is the inverse limit of the sets `PrimeSpectrum (A i)`. -/
@[stacks 078L]
#check (PrimeSpectrum.directLimitEquiv :
  ∀ {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (A : ι → Type v) [∀ i, CommRing (A i)]
    (φ : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (φ · · ·)],
    PrimeSpectrum (Ring.DirectLimit A (φ · · ·)) ≃
      PrimeSpectrum.inverseLimit A φ)
