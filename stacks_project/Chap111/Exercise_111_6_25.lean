/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.ZeroLocus
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.6.25: for ideals `I` and `J` of a commutative ring `A`, the closed sets
`V(I)` and `V(J)` in `PrimeSpectrum A` are disjoint if and only if `I ⊔ J = ⊤`. -/
@[stacks 02DF] #check (PrimeSpectrum.disjoint_zeroLocus_iff :
  ∀ {A : Type u} [CommRing A] (I J : Ideal A),
    Disjoint (PrimeSpectrum.zeroLocus (I : Set A))
      (PrimeSpectrum.zeroLocus (J : Set A)) ↔ I ⊔ J = ⊤)
