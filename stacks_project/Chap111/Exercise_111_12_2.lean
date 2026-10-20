/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Depth.EmbeddedPointCylinder
public import ReasLib.RingTheory.Ideal.MinimalPrime.Depth
import StacksCheckRecall

@[expose] public section

universe u

open scoped ENat

/- Exercise 111.12.2 (1): a Noetherian local ring of positive depth is given by the
embedded-point cylinder at its origin. -/
@[stacks 0CS2] #check
  (MvPolynomial.LineWithEmbeddedPointCylinder.moduleDepth_ge_one :
    ∀ (k : Type u) [Field k],
      (1 : ℕ∞) ≤
        moduleDepth
          (MvPolynomial.LineWithEmbeddedPointCylinder.LocalRing k)
          (MvPolynomial.LineWithEmbeddedPointCylinder.LocalRing k))

/- Exercise 111.12.2 (2): the localization at the embedded prime has module depth zero. -/
@[stacks 0CS2] #check
  (MvPolynomial.LineWithEmbeddedPointCylinder.moduleDepth_atPrime_eq_zero :
    ∀ (k : Type u) [Field k],
      moduleDepth
          (Localization.AtPrime
            (MvPolynomial.LineWithEmbeddedPointCylinder.embeddedPrime k))
          (Localization.AtPrime
            (MvPolynomial.LineWithEmbeddedPointCylinder.embeddedPrime k)) = 0)

/- Exercise 111.12.2 (3): the localization at the embedded prime has positive Krull
dimension. -/
@[stacks 0CS2] #check
  (MvPolynomial.LineWithEmbeddedPointCylinder.ringKrullDim_atPrime_ge_one :
    ∀ (k : Type u) [Field k],
      1 ≤ ringKrullDim
        (Localization.AtPrime
          (MvPolynomial.LineWithEmbeddedPointCylinder.embeddedPrime k)))

/- Exercise 111.12.2 (4): localizing a Noetherian ring at a minimal prime gives module
depth zero. -/
@[stacks 0CS2] #check
  (IsMinimalPrime.moduleDepth_atPrime_eq_zero :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
      {p : Ideal R} [p.IsPrime] (hp : p ∈ minimalPrimes R),
      moduleDepth (Localization.AtPrime p) (Localization.AtPrime p) = 0)

/- Exercise 111.12.2 (5): localizing a Noetherian ring at a minimal prime gives Krull
dimension zero. -/
@[stacks 0CS2] #check
  (IsMinimalPrime.ringKrullDim_atPrime_eq_zero :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
      {p : Ideal R} [p.IsPrime] (hp : p ∈ minimalPrimes R),
      ringKrullDim (Localization.AtPrime p) = 0)
