/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Resolution.Localization

@[expose] public section

universe u v w

/- Lemma 16.9.3: a resolution of the base-localized map at a minimal prime
descends to a finitely presented factorization whose singular ideal avoids
the original prime.  Minimality belongs to the source setup; the descent
owner is valid for every target prime. -/
@[stacks 07F9] #check
  fun {R : Type u} {A : Type v} {Λ : Type w}
    [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ]
    [IsNoetherianRing R] [Algebra.FinitePresentation R A]
    (φ : A →ₐ[R] Λ) (q : PrimeSpectrum Λ)
    (_hq : q.asIdeal ∈ φ.singularIdealIn.minimalPrimes)
    (hlocal : φ.LocallyResolvableAt q) ↦
      AlgHom.Factorisation.Finite.SmoothAt.nonempty_of_localization
        φ q hlocal

#check @AlgHom.localizeBaseAt
#check @AlgHom.LocallyResolvableAt
#check @AlgHom.Factorisation.Finite.Avoids
#check @AlgHom.Factorisation.Finite.Avoids.of
#check @AlgHom.Factorisation.Finite.Avoids.spec
#check @AlgHom.Factorisation.Finite.SmoothAt
#check @AlgHom.Factorisation.Finite.SmoothAt.of
#check @AlgHom.Factorisation.Finite.SmoothAt.spec
#check @AlgHom.Factorisation.Finite.SmoothAt.nonempty_of_localization
#check @AlgHom.Factorisation.Finite.SmoothAt.toAvoids
#check @AlgHom.ResolutionAtPrime.toSmoothAt
