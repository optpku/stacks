/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

@[expose] public section

/-!
# Locally Free Modules over Semilocal Rings

@stack 02M9

Freeness criteria for finite locally free modules over semilocal rings.
-/

universe u v

namespace Module

/-- Lemma 10.78.7 (2): a finite locally free module over a semilocal ring with connected
spectrum is free. -/
@[stacks 02M9 "connected-spectrum specialization"]
theorem free_of_semilocal_of_connected_spectrum
    {R : Type u} {M : Type v} [CommRing R] [Finite (MaximalSpectrum R)]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] [Module.Flat R M]
    [ConnectedSpace (PrimeSpectrum R)] : Module.Free R M := sorry

end Module
