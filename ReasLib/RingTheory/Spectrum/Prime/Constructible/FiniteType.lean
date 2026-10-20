/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Constructible images of finite-type spectrum maps

Over a Noetherian source, a finite-type ring homomorphism is finitely presented.  This leaf
packages that conversion at the level of constructible images, so callers can use the natural
finite-type hypothesis without rebuilding the finite-presentation bridge.

@stack 00GE
-/

@[expose] public section

universe u v

namespace RingHom.FiniteType

/-- A finite-type map out of a Noetherian ring sends constructible subsets of the target spectrum
to constructible subsets of the source spectrum. -/
@[stacks 00GE "constructible image under a finite-type map"]
theorem isConstructible_comap_image
    {R : Type u} {S : Type v} [CommRing R] [IsNoetherianRing R] [CommRing S]
    {f : R →+* S} (hf : f.FiniteType) {E : Set (PrimeSpectrum S)}
    (hE : Topology.IsConstructible E) :
    Topology.IsConstructible (PrimeSpectrum.comap f '' E) := sorry

end RingHom.FiniteType
