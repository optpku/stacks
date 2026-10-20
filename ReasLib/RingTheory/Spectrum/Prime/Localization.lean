/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.RingTheory.Spectrum.Prime.Irreducible
public import ReasLib.RingTheory.Spectrum.Prime.Localization.Homeomorph
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Irreducibility under prime-spectrum maps and localization

These ring-level statements are independent of algebraic geometry presentations.  Keeping them
under `PrimeSpectrum` lets affine and field-extension arguments reuse the same descent and
localization steps without importing a chapter support file.
-/

@[expose] public section

universe u v

namespace PrimeSpectrum

/-- Irreducibility of a prime spectrum descends along an injective ring homomorphism. -/
@[stacks 0G31 "injective spectrum descent"]
theorem irreducible_of_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f)
    (hS : IrreducibleSpace (PrimeSpectrum S)) :
    IrreducibleSpace (PrimeSpectrum R) := sorry

/-- A nontrivial localization of an irreducible prime spectrum is irreducible. -/
@[stacks 0G31 "localization of an irreducible spectrum"]
theorem irreducible_of_isLocalization
    {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (M : Submonoid R) [Algebra R A] [IsLocalization M A] [Nontrivial A]
    (hR : IrreducibleSpace (PrimeSpectrum R)) :
    IrreducibleSpace (PrimeSpectrum A) := sorry

end PrimeSpectrum
