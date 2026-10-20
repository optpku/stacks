/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

/-!
# Compact-Open Structure of Prime Spectra

The three source clauses are exposed through their exact topological classes;
the stronger spectral-space instance remains an auxiliary owner-level check.

@stack 04PM
-/

universe u

section

variable (R : Type u) [CommRing R]

/- Lemma 10.17.9: for a commutative ring `R`, the prime spectrum `Spec(R)` is a spectral space.
In particular, it is quasi-compact, it has a basis of quasi-compact opens, and intersections of
quasi-compact opens are quasi-compact. Mathlib exposes this at the owner level as the canonical
instance `PrimeSpectrum.instSpectralSpace`, already for a commutative semiring; the textbook ring
statement is its special case. -/
@[stacks 04PM "(1) prime spectra are quasi-compact"]
#check (inferInstance : CompactSpace (PrimeSpectrum R))

@[stacks 04PM "(2) compact opens form a basis"]
#check (inferInstance : PrespectralSpace (PrimeSpectrum R))

@[stacks 04PM "(3) intersections of compact opens are compact"]
#check (inferInstance : QuasiSeparatedSpace (PrimeSpectrum R))

#check @PrimeSpectrum.instSpectralSpace

end
