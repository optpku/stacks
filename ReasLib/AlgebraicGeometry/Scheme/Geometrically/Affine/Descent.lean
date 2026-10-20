/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import ReasLib.Topology.IrreducibleComponents.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Descent of Irreducible Prime Spectra

This leaf is the ring-level bridge from the open-map criterion for irreducible
spaces to affine spectra.  The fiber is represented by the canonical
`Ideal.Fiber` construction, so applications do not need a chapter-specific
set-theoretic fiber wrapper.
-/

@[expose] public section

open PrimeSpectrum

universe u v

namespace PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- An open affine spectral map with a dense set of irreducible ring fibers has
an irreducible source spectrum. -/
@[stacks 00I6 "open-map affine descent"]
theorem irreducible_of_open_denseFiber
    (hR : IrreducibleSpace (PrimeSpectrum R))
    (hopen : IsOpenMap (comap (algebraMap R S)))
    (hdense : Dense {p : PrimeSpectrum R |
      IrreducibleSpace (PrimeSpectrum (p.asIdeal.Fiber S))}) :
    IrreducibleSpace (PrimeSpectrum S) := sorry

/-- Flat finite-presentation affine maps satisfy the open-map irreducibility
criterion on a dense set of irreducible fibers. -/
@[stacks 00I6]
theorem irreducible_of_flat_finitePresentation
    (hR : IrreducibleSpace (PrimeSpectrum R))
    [Module.Flat R S] [Algebra.FinitePresentation R S]
    (hdense : Dense {p : PrimeSpectrum R |
      IrreducibleSpace (PrimeSpectrum (p.asIdeal.Fiber S))}) :
    IrreducibleSpace (PrimeSpectrum S) := sorry

end PrimeSpectrum
