/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.Local.Properties
public import ReasLib.Topology.WLocal
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Bijectivity of ring maps with w-local spectra
-/

@[expose] public section

universe u

open PrimeSpectrum

namespace RingHom.IsIsoOnLocalRings

/-- A ring map identifying local rings is bijective if both spectra are w-local,
its spectrum map is w-local, and its induced map on connected components is
bijective. -/
theorem bijective_of_bijective_connectedComponents
    {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}
    [WLocalSpace (PrimeSpectrum A)] [WLocalSpace (PrimeSpectrum B)]
    [IsWLocalMap (comap f)] (hf : f.IsIsoOnLocalRings)
    (h_connectedComponents :
      Function.Bijective (continuous_comap f).connectedComponentsMap) :
    Function.Bijective f := sorry

end RingHom.IsIsoOnLocalRings
