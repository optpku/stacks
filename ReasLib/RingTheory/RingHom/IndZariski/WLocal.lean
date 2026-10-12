/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.IndZariski.Local
public import ReasLib.Topology.WLocal
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Ind-Zariski ring maps with w-local spectra

A ring map between w-local spectra whose spectrum map is w-local is
ind-Zariski if and only if it identifies local rings.
-/

@[expose] public section

universe u

open PrimeSpectrum

namespace RingHom.IndZariski

/-- A ring map identifying local rings is ind-Zariski when both spectra and
the induced spectrum map are w-local. -/
theorem of_isIsoOnLocalRings {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}
    [WLocalSpace (PrimeSpectrum A)] [WLocalSpace (PrimeSpectrum B)]
    [IsWLocalMap (comap f)] (hf : f.IsIsoOnLocalRings) : f.IndZariski := sorry

/-- A ring map between w-local spectra whose spectrum map is w-local is
ind-Zariski if and only if it identifies local rings. -/
theorem isIsoOnLocalRings_iff {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}
    [WLocalSpace (PrimeSpectrum A)] [WLocalSpace (PrimeSpectrum B)]
    [IsWLocalMap (comap f)] : f.IndZariski ↔ f.IsIsoOnLocalRings := sorry

end RingHom.IndZariski
