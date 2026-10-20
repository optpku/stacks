/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.ExtremallyDisconnected
public import ReasLib.RingTheory.RingHom.Local.Properties
public import ReasLib.Topology.WLocal
public import ReasLib.RingTheory.RingHom.IndZariski
import Mathlib.Tactic.CrossRefAttribute

/-!
# Retractions of faithfully flat ind-Zariski ring maps

A commutative ring has retractions for every faithfully flat identifying-local-rings
map if and only if it has retractions for every faithfully flat ind-Zariski map, if
and only if its spectrum is w-local with extremally disconnected connected
components.
-/

@[expose] public section

universe u

namespace Algebra

/-- A commutative ring has the faithfully flat identifying-local-rings retraction
property when every faithfully flat ring map out of it that identifies local rings
admits a ring-homomorphism retraction. -/
def HasFaithfullyFlatIsIsoOnLocalRingsRetraction (A : Type u) [CommRing A] : Prop :=
  ∀ (B : Type u) [CommRing B] (f : A →+* B),
    f.FaithfullyFlat → f.IsIsoOnLocalRings →
      ∃ r : B →+* A, r.comp f = RingHom.id A

/-- A commutative ring has the faithfully flat ind-Zariski retraction property when
every faithfully flat ind-Zariski ring map out of it admits a ring-homomorphism
retraction. -/
def HasFaithfullyFlatIndZariskiRetraction (A : Type u) [CommRing A] : Prop :=
  ∀ (B : Type u) [CommRing B] (f : A →+* B),
    f.FaithfullyFlat → f.IndZariski →
      ∃ r : B →+* A, r.comp f = RingHom.id A

/-- For a commutative ring `A`, the following are equivalent:
every faithfully flat ring map `A →+* B` identifying local rings has a
retraction, every faithfully flat ind-Zariski ring map `A →+* B` has a
retraction, and `PrimeSpectrum A` is w-local with
`ConnectedComponents (PrimeSpectrum A)` extremally disconnected. -/
@[stacks 09AZ]
theorem hasFaithfullyFlatIndZariskiRetraction_tfae (A : Type u) [CommRing A] :
    List.TFAE
      [HasFaithfullyFlatIsIsoOnLocalRingsRetraction A,
        HasFaithfullyFlatIndZariskiRetraction A,
        WLocalSpace (PrimeSpectrum A) ∧
          ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A))] :=
  sorry

namespace HasFaithfullyFlatIsIsoOnLocalRingsRetraction

/-- A faithfully flat ring map that identifies local rings, out of a ring with the
identifying-local-rings retraction property, admits a ring-homomorphism retraction. -/
theorem exists_retraction {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}
    (h : HasFaithfullyFlatIsIsoOnLocalRingsRetraction A)
    (hf : f.FaithfullyFlat) (hiso : f.IsIsoOnLocalRings) :
    ∃ r : B →+* A, r.comp f = RingHom.id A :=
  sorry

end HasFaithfullyFlatIsIsoOnLocalRingsRetraction

namespace HasFaithfullyFlatIndZariskiRetraction

/-- A faithfully flat ind-Zariski ring map out of a ring with the ind-Zariski
retraction property admits a ring-homomorphism retraction. -/
theorem exists_retraction {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}
    (h : HasFaithfullyFlatIndZariskiRetraction A)
    (hf : f.FaithfullyFlat) (hind : f.IndZariski) :
    ∃ r : B →+* A, r.comp f = RingHom.id A :=
  sorry

/-- The identifying-local-rings and ind-Zariski retraction properties are equivalent. -/
theorem iff_isIsoOnLocalRings (A : Type u) [CommRing A] :
    HasFaithfullyFlatIndZariskiRetraction A ↔
      HasFaithfullyFlatIsIsoOnLocalRingsRetraction A :=
  sorry

/-- The ind-Zariski retraction property is equivalent to `PrimeSpectrum A` being
w-local with `ConnectedComponents (PrimeSpectrum A)` extremally disconnected. -/
theorem iff_wLocal_extremallyDisconnected (A : Type u) [CommRing A] :
    HasFaithfullyFlatIndZariskiRetraction A ↔
      WLocalSpace (PrimeSpectrum A) ∧
        ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) :=
  sorry

/-- A commutative ring whose spectrum is w-local with extremally disconnected
connected components has the faithfully flat ind-Zariski retraction property. -/
theorem of_wLocal_extremallyDisconnected {A : Type u} [CommRing A]
    [WLocalSpace (PrimeSpectrum A)]
    [ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A))] :
    HasFaithfullyFlatIndZariskiRetraction A :=
  sorry

end HasFaithfullyFlatIndZariskiRetraction

end Algebra

namespace RingHom.IndZariski

/-- Every commutative ring admits a faithfully flat ind-Zariski ring map to a ring
with the faithfully flat ind-Zariski retraction property. -/
@[stacks 09B0]
theorem exists_faithfullyFlat_indZariskiRetraction (A : Type u) [CommRing A] :
    ∃ (B : Type u) (_ : CommRing B) (f : A →+* B),
      f.FaithfullyFlat ∧ f.IndZariski ∧ Algebra.HasFaithfullyFlatIndZariskiRetraction B :=
  sorry

/-- Every commutative ring admits a faithfully flat ind-Zariski ring map to a ring
whose spectrum is w-local and whose space of connected components is extremally
disconnected. -/
theorem exists_faithfullyFlat_wLocal_extremallyDisconnected
    (A : Type u) [CommRing A] :
    ∃ (B : Type u) (_ : CommRing B) (f : A →+* B),
      f.FaithfullyFlat ∧ f.IndZariski ∧
        WLocalSpace (PrimeSpectrum B) ∧
          ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum B)) :=
  sorry

end RingHom.IndZariski
