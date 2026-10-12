/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.ExtremallyDisconnected
public import ReasLib.RingTheory.RingHom.Local.Properties
public import stacks_project.Chap61.Definition_61_2_3_WLocal
public import stacks_project.Chap61.Definition_61_4_1_IndZariski
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.6.7

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

/-- Lemma 61.6.7: for a commutative ring `A`, the following are equivalent:
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
