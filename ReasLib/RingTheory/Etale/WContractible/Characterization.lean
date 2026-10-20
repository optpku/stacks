module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.ExtremallyDisconnected
public import ReasLib.RingTheory.Etale.WContractible
public import ReasLib.RingTheory.Etale.Weakly.IndEtale
public import ReasLib.RingTheory.Henselian.StrictHenselian.EtaleRetraction
public import ReasLib.RingTheory.RingHom.IndEtale.Basic
public import ReasLib.RingTheory.RingHom.IndZariski.Retraction
import Mathlib.Tactic.CrossRefAttribute

/-!
# W-contractible characterizations

A commutative ring is w-contractible if and only if every faithfully flat
ind-étale ring map out of it has a retraction, if and only if its spectrum is
w-local with extremally disconnected connected components and strictly henselian
localizations at maximal ideals.
-/

@[expose] public section

universe u

namespace Algebra

/-- A commutative ring has the faithfully flat ind-étale retraction property
when every faithfully flat ind-étale ring map out of it admits a
ring-homomorphism retraction. -/
def HasFaithfullyFlatIndEtaleRetraction (A : Type u) [CommRing A] : Prop :=
  ∀ (B : Type u) [CommRing B] (f : A →+* B),
    f.FaithfullyFlat → f.IndEtale →
      ∃ r : B →+* A, r.comp f = RingHom.id A

namespace HasFaithfullyFlatIndEtaleRetraction

/-- A faithfully flat ind-étale ring map out of a ring with the ind-étale
retraction property admits a ring-homomorphism retraction. -/
theorem exists_retraction {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}
    (h : HasFaithfullyFlatIndEtaleRetraction A)
    (hf : f.FaithfullyFlat) (hind : f.IndEtale) :
    ∃ r : B →+* A, r.comp f = RingHom.id A :=
  sorry

end HasFaithfullyFlatIndEtaleRetraction

end Algebra

namespace IsWContractibleRing

/-- For a commutative ring `A`, being w-contractible is equivalent to every
faithfully flat ind-étale ring map `A →+* B` having a retraction, and to
`PrimeSpectrum A` being w-local with `ConnectedComponents (PrimeSpectrum A)`
extremally disconnected and `Localization.AtPrime m` strictly henselian at
every maximal ideal `m`. -/
@[stacks 0982]
theorem tfae (A : Type u) [CommRing A] :
    List.TFAE
      [IsWContractibleRing.{u, u} A,
        Algebra.HasFaithfullyFlatIndEtaleRetraction A,
        WLocalSpace (PrimeSpectrum A) ∧
          ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) ∧
            ∀ (m : Ideal A) [m.IsMaximal],
              StrictHenselianLocalRing (Localization.AtPrime m)] :=
  sorry

/-- A commutative ring is w-contractible if and only if every faithfully flat
ind-étale ring map out of it has a retraction. -/
theorem iff_hasFaithfullyFlatIndEtaleRetraction {A : Type u} [CommRing A] :
    IsWContractibleRing.{u, u} A ↔
      Algebra.HasFaithfullyFlatIndEtaleRetraction A :=
  sorry

/-- A commutative ring is w-contractible if and only if its spectrum is w-local,
its connected components are extremally disconnected, and its localizations at
maximal ideals are strictly henselian. -/
theorem iff_wLocal_extremallyDisconnected_strictlyHenselian {A : Type u}
    [CommRing A] :
    IsWContractibleRing.{u, u} A ↔
      WLocalSpace (PrimeSpectrum A) ∧
        ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) ∧
          ∀ (m : Ideal A) [m.IsMaximal],
            StrictHenselianLocalRing (Localization.AtPrime m) :=
  sorry

/-- A faithfully flat ind-étale ring map out of a w-contractible ring admits a
ring-homomorphism retraction. -/
theorem exists_indEtale_retraction {A B : Type u} [CommRing A] [CommRing B]
    [IsWContractibleRing.{u, u} A] {f : A →+* B} (hf : f.FaithfullyFlat)
    (hind : f.IndEtale) :
    ∃ r : B →+* A, r.comp f = RingHom.id A :=
  sorry

/-- The spectrum of a w-contractible ring is w-local. -/
instance wLocalSpace {A : Type u} [CommRing A] [IsWContractibleRing.{u, u} A] :
    WLocalSpace (PrimeSpectrum A) :=
  sorry

/-- The connected components of the spectrum of a w-contractible ring are
extremally disconnected. -/
instance extremallyDisconnected_connectedComponents {A : Type u} [CommRing A]
    [IsWContractibleRing.{u, u} A] :
    ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A)) :=
  sorry

/-- The localization of a w-contractible ring at a maximal ideal is strictly
henselian. -/
instance strictlyHenselian_atMaximalIdeal {A : Type u} [CommRing A]
    [IsWContractibleRing.{u, u} A] (m : Ideal A) [m.IsMaximal] :
    StrictHenselianLocalRing (Localization.AtPrime m) :=
  sorry

/-- A commutative ring whose spectrum is w-local with extremally disconnected
connected components and strictly henselian localizations at maximal ideals is
w-contractible. -/
theorem of_wLocal_extremallyDisconnected_strictlyHenselian {A : Type u}
    [CommRing A] [WLocalSpace (PrimeSpectrum A)]
    [ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum A))]
    (h_strict : ∀ (m : Ideal A) [m.IsMaximal],
      StrictHenselianLocalRing (Localization.AtPrime m)) :
    IsWContractibleRing.{u, u} A :=
  sorry

end IsWContractibleRing
