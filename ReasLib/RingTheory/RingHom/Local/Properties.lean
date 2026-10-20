/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalIso
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.RingHom.OpenImmersion
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Local properties of ring homomorphisms

This file defines properties of commutative ring maps formulated using local
rings of the target or finiteness of the target ring.
-/

@[expose] public section

universe u

namespace RingHom

/-- An explicit commutative ring homomorphism is a local isomorphism when its
associated algebra is locally a standard open immersion. -/
def IsLocalIso {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A) : Prop :=
  @Algebra.IsLocalIso R A _ _ φ.toAlgebra

/-- A ring map is an isomorphism on local rings when the induced map at every
prime of its target is bijective. -/
def IsIsoOnLocalRings {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) : Prop :=
  ∀ q : PrimeSpectrum A,
    Function.Bijective
      (Localization.localRingHom (PrimeSpectrum.comap φ q).asIdeal q.asIdeal φ rfl)

/-- A ring map is an affine open immersion when every target prime has a
source principal-open neighborhood on which the induced localization map is
bijective. -/
def IsOpenImmersion {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) : Prop :=
  ∀ q : PrimeSpectrum A, ∃ f : R,
    φ f ∉ q.asIdeal ∧ Function.Bijective (Localization.awayMap φ f)

/-- A ring map has Noetherian target when its codomain is a Noetherian ring. -/
def TargetIsNoetherian {R A : Type u} [CommRing R] [CommRing A] (_ : R →+* A) : Prop :=
  IsNoetherianRing A

/-- Being locally a standard open immersion on the target is a local property
of a commutative ring map. -/
theorem locallyStandardOpenImmersion_propertyIsLocal :
    RingHom.PropertyIsLocal (RingHom.Locally RingHom.IsStandardOpenImmersion) := sorry

/-- Being locally a standard open immersion on the target is stable under base change. -/
theorem locallyStandardOpenImmersion_isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange
      (RingHom.Locally RingHom.IsStandardOpenImmersion) := sorry

namespace IsLocalIso

/-- If a commutative ring map and its composite with a second map are local
isomorphisms, then the second map is a local isomorphism. -/
theorem of_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} {g : S →+* T} (source_isLocalIso : RingHom.IsLocalIso f)
    (composite_isLocalIso : RingHom.IsLocalIso (g.comp f)) :
    RingHom.IsLocalIso g := sorry

end IsLocalIso

namespace IsIsoOnLocalRings

/-- If a commutative ring map and its composite with a second map identify
local rings, then the second map identifies local rings. -/
theorem of_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} {g : S →+* T}
    (source_isIsoOnLocalRings : RingHom.IsIsoOnLocalRings f)
    (composite_isIsoOnLocalRings : RingHom.IsIsoOnLocalRings (g.comp f)) :
    RingHom.IsIsoOnLocalRings g := sorry

/-- Being an isomorphism on every target local ring is a local property of a
commutative ring map. -/
theorem propertyIsLocal :
    RingHom.PropertyIsLocal RingHom.IsIsoOnLocalRings := sorry

/-- Being an isomorphism on every target local ring is stable under base change. -/
theorem isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange RingHom.IsIsoOnLocalRings := sorry

/-- Being an isomorphism on every target local ring is stable under composition. -/
theorem stableUnderComposition :
    RingHom.StableUnderComposition RingHom.IsIsoOnLocalRings := sorry

end IsIsoOnLocalRings

namespace IsOpenImmersion

/-- An affine open immersion supplies, at every target prime, a source
element avoided by that prime and a bijective map of principal localizations. -/
theorem exists_awayMap_bijective {R A : Type u} [CommRing R] [CommRing A]
    {φ : R →+* A} (h : RingHom.IsOpenImmersion φ) (q : PrimeSpectrum A) :
    ∃ f : R, φ f ∉ q.asIdeal ∧ Function.Bijective (Localization.awayMap φ f) := sorry

/-- Being an affine open immersion is a local property of a commutative ring map. -/
theorem propertyIsLocal :
    RingHom.PropertyIsLocal RingHom.IsOpenImmersion := sorry

end IsOpenImmersion

namespace TargetIsNoetherian

/-- Having Noetherian target is a local property of a commutative ring map. -/
theorem propertyIsLocal :
    RingHom.PropertyIsLocal RingHom.TargetIsNoetherian := sorry

/-- Having Noetherian target is stable under composition of commutative ring maps. -/
theorem stableUnderComposition :
    RingHom.StableUnderComposition RingHom.TargetIsNoetherian := sorry

end TargetIsNoetherian

end RingHom
