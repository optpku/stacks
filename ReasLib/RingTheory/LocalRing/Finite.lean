/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.ResidueField.Map
public import ReasLib.RingTheory.LocalRing.ResidueField.Under
public import ReasLib.RingTheory.Spectrum.Maximal.Over

@[expose] public section

/-!
# Finite algebras over local rings

This leaf contains local-ring criteria for finite algebras expressed by the
fiber of prime ideals over the closed point of the base, together with the
basic locality theorem for finite maps between local rings.
-/

universe u v

open scoped TensorProduct
open IsLocalRing

namespace IsLocalRing

/-- A finite algebra over a local ring is local when a chosen prime over the
maximal ideal is the only prime over that ideal. The fiber uniqueness is an
explicit proposition because it is not a canonical instance. -/
@[stacks 04GG "finite local algebra from singleton prime fiber"]
theorem of_subsingleton_primesOver
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [Module.Finite R S] (q : (maximalIdeal R).primesOver S)
    (h : Subsingleton ((maximalIdeal R).primesOver S)) :
    IsLocalRing S := sorry

/-- A finite flat algebra over a local ring with rank-one closed fiber has bijective structure
map. -/
@[stacks 04GG "rank-one special fiber of a finite flat local algebra"]
theorem algebraMap_bijective_of_finrank_specialFiber_eq_one
    {R : Type u} {A : Type v} [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Flat R A]
    (hfinrank : Module.finrank (ResidueField R) (ResidueField R ⊗[R] A) = 1) :
    Function.Bijective (algebraMap R A) := sorry

/-- A finite flat algebra over a local ring with rank-one closed fiber is canonically equivalent
to the base as an algebra. -/
@[stacks 04GG "rank-one special fiber of a finite flat local algebra"]
noncomputable def algEquiv_of_finrank_specialFiber_eq_one
    {R : Type u} {A : Type v} [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Flat R A]
    (hfinrank : Module.finrank (ResidueField R) (ResidueField R ⊗[R] A) = 1) :
    A ≃ₐ[R] R :=
  (AlgEquiv.ofBijective (Algebra.ofId R A)
    (algebraMap_bijective_of_finrank_specialFiber_eq_one (R := R) (A := A) hfinrank)).symm

end IsLocalRing

namespace RingHom

/-- A finite homomorphism between local commutative rings is local.  This is
the map-level owner; `Algebra.isLocalHom_of_moduleFinite` is the canonical
algebra-map specialization. -/
@[stacks 04GH "finite local homomorphism"]
theorem isLocalHom_of_finite
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] {f : R →+* S} (hf : f.Finite) :
    IsLocalHom f := sorry

end RingHom

namespace Algebra

/-- The structure map of a module-finite algebra between local commutative
rings is local.  This is the no-extra-data form used by algebraic geometry
applications. -/
@[stacks 04GH "finite local algebra map"]
theorem isLocalHom_of_moduleFinite
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [Module.Finite R S] :
    IsLocalHom (algebraMap R S) := sorry

end Algebra

namespace MaximalSpectrum

/-- For a module-finite algebra over a local ring, every maximal ideal contracts to the unique
maximal ideal of the base. -/
theorem comap_eq_maximalIdeal_of_moduleFinite
    (R : Type u) {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [Module.Finite R S] (m : MaximalSpectrum S) :
    Ideal.comap (algebraMap R S) m.asIdeal = maximalIdeal R := sorry

/-- A maximal ideal of a module-finite algebra over a local ring lies over the closed point of the
base. -/
theorem liesOver_maximalIdeal_of_moduleFinite
    (R : Type u) {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [Module.Finite R S] (m : MaximalSpectrum S) :
    m.asIdeal.LiesOver (maximalIdeal R) := sorry

/-- The closed-point relation for a maximal ideal of a module-finite local algebra is canonical,
so it is available to typeclass search. -/
instance instLiesOverMaximalIdealOfModuleFinite
    (R : Type u) {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [Module.Finite R S] (m : MaximalSpectrum S) :
    m.asIdeal.LiesOver (maximalIdeal R) :=
  liesOver_maximalIdeal_of_moduleFinite R m

/-- A module-finite algebra over a local ring has a finite maximal spectrum. -/
theorem finite_of_moduleFinite
    (R : Type u) {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [Module.Finite R S] :
    Finite (MaximalSpectrum S) := sorry

/-- For a module-finite algebra over a local ring, every maximal point lies over the closed point,
so the full maximal spectrum is canonically the closed-point fiber. -/
def overMaximalIdealEquivOfModuleFinite
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [Module.Finite R S] :
    MaximalSpectrum S ≃ over (maximalIdeal R) S :=
  equivOver (maximalIdeal R) (liesOver_maximalIdeal_of_moduleFinite R)

/-- The residue field at a maximal ideal of a module-finite local algebra is finite over the
residue field of the base. The induced scalar structure remains scoped, since registering it as a
global instance would create competing residue-field algebra paths. -/
theorem residueField_finite_of_moduleFinite
    (R : Type u) {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [Module.Finite R S] (m : MaximalSpectrum S) :
    letI : Algebra (maximalIdeal R).ResidueField m.asIdeal.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver (maximalIdeal R) m.asIdeal
    Module.Finite (maximalIdeal R).ResidueField m.asIdeal.ResidueField := sorry

end MaximalSpectrum

namespace Ideal.ResidueField

/-- The residue-field map from the contraction of a maximal ideal in a module-finite algebra over
a local ring is finite. This map-level form avoids a scoped residue-field algebra instance. -/
@[stacks 02M0 "finite residue-field map of a module-finite algebra"]
theorem mapUnder_finite_of_moduleFinite
    (R : Type u) {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [Module.Finite R S] (m : MaximalSpectrum S) :
    (mapUnder R m.asIdeal).Finite := sorry

end Ideal.ResidueField
