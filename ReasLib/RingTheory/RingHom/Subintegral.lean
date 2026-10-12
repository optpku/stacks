/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.LocallyNilpotent
public import ReasLib.RingTheory.RingHom.BaseChange
public import ReasLib.RingTheory.RingHom.Fiber.ResidueField
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Subintegral ring homomorphisms

This leaf packages the standard subintegral condition: integrality, a
bijection on prime spectra, and isomorphisms on residue fields. It is the
neutral owner for conclusions that should not be represented by a repeated
large conjunction.
-/

@[expose] public section

open PrimeSpectrum
open scoped TensorProduct

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A subintegral ring homomorphism is integral, bijective on prime spectra, and induces
bijective maps on residue fields. -/
structure IsSubintegral (f : R →+* S) : Prop where
  /-- The ring map is integral. -/
  isIntegral : f.IsIntegral
  /-- Contraction along the ring map is a bijection on prime spectra. -/
  comap_bijective : Function.Bijective (comap f)
  /-- Every induced residue-field map is bijective. -/
  residueField_maps_bijective : ResidueField.MapsBijective f

namespace IsSubintegral

/-- A subintegral map is injective on prime spectra. -/
theorem comap_injective
    {f : R →+* S} (h : f.IsSubintegral) :
    Function.Injective (comap f) := sorry

/-- A subintegral map is surjective on prime spectra. -/
theorem comap_surjective
    {f : R →+* S} (h : f.IsSubintegral) :
    Function.Surjective (comap f) := sorry

/-- A subintegral map has a bijective residue-field map at every specified target prime. -/
theorem residueField_map_bijective
    {f : R →+* S} (h : f.IsSubintegral) (q : PrimeSpectrum S) :
    let p : PrimeSpectrum R := comap f q
    Function.Bijective (Ideal.ResidueField.map p.asIdeal q.asIdeal f rfl) := sorry

/-- A subintegral map has a bijective residue-field map when the source prime is supplied
separately together with its contraction equality. -/
theorem residueField_map_bijective_of_comap_eq
    {f : R →+* S} (h : f.IsSubintegral)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S) (hq : comap f q = p) :
    let fκ : p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
      Ideal.ResidueField.map p.asIdeal q.asIdeal f
        (by simpa using (congrArg PrimeSpectrum.asIdeal hq).symm)
    Function.Bijective fκ := sorry

/-- The canonical residue-field equivalence attached to a subintegral map. -/
noncomputable def residueField_equiv
    {f : R →+* S} (h : f.IsSubintegral) (q : PrimeSpectrum S) :
    let p : PrimeSpectrum R := comap f q
    p.asIdeal.ResidueField ≃+* q.asIdeal.ResidueField :=
  ResidueField.MapsBijective.equiv h.residueField_maps_bijective q

/-- A subintegral map induces a homeomorphism on prime spectra. -/
theorem isHomeomorph_comap
    {f : R →+* S} (h : f.IsSubintegral) :
    IsHomeomorph (comap f) := sorry

/-- The kernel of a subintegral map is locally nilpotent. -/
theorem ker_isLocallyNilpotent
    {f : R →+* S} (h : f.IsSubintegral) :
    (RingHom.ker f).IsLocallyNilpotent := sorry

/-- Subintegrality is preserved by arbitrary tensor-product base change when the ambient algebra
structures are already fixed. -/
theorem baseChange
    {R' : Type w} [CommRing R'] [Algebra R S] [Algebra R R']
    (h : (algebraMap R S).IsSubintegral) :
    let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
    f'.IsSubintegral := sorry

/-- Ring-hom presentation of subintegrality after base change. This bridge intentionally installs
the canonical algebra associated to `f`; callers with an ambient `Algebra R S` should prefer
`IsSubintegral.baseChange`. -/
theorem baseChange_of_ringHom
    {R' : Type w} [CommRing R'] [Algebra R R']
    {f : R →+* S} (h : f.IsSubintegral) :
    letI : Algebra R S := f.toAlgebra
    let f' : R' →+* R' ⊗[R] S := algebraMap R' (R' ⊗[R] S)
    f'.IsSubintegral := sorry

end IsSubintegral

end RingHom
