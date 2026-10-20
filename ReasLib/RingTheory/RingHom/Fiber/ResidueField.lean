/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.Local.AtPrime

/-!
# Bijective residue-field maps

This leaf owns the pointwise residue-field-isomorphism property of a
commutative ring homomorphism. It is independent of the mechanism used to
obtain that property.

@stack 0CAR
-/

@[expose] public section

open PrimeSpectrum

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring homomorphism induces a bijection on residue fields at the target
prime `q`. -/
@[stacks 0CAR "bijective residue-field map at a target prime"]
def ResidueField.IsBijectiveAt (f : R →+* S) (q : PrimeSpectrum S) : Prop :=
  Function.Bijective (Ideal.ResidueField.map
    (comap f q).asIdeal q.asIdeal f rfl)

/-- The residue-field map at a named source prime and target prime.  The
equality argument identifies the source prime with the contraction of the
target prime, so consumers can keep the geometric point `p` visible instead
of unfolding `PrimeSpectrum.comap`. -/
noncomputable def ResidueField.mapAtSourcePrime
    (f : R →+* S) (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hpq : p = PrimeSpectrum.comap f q) :
    p.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
  Ideal.ResidueField.map p.asIdeal q.asIdeal f
    ((congrArg PrimeSpectrum.asIdeal hpq).trans
      (PrimeSpectrum.comap_asIdeal f q))

namespace ResidueField.IsBijectiveAt

/-- A bijective residue-field map at `q` remains bijective when its source
prime is named explicitly. -/
theorem mapAtSourcePrime_bijective
    {f : R →+* S} {q : PrimeSpectrum S}
    (h : ResidueField.IsBijectiveAt f q)
    {p : PrimeSpectrum R} (hpq : p = PrimeSpectrum.comap f q) :
    Function.Bijective (ResidueField.mapAtSourcePrime f p q hpq) := sorry

/-- The pointwise property gives bijectivity of the canonical residue-field
map. -/
theorem map_bijective
    {f : R →+* S} {q : PrimeSpectrum S}
    (h : ResidueField.IsBijectiveAt f q) :
    Function.Bijective (Ideal.ResidueField.map
      (comap f q).asIdeal q.asIdeal f rfl) := sorry

/-- The pointwise property is independent of how the contracted prime is
named. -/
theorem map_bijective_of_comap_eq
    {f : R →+* S} {q : PrimeSpectrum S}
    (h : ResidueField.IsBijectiveAt f q) {p : PrimeSpectrum R}
    (hp : p.asIdeal = Ideal.comap f q.asIdeal) :
    Function.Bijective
      (Ideal.ResidueField.map p.asIdeal q.asIdeal f hp) := sorry

/-- The canonical ring equivalence induced by the residue-field map at a
target prime. -/
noncomputable def equiv
    {f : R →+* S} {q : PrimeSpectrum S}
    (h : ResidueField.IsBijectiveAt f q) :
    (comap f q).asIdeal.ResidueField ≃+* q.asIdeal.ResidueField :=
  RingEquiv.ofBijective
    (Ideal.ResidueField.map (comap f q).asIdeal q.asIdeal f rfl) h

/-- The pointwise residue-field equivalence agrees with the canonical map on
elements. -/
theorem equiv_apply
    {f : R →+* S} {q : PrimeSpectrum S}
    (h : ResidueField.IsBijectiveAt f q)
    (x : (comap f q).asIdeal.ResidueField) :
    h.equiv x =
      Ideal.ResidueField.map (comap f q).asIdeal q.asIdeal f rfl x := sorry

end ResidueField.IsBijectiveAt

/-- A ring homomorphism has bijective residue-field maps at every target prime. -/
@[stacks 0CAR "bijective residue-field maps at every target prime"]
def ResidueField.MapsBijective (f : R →+* S) : Prop :=
  ∀ q : PrimeSpectrum S, ResidueField.IsBijectiveAt f q

namespace ResidueField.MapsBijective

/-- The bundled residue-field property gives the bijectivity statement at a specified target
prime. -/
theorem map_bijective
    {f : R →+* S} (h : ResidueField.MapsBijective f) (q : PrimeSpectrum S) :
    Function.Bijective (Ideal.ResidueField.map
      (comap f q).asIdeal q.asIdeal f rfl) := sorry

/-- The bundled residue-field property can be expressed using an independently named contracted
prime. -/
theorem map_bijective_of_comap_eq
    {f : R →+* S} (h : ResidueField.MapsBijective f)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S) (hq : comap f q = p) :
    Function.Bijective (Ideal.ResidueField.map p.asIdeal q.asIdeal f
      (congrArg PrimeSpectrum.asIdeal hq).symm) := sorry

/-- The canonical ring equivalence induced by a bijective residue-field map. -/
noncomputable def equiv
    {f : R →+* S} (h : ResidueField.MapsBijective f) (q : PrimeSpectrum S) :
    (comap f q).asIdeal.ResidueField ≃+* q.asIdeal.ResidueField :=
  ResidueField.IsBijectiveAt.equiv (h q)

/-- The residue-field equivalence is the canonical residue-field map on elements. -/
theorem equiv_apply
    {f : R →+* S} (h : ResidueField.MapsBijective f) (q : PrimeSpectrum S)
    (x : (comap f q).asIdeal.ResidueField) :
    h.equiv q x =
      Ideal.ResidueField.map (comap f q).asIdeal q.asIdeal f rfl x := sorry

end ResidueField.MapsBijective

end RingHom
