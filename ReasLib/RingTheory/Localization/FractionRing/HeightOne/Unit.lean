/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Localization.FractionRing.HeightOne

/-!
# Units at height-one primes

This file records when a unit of a chosen fraction field is already a unit in the
localization at a height-one prime.
-/

@[expose] public section

universe u v

namespace PrimeSpectrum.HeightOne

/-- A fraction-field unit is a unit at a height-one point when it comes from a unit of the
corresponding localization subalgebra. -/
def IsUnitAt {A : Type u} [CommRing A] [IsDomain A]
    (p : PrimeSpectrum.HeightOne A) (K : Type v)
    [Field K] [Algebra A K] [IsFractionRing A K] (f : Kˣ) : Prop :=
  ∃ a : (p.localizationSubalgebra K)ˣ,
    Units.map (p.localizationSubalgebra K).val.toMonoidHom a = f

/-- Membership in the local unit group is witnessed by a unit of the localization subalgebra
whose image is the given fraction-field unit. -/
theorem isUnitAt_iff {A : Type u} [CommRing A] [IsDomain A]
    (p : PrimeSpectrum.HeightOne A) (K : Type v)
    [Field K] [Algebra A K] [IsFractionRing A K] (f : Kˣ) :
    p.IsUnitAt K f ↔ ∃ a : (p.localizationSubalgebra K)ˣ,
      Units.map (p.localizationSubalgebra K).val.toMonoidHom a = f := sorry

end PrimeSpectrum.HeightOne
