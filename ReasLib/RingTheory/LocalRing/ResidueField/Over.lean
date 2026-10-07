module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal
public import ReasLib.RingTheory.LocalRing.ResidueField.Under

/-!
# Residue extensions at maximal points

This file compares length over a local base with Mathlib's canonical
`Ideal.inertiaDeg` when a maximal point contracts to the closed point.

@stack 02M0
-/

@[expose] public section

universe u v

open IsLocalRing

namespace MaximalSpectrum

/-- When the residue-field map is finite, the length over the local base is the inertia degree. -/
@[stacks 02M0 "residue-field length equals inertia degree"]
theorem residueField_length_eq_inertiaDeg
    (A : Type u) {B : Type v}
    [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]
    (m : MaximalSpectrum B)
    (hcomap : Ideal.comap (algebraMap A B) m.asIdeal = maximalIdeal A)
    (hfinite : (Ideal.ResidueField.mapUnder A m.asIdeal).Finite) :
    Module.length A m.ResidueField = (m.asIdeal.inertiaDeg A : ℕ∞) := sorry

end MaximalSpectrum
