/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.PrimeAvoidance
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Prime avoidance with transcendental residue classes
-/

@[expose] public section

universe u v

namespace Ideal

/-- For a finite pairwise-incomparable family of prime ideals, an ideal contained in
none of them contains an element whose residue class at every prime is transcendental
over the corresponding specified subfield. -/
theorem exists_mem_transcendental_residueFields
    {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
    (p : ι → PrimeSpectrum R)
    (hpair : ∀ ⦃i j⦄, i ≠ j → ¬ (p i).asIdeal ≤ (p j).asIdeal)
    (k : ∀ i, Subfield (p i).asIdeal.ResidueField)
    (htrans : ∀ i, ¬ Algebra.IsAlgebraic (k i) (p i).asIdeal.ResidueField)
    (J : Ideal R)
    (hJ : ∀ i, ¬ J ≤ (p i).asIdeal) :
    ∃ x ∈ J, ∀ i, Transcendental (k i)
      (algebraMap R (p i).asIdeal.ResidueField x) := sorry

end Ideal
