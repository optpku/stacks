/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The regular locus of a prime spectrum

This file owns the regular locus independently of the `J`-ring hierarchy.  The locus is concrete
data; openness conditions and `J`-ring predicates live in downstream files.
@stack 07P7
-/

universe u

namespace PrimeSpectrum

variable (R : Type u) [CommRing R]

/-- The regular locus of `Spec R` consists of primes whose local rings are regular. -/
@[stacks 07P7 "regular locus"]
def regularLocus : Set (PrimeSpectrum R) :=
  { p | IsRegularLocalRing (Localization.AtPrime p.asIdeal) }

/-- Textbook notation for the regular locus of an affine spectrum. -/
scoped[PrimeSpectrum] notation "Reg(Spec " R ")" => regularLocus R

/-- Membership in the regular locus is regularity of the corresponding prime localization. -/
@[simp]
theorem mem_regularLocus (p : PrimeSpectrum R) :
    p ∈ Reg(Spec R) ↔ IsRegularLocalRing (Localization.AtPrime p.asIdeal) := sorry

/-- The regular locus is stable under generalization. -/
theorem regularLocus_stableUnderGeneralization :
    StableUnderGeneralization (Reg(Spec R)) := sorry

end PrimeSpectrum

open PrimeSpectrum
open scoped PrimeSpectrum

/-- A principal localization is regular exactly when its basic open lies in the regular locus. -/
theorem isRegularRing_localizationAway_iff_basicOpen_subset_regularLocus
    {A : Type u} [CommRing A] [IsNoetherianRing A] (a : A) :
    IsRegularRing (Localization.Away a) ↔
      (basicOpen a : Set (PrimeSpectrum A)) ⊆ Reg(Spec A) := sorry

/-- The regular locus of a regular ring is the whole spectrum. -/
theorem regularLocus_eq_univ_of_isRegularRing
    (R : Type u) [CommRing R] [IsRegularRing R] :
    Reg(Spec R) = Set.univ := sorry
