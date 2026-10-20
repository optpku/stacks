/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.Branches
public import ReasLib.RingTheory.Henselian.Henselization.Completion
public import ReasLib.RingTheory.Ideal.MinimalPrime.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Branch numbers and henselization-completion comparison

The canonical comparison from a henselization to the maximal-ideal completion contracts minimal
primes surjectively. Consequently, ordinary and geometric branch numbers cannot decrease after
completion.

@stack 0C28
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u v w

namespace IsHenselizationOf.Completion.Comparison

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/-- The comparison from a henselization of a Noetherian local ring to its completion is faithfully
flat. -/
@[stacks 0C28 "henselization-completion comparison is faithfully flat"]
theorem faithfullyFlat
    (iota : IsHenselizationOf.Completion.Comparison (R := A) (Rh := Ah)) :
    RingHom.FaithfullyFlat iota.toAlgHom.toRingHom := sorry
-- Proof strategy: identify `iota` with the canonical map from the henselization to the
-- maximal-ideal completion, then combine flatness of completion with surjectivity on spectra.

/-- Contraction along a henselization-completion comparison sends a completion minimal prime to a
henselization minimal prime. -/
@[stacks 0C28 "contraction of completion minimal primes"]
theorem comap_mem_minimalPrimes
    (iota : IsHenselizationOf.Completion.Comparison (R := A) (Rh := Ah))
    (Q : minimalPrimes ACompletion) :
    Ideal.comap iota.toAlgHom.toRingHom Q ∈ minimalPrimes Ah := sorry
-- Proof strategy: apply contraction of minimal primes along the faithfully flat comparison
-- `faithfullyFlat iota`, using the canonical prime structure carried by `Q`.

/-- The explicit map on minimal primes induced by contracting along a henselization-completion
comparison. -/
@[stacks 0C28 "minimal-prime map from completion to henselization"]
def minimalPrimeMap
    (iota : IsHenselizationOf.Completion.Comparison (R := A) (Rh := Ah)) :
    minimalPrimes ACompletion → minimalPrimes Ah :=
  fun Q => ⟨Ideal.comap iota.toAlgHom.toRingHom Q, comap_mem_minimalPrimes iota Q⟩

/-- The ideal underlying `minimalPrimeMap` is contraction along the comparison map. -/
@[simp, stacks 0C28 "minimal-prime comparison map on ideals"]
theorem minimalPrimeMap_apply
    (iota : IsHenselizationOf.Completion.Comparison (R := A) (Rh := Ah))
    (Q : minimalPrimes ACompletion) :
    (minimalPrimeMap iota Q : Ideal Ah) = Ideal.comap iota.toAlgHom.toRingHom Q := sorry
-- Proof strategy: unfold `minimalPrimeMap`; the underlying ideal of the resulting subtype is
-- definitionally the contraction of `Q`.

/-- Lemma 15.109.1 (1): the comparison from a henselization of a Noetherian local ring to its
completion induces a surjection on minimal primes. -/
@[stacks 0C28 "Lemma 15.109.1 (1)"]
theorem minimalPrimeMap_surjective
    (iota : IsHenselizationOf.Completion.Comparison (R := A) (Rh := Ah)) :
    Function.Surjective (minimalPrimeMap iota) := sorry
-- Proof strategy: use lying over for the faithfully flat comparison to lift a minimal prime of
-- `Ah`, then choose a minimal prime below the lift and contract it using minimality.

end IsHenselizationOf.Completion.Comparison

namespace BranchNumber

/-- Lemma 15.109.1 (2): the branch number of a Noetherian local ring is at most the number of
minimal primes of its maximal-ideal completion, hence at most the branch number of that
completion. -/
@[stacks 0C28 "Lemma 15.109.1 (2)"]
theorem le_completion
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah] :
    branchNumber A Ah ≤
      (minimalPrimes (AdicCompletion (maximalIdeal A) A)).encard := sorry
-- Proof strategy: instantiate the canonical henselization-to-completion comparison, apply
-- `minimalPrimeMap_surjective`, and turn its surjectivity into the corresponding `encard` bound.

end BranchNumber

namespace GeometricBranchNumber

/-- Lemma 15.109.1 (3): the geometric branch number of a Noetherian local ring is at most the
geometric branch number of its maximal-ideal completion. -/
@[stacks 0C28 "Lemma 15.109.1 (3)"]
theorem le_completion
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {Ash : Type v} [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    {Ahatsh : Type w} [CommRing Ahatsh]
    [Algebra (AdicCompletion (maximalIdeal A) A) Ahatsh]
    [IsStrictHenselizationOf (AdicCompletion (maximalIdeal A) A) Ahatsh] :
    geometricBranchNumber A Ash ≤
      geometricBranchNumber (AdicCompletion (maximalIdeal A) A) Ahatsh := sorry
-- Proof strategy: apply `BranchNumber.le_completion` to the chosen strict henselization and
-- rewrite the two branch-number carriers by the strict-henselization definitions.

end GeometricBranchNumber
