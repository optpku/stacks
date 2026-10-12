/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.SeparableDegree
public import ReasLib.Data.Set.Card
public import ReasLib.RingTheory.Ideal.MinimalPrime.Cardinality
public import ReasLib.RingTheory.LocalRing.Branches
public import ReasLib.RingTheory.LocalRing.Unibranch.Henselization
public import ReasLib.RingTheory.LocalRing.Unibranch.StrictHenselization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Branch numbers and unibranch local rings

This file gives the qualitative and normalization formulas for the branch invariants. The
Henselization and strict Henselization remain explicit inputs, while their universes are
independent of the base ring.

@stack 0C37
-/

@[expose] public section

open Ideal
open scoped Unibranch

universe u v

namespace BranchNumber

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

/-- Infinitely many minimal primes of a local ring force its branch number to be infinite. -/
@[stacks 0C37 "Lemma 15.107.7 (1), infinitely many branches"]
theorem eq_top_of_infinite_minimalPrimes
    (h : (minimalPrimes A).Infinite) :
    branchNumber A Ah = ⊤ :=
  (RingHom.minimalPrimes_infinite_of_injective
    (FaithfulSMul.algebraMap_injective A Ah) h).encard_eq

/-- A local ring has branch number one exactly when it is unibranch. -/
@[stacks 0C37 "Lemma 15.107.7 (2), one branch iff unibranch"]
theorem eq_one_iff_isUnibranch :
    branchNumber A Ah = 1 ↔ IsUnibranch A := by
  simpa only [branchNumber, Set.encard_eq_one_iff_existsUnique_mem] using
    (IsUnibranch.Henselization.iff_uniqueMinimalPrime (A := A) (Ah := Ah)).symm

/-- If a local ring has finitely many minimal primes, its branches are counted by the maximal
spectrum of the normalization of its reduction. -/
@[stacks 0C37 "Lemma 15.107.7 (4), branches counted by the normalization"]
theorem eq_card_normalization
    (h : (minimalPrimes A).Finite) :
    branchNumber A Ah = ENat.card (MaximalSpectrum A′) := sorry

end BranchNumber

namespace GeometricBranchNumber

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {Ash : Type v} [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

/-- Infinitely many minimal primes of a local ring force its geometric branch number to be
infinite. -/
@[stacks 0C37 "Lemma 15.107.7 (1), infinitely many geometric branches"]
theorem eq_top_of_infinite_minimalPrimes
    (h : (minimalPrimes A).Infinite) :
    geometricBranchNumber A Ash = ⊤ :=
  (RingHom.minimalPrimes_infinite_of_injective
    (FaithfulSMul.algebraMap_injective A Ash) h).encard_eq

/-- A local ring has geometric branch number one exactly when it is geometrically unibranch. -/
@[stacks 0C37 "Lemma 15.107.7 (3), one geometric branch iff geometrically unibranch"]
theorem eq_one_iff_isGeometricallyUnibranch :
    geometricBranchNumber A Ash = 1 ↔ IsGeometricallyUnibranch A := by
  simpa only [geometricBranchNumber, Set.encard_eq_one_iff_existsUnique_mem] using
    (IsGeometricallyUnibranch.StrictHenselization.iff_uniqueMinimalPrime
      (A := A) (Ash := Ash)).symm

/-- If a local ring has finitely many minimal primes, its geometric branches are the maximal
points of the normalization weighted by residue-field embeddings. -/
@[stacks 0C37 "Lemma 15.107.7 (5), geometric branches counted by the normalization"]
theorem eq_card_normalization
    (h : (minimalPrimes A).Finite) :
    geometricBranchNumber A Ash =
      ENat.card
        (Σ m : MaximalSpectrum A′, Field.Emb (IsLocalRing.ResidueField A) m.ResidueField) := sorry

end GeometricBranchNumber
