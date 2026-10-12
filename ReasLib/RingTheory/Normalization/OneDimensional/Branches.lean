/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.Branches
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.LocalRing.Branches
public import ReasLib.RingTheory.LocalRing.Wedge.StrictHenselianDvr
public import ReasLib.RingTheory.Normalization.OneDimensional.DeltaInvariant
public import ReasLib.RingTheory.PowerSeries.Multicross

/-!
# Branch bounds from normalization delta invariants

This leaf compares the normalization delta invariant with minimal-prime branch
counts in reduced Nagata one-dimensional local rings and records its wedge
rigidity case.
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace Normalization.OneDimensional

namespace StrictHenselian

variable {A : Type u}
variable [CommRing A] [StrictHenselianLocalRing A] [NagataRing A] [IsReduced A]

/-- The normalization delta invariant of a strictly henselian reduced Nagata
one-dimensional local ring is at least its minimal-prime count minus one. -/
@[stacks 0C42]
theorem deltaInvariant_ge_minimalPrimes_sub_one
    (h_dimension : ringKrullDim A = 1) :
    deltaInvariant A ≥ (minimalPrimes A).encard - 1 := sorry

/-- Equality in the minimal-prime bound for the normalization delta invariant
yields a wedge presentation by a finite family of strictly henselian discrete
valuation rings. -/
@[stacks 0C42]
theorem exists_wedgeOf_dvrFamily_of_deltaInvariant_eq
    (h_dimension : ringKrullDim A = 1)
    (h_eq : deltaInvariant A = (minimalPrimes A).encard - 1) :
    ∃ (m : ℕ) (As : LocalRing.Wedge.StrictHenselianDvrFamily m),
      As.IsWedgeOf A := sorry

end StrictHenselian

namespace StrictHenselization

variable {A : Type u} {Ash : Type v}
variable [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]

/-- The normalization delta invariant of a reduced Nagata one-dimensional
local ring is at least its geometric branch number, namely the minimal-prime
count of any strict henselization, minus one. -/
@[stacks 0C43]
theorem deltaInvariant_ge_minimalPrimes_sub_one
    (h_dimension : ringKrullDim A = 1) :
    deltaInvariant A ≥ (minimalPrimes Ash).encard - 1 := sorry

end StrictHenselization

section

variable {k : Type u} [Field k] [IsSepClosed k]
variable {A : Type v} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]
variable [Algebra k A]
variable {Ah : Type w} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

/-- The normalization delta invariant of a one-dimensional reduced Nagata local
`k`-algebra over a separably closed field, with residue field `k`, is at least
its branch number minus one. -/
@[stacks 0C1V]
theorem deltaInvariant_ge_branchNumber_sub_one
    (h_residue : Function.Bijective (ResidueField.map (algebraMap k A)))
    (h_dimension : ringKrullDim A = 1) :
    deltaInvariant A ≥ branchNumber A Ah - 1 := sorry

/-- Equality between the normalization delta invariant and the branch number
minus one for a one-dimensional reduced Nagata local `k`-algebra over a
separably closed field, with residue field `k`, identifies its maximal-ideal
completion with a multicross ring having the same number of branches. -/
@[stacks 0C1V]
theorem exists_completion_algEquiv_multicross_of_deltaInvariant_eq
    (h_residue : Function.Bijective (ResidueField.map (algebraMap k A)))
    (h_dimension : ringKrullDim A = 1)
    (h_eq : deltaInvariant A = branchNumber A Ah - 1) :
    ∃ n : ℕ, branchNumber A Ah = (n : ℕ∞) ∧
      Nonempty (AdicCompletion (maximalIdeal A) A ≃ₐ[k] Multicross.ring k n) := sorry

end

end Normalization.OneDimensional
