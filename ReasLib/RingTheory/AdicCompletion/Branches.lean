/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.Henselian
public import ReasLib.RingTheory.LocalRing.Branches

@[expose] public section

/-!
# Branch numbers under one-dimensional completion

For a one-dimensional Noetherian local ring, maximal-ideal completion
preserves both ordinary and geometric branch numbers.  Chosen henselizations
remain explicit because the invariants are defined from their minimal-prime
sets, while the completion itself is the canonical `AdicCompletion` owner.

@stack 0C2D
-/

open IsLocalRing

universe u v w

namespace BranchNumber

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
variable {Ahat : Type w} [CommRing Ahat]
variable [Algebra (AdicCompletion (maximalIdeal A) A) Ahat]
variable [IsHenselizationOf (AdicCompletion (maximalIdeal A) A) Ahat]

/-- Maximal-ideal completion preserves the branch number of a one-dimensional
Noetherian local ring. -/
@[stacks 0C2D "branches of a one-dimensional local ring and its completion"]
theorem eq_completion_of_ringKrullDim_eq_one (hdim : ringKrullDim A = 1) :
    branchNumber A Ah =
      branchNumber (AdicCompletion (maximalIdeal A) A) Ahat := sorry
-- Proof strategy: combine `BranchNumber.le_completion` with the dimension-one description of
-- completion minimal primes from `exists_minimalPrime_of_completion_quotient_dimension_one`,
-- and conclude by antisymmetry of the two cardinal bounds.

end BranchNumber

namespace GeometricBranchNumber

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {Ash : Type v} [CommRing Ash] [Algebra A Ash]
variable [IsStrictHenselizationOf A Ash]
variable {Ahatsh : Type w} [CommRing Ahatsh]
variable [Algebra (AdicCompletion (maximalIdeal A) A) Ahatsh]
variable [IsStrictHenselizationOf (AdicCompletion (maximalIdeal A) A) Ahatsh]

/-- Maximal-ideal completion preserves the geometric branch number of a
one-dimensional Noetherian local ring. -/
@[stacks 0C2D "geometric branches of a one-dimensional local ring and its completion"]
theorem eq_completion_of_ringKrullDim_eq_one (hdim : ringKrullDim A = 1) :
    geometricBranchNumber A Ash =
      geometricBranchNumber (AdicCompletion (maximalIdeal A) A) Ahatsh := sorry
-- Proof strategy: apply the ordinary branch-number equality to the chosen strict
-- henselizations and rewrite both sides by the definition of geometric branch number.

end GeometricBranchNumber
