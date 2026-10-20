/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.Branches

/-!
# Branch numbers at scheme points

This leaf transports the local-ring branch invariants to the stalk of a
scheme.  It has no normalization or field-extension assumptions, so both
specialized layers build on this one.
-/

@[expose] public section

open AlgebraicGeometry

universe u v

noncomputable section

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The branch number of `X` at `x` is the branch number of the local ring
`X.presheaf.stalk x`. -/
@[stacks 0C38 "branch number at a scheme point"]
abbrev branchNumberAt
    (x : X) (Ah : Type v) [CommRing Ah] [Algebra (X.presheaf.stalk x) Ah]
    [IsHenselizationOf (X.presheaf.stalk x) Ah] : ℕ∞ :=
  branchNumber (X.presheaf.stalk x) Ah

/-- The scheme-level branch number is the branch number of the stalk. -/
@[simp, stacks 0C38 "branch number at a scheme point definition"]
theorem branchNumberAt_def
    (x : X) (Ah : Type v) [CommRing Ah] [Algebra (X.presheaf.stalk x) Ah]
    [IsHenselizationOf (X.presheaf.stalk x) Ah] :
    X.branchNumberAt x Ah = branchNumber (X.presheaf.stalk x) Ah := sorry

/-- The branch number at a scheme point is the number of minimal primes of its
chosen henselization. -/
@[simp, stacks 0C38 "branch number as minimal-prime cardinality"]
theorem branchNumberAt_eq_encard_minimalPrimes
    (x : X) (Ah : Type v) [CommRing Ah] [Algebra (X.presheaf.stalk x) Ah]
    [IsHenselizationOf (X.presheaf.stalk x) Ah] :
    X.branchNumberAt x Ah = (minimalPrimes Ah).encard := sorry

/-- The geometric branch number of `X` at `x` is the geometric branch number
of the local ring `X.presheaf.stalk x`. -/
@[stacks 0C38 "geometric branch number at a scheme point"]
abbrev geometricBranchNumberAt
    (x : X) (Ash : Type v) [CommRing Ash]
    [Algebra (X.presheaf.stalk x) Ash]
    [IsStrictHenselizationOf (X.presheaf.stalk x) Ash] : ℕ∞ :=
  geometricBranchNumber (X.presheaf.stalk x) Ash

/-- The scheme-level geometric branch number is the geometric branch number
of the stalk. -/
@[simp, stacks 0C38 "geometric branch number at a scheme point definition"]
theorem geometricBranchNumberAt_def
    (x : X) (Ash : Type v) [CommRing Ash] [Algebra (X.presheaf.stalk x) Ash]
    [IsStrictHenselizationOf (X.presheaf.stalk x) Ash] :
    X.geometricBranchNumberAt x Ash =
      geometricBranchNumber (X.presheaf.stalk x) Ash := sorry

/-- The geometric branch number at a scheme point is the number of minimal
primes of its chosen strict henselization. -/
@[simp, stacks 0C38 "geometric branch number as minimal-prime cardinality"]
theorem geometricBranchNumberAt_eq_encard_minimalPrimes
    (x : X) (Ash : Type v) [CommRing Ash] [Algebra (X.presheaf.stalk x) Ash]
    [IsStrictHenselizationOf (X.presheaf.stalk x) Ash] :
    X.geometricBranchNumberAt x Ash = (minimalPrimes Ash).encard := sorry

end AlgebraicGeometry.Scheme
