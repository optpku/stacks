/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Instances.ENat
public import ReasLib.AlgebraicGeometry.Scheme.Branch
public import ReasLib.RingTheory.LocalRing.MinimalPrime

/-!
# Branch numbers and minimal primes

This file decomposes the branch numbers at a scheme point into the branch
numbers of the quotients of its local ring by minimal prime ideals.
-/

@[expose] public section

open AlgebraicGeometry
open scoped BigOperators

universe u v w

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (x : X)

/-- The branch number at a scheme point is the sum of the branch numbers of
the stalk quotients by its minimal prime ideals. -/
theorem branchNumberAt_eq_tsum_quotient_minimalPrimes
    (Ah : Type v) [CommRing Ah] [Algebra (X.presheaf.stalk x) Ah]
    [IsHenselizationOf (X.presheaf.stalk x) Ah]
    (Ahp : minimalPrimes (X.presheaf.stalk x) → Type w)
    [∀ p, CommRing (Ahp p)]
    [∀ p, Algebra ((X.presheaf.stalk x) ⧸ p.1) (Ahp p)]
    [∀ p, IsHenselizationOf ((X.presheaf.stalk x) ⧸ p.1) (Ahp p)] :
    X.branchNumberAt x Ah =
      ∑' p : minimalPrimes (X.presheaf.stalk x),
        branchNumber ((X.presheaf.stalk x) ⧸ p.1) (Ahp p) := sorry

/-- The geometric branch number at a scheme point is the sum of the geometric
branch numbers of the stalk quotients by its minimal prime ideals. -/
theorem geometricBranchNumberAt_eq_tsum_quotient_minimalPrimes
    (Ash : Type v) [CommRing Ash] [Algebra (X.presheaf.stalk x) Ash]
    [IsStrictHenselizationOf (X.presheaf.stalk x) Ash]
    (Ashp : minimalPrimes (X.presheaf.stalk x) → Type w)
    [∀ p, CommRing (Ashp p)]
    [∀ p, Algebra ((X.presheaf.stalk x) ⧸ p.1) (Ashp p)]
    [∀ p, IsStrictHenselizationOf ((X.presheaf.stalk x) ⧸ p.1) (Ashp p)] :
    X.geometricBranchNumberAt x Ash =
      ∑' p : minimalPrimes (X.presheaf.stalk x),
        geometricBranchNumber ((X.presheaf.stalk x) ⧸ p.1) (Ashp p) := sorry

end AlgebraicGeometry.Scheme
