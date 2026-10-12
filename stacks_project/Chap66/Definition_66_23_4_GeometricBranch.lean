/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing

/-!
# Geometric branch numbers of algebraic spaces

The number of geometric branches of an algebraic space at a geometric point is the
number of minimal primes of its étale local ring.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The number of geometric branches of an algebraic space `X` at a geometric point `xbar`
is the number of minimal primes of the étale local ring `etaleLocalRing X xbar`. -/
noncomputable abbrev geometricBranchNumberAt {S : Scheme.{u}} (X : AlgebraicSpace S)
    (xbar : GeometricPoint X) : ℕ∞ :=
  (minimalPrimes (etaleLocalRing X xbar)).encard

/-- The geometric branch number at a geometric point is the cardinality of the set of
minimal primes of the étale local ring. -/
@[simp]
theorem geometricBranchNumberAt_eq_encard_minimalPrimes {S : Scheme.{u}}
    (X : AlgebraicSpace S) (xbar : GeometricPoint X) :
    X.geometricBranchNumberAt xbar = (minimalPrimes (etaleLocalRing X xbar)).encard :=
  sorry

/-- The geometric branch number depends only on the image point in `|X|`. -/
theorem geometricBranchNumberAt_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {xbar ybar : GeometricPoint X} (h : xbar.image = ybar.image) :
    X.geometricBranchNumberAt xbar = X.geometricBranchNumberAt ybar :=
  sorry

/-- On a scheme over `S`, viewed as an algebraic space, the geometric branch number is the
number of minimal primes of the scheme-theoretic étale local ring. -/
theorem geometricBranchNumberAt_ofOver {S : Scheme.{u}} {U : Over S}
    (p : GeometricPoint (ofOver U)) :
    geometricBranchNumberAt (ofOver U) p =
      (minimalPrimes (Scheme.etaleLocalRing U.left p.toScheme)).encard :=
  sorry

/-- For a positive integer `n`, the geometric branch number at `xbar` is `n` if and only if
every geometric point over the same image has exactly `n` minimal primes in its étale
local ring. -/
theorem geometricBranchNumberAt_eq_nat_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) {n : ℕ} (hn : 0 < n) :
    X.geometricBranchNumberAt xbar = n ↔
      ∀ ybar : GeometricPoint X, ybar.liesOver xbar.image →
        (minimalPrimes (etaleLocalRing X ybar)).encard = n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
