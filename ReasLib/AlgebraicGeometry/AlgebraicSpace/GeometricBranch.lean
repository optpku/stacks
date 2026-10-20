/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalRing

/-!
# Geometric branch numbers of algebraic spaces

The geometric branch number at a point counts the minimal primes of the étale
local ring at a geometric representative of that point.
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
  rfl

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

/-- The number of geometric branches at an ordinary point is the number of minimal
primes of the étale local ring at its algebraic-closure geometric representative. -/
noncomputable def geometricBranchNumber {S : Scheme.{u}} (X : AlgebraicSpace S)
    (x : Points X) : ℕ∞ :=
  X.geometricBranchNumberAt (geometricPointOver x)

/-- The geometric branch number at an ordinary point agrees with the count at every
geometric point lying over it. -/
theorem geometricBranchNumber_eq_geometricBranchNumberAt {S : Scheme.{u}}
    {X : AlgebraicSpace S} (x : Points X) (xbar : GeometricPoint X)
    (h : xbar.liesOver x) :
    X.geometricBranchNumber x = X.geometricBranchNumberAt xbar :=
  sorry

/-- The geometric branch number at a point of an algebraic space is nonzero. -/
theorem geometricBranchNumber_ne_zero {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) : X.geometricBranchNumber x ≠ 0 :=
  sorry

/-- For a positive integer `n`, the geometric branch number at an ordinary point is `n`
if and only if every geometric representative has exactly `n` minimal primes in its
étale local ring. -/
theorem geometricBranchNumber_eq_nat_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) {n : ℕ} (hn : 0 < n) :
    X.geometricBranchNumber x = n ↔
      ∀ ybar : GeometricPoint X, ybar.liesOver x →
        (minimalPrimes (etaleLocalRing X ybar)).encard = n :=
  sorry

/-- The geometric branch number is infinite precisely when there is no positive finite
number equal to the minimal-prime count at every geometric representative. -/
theorem geometricBranchNumber_eq_top_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) :
    X.geometricBranchNumber x = ⊤ ↔
      ¬ ∃ n : ℕ, 0 < n ∧ ∀ ybar : GeometricPoint X, ybar.liesOver x →
        (minimalPrimes (etaleLocalRing X ybar)).encard = n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
