/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Defs

/-!
# Branch numbers of decent algebraic spaces

The number of branches of a decent algebraic space at a point is the number of
minimal primes of its henselian local ring, as an extended natural number.
-/

@[expose] public section

universe u

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- The number of branches of a decent algebraic space `X` at a point `x` is the
number of minimal primes of `henselianLocalRing X x`, as an extended natural
number. -/
abbrev branchNumberAt {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) : ℕ∞ :=
  (minimalPrimes (henselianLocalRing X x)).encard

/-- The number of branches of `X` at `x` equals the `encard` of the set of
minimal primes of `henselianLocalRing X x`. -/
theorem branchNumberAt_def {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) :
    X.branchNumberAt x = (minimalPrimes (henselianLocalRing X x)).encard :=
  sorry

/-- For `0 < n`, the number of branches of `X` at `x` equals `n` if and only if
every elementary étale neighbourhood of `(X, x)` has at most `n` minimal primes
in its local ring at the selected point, and some such neighbourhood attains
`n`. -/
theorem branchNumberAt_eq_nat_iff {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] (x : Points X) {n : ℕ} (hn : 0 < n) :
    X.branchNumberAt x = n ↔
      (∀ U : EtaleNeighborhood.Elementary X x,
          (minimalPrimes (U.obj.scheme.presheaf.stalk U.obj.point)).encard ≤ n) ∧
        ∃ U : EtaleNeighborhood.Elementary X x,
          (minimalPrimes (U.obj.scheme.presheaf.stalk U.obj.point)).encard = n :=
  sorry

/-- The number of branches of `X` at `x` is the supremum of the numbers of
minimal primes of the local rings of elementary étale neighbourhoods of
`(X, x)`. -/
theorem branchNumberAt_eq_iSup_elementary_minimalPrimes
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X) :
    X.branchNumberAt x =
      ⨆ U : EtaleNeighborhood.Elementary X x,
        (minimalPrimes (U.obj.scheme.presheaf.stalk U.obj.point)).encard :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
