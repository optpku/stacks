/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Branch
import StacksCheckRecall

/-!
# Finite numbers of branches of decent algebraic spaces

The finite branch-count equivalences and the supporting cardinality statements
are provided by their shared mathematical owners.
-/

universe u

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

/- Lemma 68.24.3 (1): Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x : Points X`. Let `n : ℕ` with `0 < n`. The number of minimal primes of
`henselianLocalRing X x` is `n` if and only if for every elementary étale
neighbourhood `U : EtaleNeighborhood.Elementary X x` the number of minimal primes of
`U.obj.scheme.presheaf.stalk U.obj.point` is `≤ n`, and for at least one such neighbourhood it is `n`. -/
@[stacks 0DQ8]
#check (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing.encard_minimalPrimes_iff_elementary_minimalPrimes :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X)
    (n : ℕ) (hn : 0 < n),
    (minimalPrimes (henselianLocalRing X x)).encard = n ↔
      (∀ U : EtaleNeighborhood.Elementary X x,
          (minimalPrimes (U.obj.scheme.presheaf.stalk U.obj.point)).encard ≤ n) ∧
        ∃ U : EtaleNeighborhood.Elementary X x,
          (minimalPrimes (U.obj.scheme.presheaf.stalk U.obj.point)).encard = n)

/- Lemma 68.24.3 (2): Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x : Points X`. Let `n : ℕ` with `0 < n`. The number of minimal primes of
`henselianLocalRing X x` is `n` if and only if for every elementary étale
neighbourhood `U : EtaleNeighborhood.Elementary X x` the number of irreducible
components of `U` through `U.obj.point` is `≤ n`, and for at least one such
neighbourhood it is `n`. -/
@[stacks 0DQ8]
#check (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing.encard_minimalPrimes_iff_elementary_irreducibleComponents :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X)
    (n : ℕ) (hn : 0 < n),
    (minimalPrimes (henselianLocalRing X x)).encard = n ↔
      (∀ U : EtaleNeighborhood.Elementary X x,
          (irreducibleComponentsAt U.obj.point).encard ≤ n) ∧
        ∃ U : EtaleNeighborhood.Elementary X x,
          (irreducibleComponentsAt U.obj.point).encard = n)

/- Lemma 68.24.3 (3): Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x : Points X`. Let `n : ℕ` with `0 < n`. The number of minimal primes of
`henselianLocalRing X x` is `n` if and only if for every elementary étale
neighbourhood `U : EtaleNeighborhood.Elementary X x` the number of branches of
`U.obj.scheme` at `U.obj.point` is `≤ n`, and for at least one such neighbourhood
it is `n`. -/
@[stacks 0DQ8]
#check (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing.encard_minimalPrimes_iff_elementary_branchNumber :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X)
    (n : ℕ) (hn : 0 < n),
    (minimalPrimes (henselianLocalRing X x)).encard = n ↔
      (∀ (U : EtaleNeighborhood.Elementary X x) (Ah : Type u)
          [CommRing Ah]
          [Algebra (U.obj.scheme.presheaf.stalk U.obj.point) Ah]
          [IsHenselizationOf (U.obj.scheme.presheaf.stalk U.obj.point) Ah],
        U.obj.scheme.branchNumberAt U.obj.point Ah ≤ n) ∧
      ∃ U : EtaleNeighborhood.Elementary X x,
        ∀ (Ah : Type u) [CommRing Ah]
          [Algebra (U.obj.scheme.presheaf.stalk U.obj.point) Ah]
          [IsHenselizationOf (U.obj.scheme.presheaf.stalk U.obj.point) Ah],
          U.obj.scheme.branchNumberAt U.obj.point Ah = n)

#check (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing.encard_minimalPrimes_eq_iSup_elementary_minimalPrimes :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X),
    (minimalPrimes (henselianLocalRing X x)).encard =
      ⨆ U : EtaleNeighborhood.Elementary X x,
        (minimalPrimes (U.obj.scheme.presheaf.stalk U.obj.point)).encard)

#check (AlgebraicGeometry.Scheme.encard_minimalPrimes_stalk_eq_irreducibleComponentsAt :
  ∀ (X : Scheme.{u}) (x : X),
    (minimalPrimes (X.presheaf.stalk x)).encard =
      (TopologicalSpace.irreducibleComponentsAt x).encard)
