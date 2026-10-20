/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricBranch
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.Scheme.Branch
public import ReasLib.Topology.IrreducibleComponents.AtPoint

/-!
# Étale-chart characterizations of finite geometric branch numbers

A positive finite geometric branch number is characterized by bounded and attained counts
of stalk minimal primes, irreducible components, or branches on étale scheme charts, and by
a constant geometric branch count on those charts.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The number of minimal primes of the local ring of every étale scheme chart of `X` through
`x` is at most `n`, and equals `n` for some such chart. -/
def stalkMinimalPrimesBoundAttained {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) : Prop :=
  (∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
      Etale a → Points.mapOfOver a u = x →
        (minimalPrimes (U.left.presheaf.stalk u)).encard ≤ n) ∧
    ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
      Etale a ∧ Points.mapOfOver a u = x ∧
        (minimalPrimes (U.left.presheaf.stalk u)).encard = n

/-- `stalkMinimalPrimesBoundAttained x n` is the bound-and-attainment condition on the number of
minimal primes of stalks of étale scheme charts through `x`. -/
theorem stalkMinimalPrimesBoundAttained_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) :
    stalkMinimalPrimesBoundAttained x n ↔
      (∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
          Etale a → Points.mapOfOver a u = x →
            (minimalPrimes (U.left.presheaf.stalk u)).encard ≤ n) ∧
        ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
          Etale a ∧ Points.mapOfOver a u = x ∧
            (minimalPrimes (U.left.presheaf.stalk u)).encard = n :=
  Iff.rfl

/-- The number of irreducible components through the selected point of every étale scheme chart
of `X` through `x` is at most `n`, and equals `n` for some such chart. -/
def irreducibleComponentsBoundAttained {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) : Prop :=
  (∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
      Etale a → Points.mapOfOver a u = x →
        (irreducibleComponentsAt u).encard ≤ n) ∧
    ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
      Etale a ∧ Points.mapOfOver a u = x ∧
        (irreducibleComponentsAt u).encard = n

/-- `irreducibleComponentsBoundAttained x n` is the bound-and-attainment condition on irreducible
components of étale scheme charts through `x`. -/
theorem irreducibleComponentsBoundAttained_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) :
    irreducibleComponentsBoundAttained x n ↔
      (∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
          Etale a → Points.mapOfOver a u = x →
            (irreducibleComponentsAt u).encard ≤ n) ∧
        ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
          Etale a ∧ Points.mapOfOver a u = x ∧
            (irreducibleComponentsAt u).encard = n :=
  Iff.rfl

/-- The number of branches of every étale scheme chart of `X` through `x` is at most `n`, and
equals `n` for some such chart. -/
def branchNumberBoundAttained {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) : Prop :=
  (∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
      Etale a → Points.mapOfOver a u = x →
        ∀ (Ah : Type u) [CommRing Ah] [Algebra (U.left.presheaf.stalk u) Ah]
          [IsHenselizationOf (U.left.presheaf.stalk u) Ah],
          U.left.branchNumberAt u Ah ≤ n) ∧
    ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
      Etale a ∧ Points.mapOfOver a u = x ∧
        ∀ (Ah : Type u) [CommRing Ah] [Algebra (U.left.presheaf.stalk u) Ah]
          [IsHenselizationOf (U.left.presheaf.stalk u) Ah],
          U.left.branchNumberAt u Ah = n

/-- `branchNumberBoundAttained x n` is the bound-and-attainment condition on scheme-level branch
numbers of étale charts through `x`. -/
theorem branchNumberBoundAttained_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) :
    branchNumberBoundAttained x n ↔
      (∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
          Etale a → Points.mapOfOver a u = x →
            ∀ (Ah : Type u) [CommRing Ah] [Algebra (U.left.presheaf.stalk u) Ah]
              [IsHenselizationOf (U.left.presheaf.stalk u) Ah],
              U.left.branchNumberAt u Ah ≤ n) ∧
        ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
          Etale a ∧ Points.mapOfOver a u = x ∧
            ∀ (Ah : Type u) [CommRing Ah] [Algebra (U.left.presheaf.stalk u) Ah]
              [IsHenselizationOf (U.left.presheaf.stalk u) Ah],
              U.left.branchNumberAt u Ah = n :=
  Iff.rfl

/-- Every étale scheme chart of `X` through `x` has exactly `n` geometric branches at the selected
point. -/
def geometricBranchNumberEq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) : Prop :=
  ∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
    Etale a → Points.mapOfOver a u = x →
      ∀ (Ash : Type u) [CommRing Ash] [Algebra (U.left.presheaf.stalk u) Ash]
        [IsStrictHenselizationOf (U.left.presheaf.stalk u) Ash],
        U.left.geometricBranchNumberAt u Ash = n

/-- `geometricBranchNumberEq x n` means every étale scheme chart through `x` has geometric branch
number `n`. -/
theorem geometricBranchNumberEq_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) :
    geometricBranchNumberEq x n ↔
      ∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
        Etale a → Points.mapOfOver a u = x →
          ∀ (Ash : Type u) [CommRing Ash] [Algebra (U.left.presheaf.stalk u) Ash]
            [IsStrictHenselizationOf (U.left.presheaf.stalk u) Ash],
            U.left.geometricBranchNumberAt u Ash = n :=
  Iff.rfl

/-- For a positive integer, the geometric branch number equals that integer precisely when
étale scheme charts satisfy the equivalent stalk, component, branch, or geometric branch
count conditions. -/
theorem geometricBranchNumber_eq_nat_tfae {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) (hn : 0 < n) :
    List.TFAE
      [stalkMinimalPrimesBoundAttained x n, irreducibleComponentsBoundAttained x n,
        branchNumberBoundAttained x n, geometricBranchNumberEq x n,
        X.geometricBranchNumber x = n] :=
  sorry

/-- The geometric branch number at a point equals a natural number if and only if some
geometric point over it has that many minimal primes in its étale local ring. -/
theorem geometricBranchNumber_eq_nat_iff_exists {S : Scheme.{u}}
    {X : AlgebraicSpace S} (x : Points X) (n : ℕ) :
    X.geometricBranchNumber x = n ↔
      ∃ xbar : GeometricPoint X, xbar.liesOver x ∧
        (minimalPrimes (etaleLocalRing X xbar)).encard = n :=
  sorry

/-- The geometric branch number equals `n` if and only if étale scheme charts through `x` satisfy
the bound-and-attainment condition on stalk minimal primes. -/
theorem geometricBranchNumber_eq_nat_iff_stalkMinimalPrimes
    {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) (n : ℕ) (hn : 0 < n) :
    X.geometricBranchNumber x = n ↔ stalkMinimalPrimesBoundAttained x n :=
  sorry

/-- The geometric branch number equals `n` if and only if étale scheme charts through `x` satisfy
the bound-and-attainment condition on irreducible components. -/
theorem geometricBranchNumber_eq_nat_iff_irreducibleComponents
    {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) (n : ℕ) (hn : 0 < n) :
    X.geometricBranchNumber x = n ↔ irreducibleComponentsBoundAttained x n :=
  sorry

/-- The geometric branch number equals `n` if and only if étale scheme charts through `x` satisfy
the bound-and-attainment condition on branch numbers. -/
theorem geometricBranchNumber_eq_nat_iff_branchNumber
    {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) (n : ℕ) (hn : 0 < n) :
    X.geometricBranchNumber x = n ↔ branchNumberBoundAttained x n :=
  sorry

/-- The geometric branch number equals `n` if and only if every étale scheme chart through `x`
has geometric branch number `n`. -/
theorem geometricBranchNumber_eq_nat_iff_geometricBranchNumber
    {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) (n : ℕ) (hn : 0 < n) :
    X.geometricBranchNumber x = n ↔ geometricBranchNumberEq x n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
