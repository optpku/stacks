/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Branch
public import ReasLib.Topology.IrreducibleComponents.AtPoint
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# Finite numbers of geometric branches of algebraic spaces

For an algebraic space and a point, a finite positive count of minimal primes of the
étale local ring is equivalent to bound-and-attainment counts on étale scheme charts,
and to every such chart having that many geometric branches.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The stalk of the structure sheaf of a scheme at a point. -/
noncomputable abbrev schemeStalk (Y : Scheme.{u}) (y : Y) := Y.presheaf.stalk y

/-- `schemeStalk Y y` is the stalk of the structure sheaf of `Y` at `y`. -/
theorem schemeStalk_eq (Y : Scheme.{u}) (y : Y) :
    schemeStalk Y y = Y.presheaf.stalk y :=
  sorry

/-- The number of minimal primes of the local ring of every étale scheme chart of `X` through
`x` is at most `n`, and equals `n` for some such chart. -/
def stalkMinimalPrimesBoundAttained {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) : Prop :=
  (∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
      Etale a → Points.mapOfOver a u = x →
        (minimalPrimes (schemeStalk U.left u)).encard ≤ n) ∧
    ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
      Etale a ∧ Points.mapOfOver a u = x ∧
        (minimalPrimes (schemeStalk U.left u)).encard = n

/-- `stalkMinimalPrimesBoundAttained x n` is the bound-and-attainment condition on the number of
minimal primes of stalks of étale scheme charts through `x`. -/
theorem stalkMinimalPrimesBoundAttained_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) :
    stalkMinimalPrimesBoundAttained x n ↔
      (∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
          Etale a → Points.mapOfOver a u = x →
            (minimalPrimes (schemeStalk U.left u)).encard ≤ n) ∧
        ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
          Etale a ∧ Points.mapOfOver a u = x ∧
            (minimalPrimes (schemeStalk U.left u)).encard = n :=
  sorry

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
  sorry

/-- The number of branches of every étale scheme chart of `X` through `x` is at most `n`, and
equals `n` for some such chart. -/
def branchNumberBoundAttained {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) : Prop :=
  (∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
      Etale a → Points.mapOfOver a u = x →
        ∀ (Ah : Type u) [CommRing Ah] [Algebra (schemeStalk U.left u) Ah]
          [IsHenselizationOf (schemeStalk U.left u) Ah],
          U.left.branchNumberAt u Ah ≤ n) ∧
    ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
      Etale a ∧ Points.mapOfOver a u = x ∧
        ∀ (Ah : Type u) [CommRing Ah] [Algebra (schemeStalk U.left u) Ah]
          [IsHenselizationOf (schemeStalk U.left u) Ah],
          U.left.branchNumberAt u Ah = n

/-- `branchNumberBoundAttained x n` is the bound-and-attainment condition on scheme-level branch
numbers of étale charts through `x`. -/
theorem branchNumberBoundAttained_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) :
    branchNumberBoundAttained x n ↔
      (∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
          Etale a → Points.mapOfOver a u = x →
            ∀ (Ah : Type u) [CommRing Ah] [Algebra (schemeStalk U.left u) Ah]
              [IsHenselizationOf (schemeStalk U.left u) Ah],
              U.left.branchNumberAt u Ah ≤ n) ∧
        ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
          Etale a ∧ Points.mapOfOver a u = x ∧
            ∀ (Ah : Type u) [CommRing Ah] [Algebra (schemeStalk U.left u) Ah]
              [IsHenselizationOf (schemeStalk U.left u) Ah],
              U.left.branchNumberAt u Ah = n :=
  sorry

/-- Every étale scheme chart of `X` through `x` has exactly `n` geometric branches at the selected
point. -/
def geometricBranchNumberEq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) : Prop :=
  ∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
    Etale a → Points.mapOfOver a u = x →
      ∀ (Ash : Type u) [CommRing Ash] [Algebra (schemeStalk U.left u) Ash]
        [IsStrictHenselizationOf (schemeStalk U.left u) Ash],
        U.left.geometricBranchNumberAt u Ash = n

/-- `geometricBranchNumberEq x n` means every étale scheme chart through `x` has geometric branch
number `n`. -/
theorem geometricBranchNumberEq_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) :
    geometricBranchNumberEq x n ↔
      ∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
        Etale a → Points.mapOfOver a u = x →
          ∀ (Ash : Type u) [CommRing Ash] [Algebra (schemeStalk U.left u) Ash]
            [IsStrictHenselizationOf (schemeStalk U.left u) Ash],
            U.left.geometricBranchNumberAt u Ash = n :=
  sorry

/-- Every geometric point of `X` lying over `x` has exactly `n` minimal primes in the étale
local ring. -/
def etaleLocalRing_encard_minimalPrimes_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) : Prop :=
  ∀ xbar : GeometricPoint X, xbar.liesOver x →
    (minimalPrimes (etaleLocalRing X xbar)).encard = n

/-- `etaleLocalRing_encard_minimalPrimes_eq x n` means the étale local ring at every geometric
point over `x` has exactly `n` minimal primes. -/
theorem etaleLocalRing_encard_minimalPrimes_eq_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) :
    etaleLocalRing_encard_minimalPrimes_eq x n ↔
      ∀ xbar : GeometricPoint X, xbar.liesOver x →
        (minimalPrimes (etaleLocalRing X xbar)).encard = n :=
  sorry

/-- Lemma 66.23.3: let `S` be a scheme, let `X` be an algebraic space over `S`, let `x` be a
point of `|X|`, and let `n` be a positive integer. The following are equivalent: every étale
scheme chart through `x` has at most `n` minimal primes in the stalk, and some chart attains
`n`; the same bound-and-attainment for irreducible components through the selected point; the
same for the number of branches of the chart; every such chart has exactly `n` geometric
branches; and every geometric point over `x` has exactly `n` minimal primes in
`etaleLocalRing X xbar`. -/
@[stacks 0DQ3]
theorem etaleLocalRing_encard_minimalPrimes_tfae {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) (n : ℕ) (hn : 0 < n) :
    List.TFAE
      [stalkMinimalPrimesBoundAttained x n, irreducibleComponentsBoundAttained x n,
        branchNumberBoundAttained x n, geometricBranchNumberEq x n,
        etaleLocalRing_encard_minimalPrimes_eq x n] :=
  sorry

/-- The étale local ring at every geometric point over `x` has exactly `n` minimal primes if and
only if some geometric point over `x` has this count. -/
theorem etaleLocalRing_encard_minimalPrimes_eq_iff_exists {S : Scheme.{u}}
    {X : AlgebraicSpace S} (x : Points X) (n : ℕ) :
    etaleLocalRing_encard_minimalPrimes_eq x n ↔
      ∃ xbar : GeometricPoint X, xbar.liesOver x ∧
        (minimalPrimes (etaleLocalRing X xbar)).encard = n :=
  sorry

/-- The étale-local-ring count equals `n` if and only if étale scheme charts through `x` satisfy
the bound-and-attainment condition on stalk minimal primes. -/
theorem etaleLocalRing_encard_minimalPrimes_eq_iff_stalkMinimalPrimes
    {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) (n : ℕ) (hn : 0 < n) :
    etaleLocalRing_encard_minimalPrimes_eq x n ↔ stalkMinimalPrimesBoundAttained x n :=
  sorry

/-- The étale-local-ring count equals `n` if and only if étale scheme charts through `x` satisfy
the bound-and-attainment condition on irreducible components. -/
theorem etaleLocalRing_encard_minimalPrimes_eq_iff_irreducibleComponents
    {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) (n : ℕ) (hn : 0 < n) :
    etaleLocalRing_encard_minimalPrimes_eq x n ↔ irreducibleComponentsBoundAttained x n :=
  sorry

/-- The étale-local-ring count equals `n` if and only if étale scheme charts through `x` satisfy
the bound-and-attainment condition on branch numbers. -/
theorem etaleLocalRing_encard_minimalPrimes_eq_iff_branchNumber
    {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) (n : ℕ) (hn : 0 < n) :
    etaleLocalRing_encard_minimalPrimes_eq x n ↔ branchNumberBoundAttained x n :=
  sorry

/-- The étale-local-ring count equals `n` if and only if every étale scheme chart through `x`
has geometric branch number `n`. -/
theorem etaleLocalRing_encard_minimalPrimes_eq_iff_geometricBranchNumber
    {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) (n : ℕ) (hn : 0 < n) :
    etaleLocalRing_encard_minimalPrimes_eq x n ↔ geometricBranchNumberEq x n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
