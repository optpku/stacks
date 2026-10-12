/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Branch
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.Topology.IrreducibleComponents.AtPoint
public import stacks_project.Chap68.Definition_68_11_7_HenselianLocalRing

/-!
# Finite numbers of branches of decent algebraic spaces

On a decent algebraic space, a finite positive count of minimal primes of the
henselian local ring at a point is equivalent to the same bound-and-attainment
count for minimal primes of stalks, irreducible components through selected
points, and scheme-level branch numbers of elementary étale neighbourhoods.
-/

@[expose] public section

universe u

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

namespace AlgebraicGeometry.AlgebraicSpace

namespace EtaleNeighborhood

/-- The local ring of an étale neighbourhood at its selected point. -/
noncomputable abbrev stalk {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (U : EtaleNeighborhood X x) :=
  U.scheme.presheaf.stalk U.point

/-- The local ring of an étale neighbourhood is the stalk of its structure sheaf at the
selected point. -/
theorem stalk_def {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (U : EtaleNeighborhood X x) :
    U.stalk = U.scheme.presheaf.stalk U.point :=
  sorry

end EtaleNeighborhood

/-- Lemma 68.24.3 (1): Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x : Points X`. Let `n : ℕ` with `0 < n`. The number of minimal primes of
`henselianLocalRing X x` is `n` if and only if for every elementary étale
neighbourhood `U : EtaleNeighborhood.Elementary X x` the number of minimal primes of
`U.obj.stalk` is `≤ n`, and for at least one such neighbourhood it is `n`. -/
@[stacks 0DQ8]
theorem henselianLocalRing.encard_minimalPrimes_iff_elementary_minimalPrimes
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X)
    (n : ℕ) (hn : 0 < n) :
    (minimalPrimes (henselianLocalRing X x)).encard = n ↔
      (∀ U : EtaleNeighborhood.Elementary X x,
          (minimalPrimes (U.obj.stalk)).encard ≤ n) ∧
        ∃ U : EtaleNeighborhood.Elementary X x,
          (minimalPrimes (U.obj.stalk)).encard = n :=
  sorry

/-- Lemma 68.24.3 (2): Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x : Points X`. Let `n : ℕ` with `0 < n`. The number of minimal primes of
`henselianLocalRing X x` is `n` if and only if for every elementary étale
neighbourhood `U : EtaleNeighborhood.Elementary X x` the number of irreducible
components of `U` through `U.obj.point` is `≤ n`, and for at least one such
neighbourhood it is `n`. -/
@[stacks 0DQ8]
theorem henselianLocalRing.encard_minimalPrimes_iff_elementary_irreducibleComponents
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X)
    (n : ℕ) (hn : 0 < n) :
    (minimalPrimes (henselianLocalRing X x)).encard = n ↔
      (∀ U : EtaleNeighborhood.Elementary X x,
          (irreducibleComponentsAt U.obj.point).encard ≤ n) ∧
        ∃ U : EtaleNeighborhood.Elementary X x,
          (irreducibleComponentsAt U.obj.point).encard = n :=
  sorry

/-- Lemma 68.24.3 (3): Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x : Points X`. Let `n : ℕ` with `0 < n`. The number of minimal primes of
`henselianLocalRing X x` is `n` if and only if for every elementary étale
neighbourhood `U : EtaleNeighborhood.Elementary X x` the number of branches of
`U.obj.scheme` at `U.obj.point` is `≤ n`, and for at least one such neighbourhood
it is `n`. -/
@[stacks 0DQ8]
theorem henselianLocalRing.encard_minimalPrimes_iff_elementary_branchNumber
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X)
    (n : ℕ) (hn : 0 < n) :
    (minimalPrimes (henselianLocalRing X x)).encard = n ↔
      (∀ (U : EtaleNeighborhood.Elementary X x) (Ah : Type u)
          [CommRing Ah]
          [Algebra (U.obj.stalk) Ah]
          [IsHenselizationOf (U.obj.stalk) Ah],
        U.obj.scheme.branchNumberAt U.obj.point Ah ≤ n) ∧
      ∃ U : EtaleNeighborhood.Elementary X x,
        ∀ (Ah : Type u) [CommRing Ah]
          [Algebra (U.obj.stalk) Ah]
          [IsHenselizationOf (U.obj.stalk) Ah],
          U.obj.scheme.branchNumberAt U.obj.point Ah = n :=
  sorry

/-- The number of minimal primes of `henselianLocalRing X x` is the supremum of the
numbers of minimal primes of the local rings of elementary étale neighbourhoods of
`(X, x)`. -/
theorem henselianLocalRing.encard_minimalPrimes_eq_iSup_elementary_minimalPrimes
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X) :
    (minimalPrimes (henselianLocalRing X x)).encard =
      ⨆ U : EtaleNeighborhood.Elementary X x,
        (minimalPrimes (U.obj.stalk)).encard :=
  sorry

/-- The number of minimal primes of the local ring of an elementary étale
neighbourhood at its selected point equals the number of irreducible components
through that point. -/
theorem EtaleNeighborhood.Elementary.encard_minimalPrimes_eq_irreducibleComponentsAt
    {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (U : EtaleNeighborhood.Elementary X x) :
    (minimalPrimes (U.obj.stalk)).encard =
      (irreducibleComponentsAt U.obj.point).encard :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
