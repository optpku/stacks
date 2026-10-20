module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Branch
public import ReasLib.AlgebraicGeometry.Scheme.IrreducibleComponents.AtPoint

/-!
# Branch counts of decent algebraic spaces

Minimal primes of henselian local rings are counted by elementary étale
neighbourhood stalks, irreducible components, and scheme branch numbers.
-/

@[expose] public section

universe u

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

namespace AlgebraicGeometry.AlgebraicSpace

/-- The number of minimal primes of the henselian local ring of a decent algebraic
space is the supremum of the minimal-prime counts of its elementary étale
neighbourhood stalks. -/
theorem henselianLocalRing.encard_minimalPrimes_eq_iSup_elementary_minimalPrimes
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X) :
    (minimalPrimes (henselianLocalRing X x)).encard =
      ⨆ U : EtaleNeighborhood.Elementary X x,
        (minimalPrimes (U.obj.scheme.presheaf.stalk U.obj.point)).encard :=
  sorry

/-- The henselian local ring of a decent algebraic space has exactly `n` minimal primes,
for positive `n`, if and only if every elementary étale neighbourhood stalk has at most
`n` minimal primes and some such stalk has exactly `n`. -/
theorem henselianLocalRing.encard_minimalPrimes_iff_elementary_minimalPrimes
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X)
    (n : ℕ) (hn : 0 < n) :
    (minimalPrimes (henselianLocalRing X x)).encard = n ↔
      (∀ U : EtaleNeighborhood.Elementary X x,
          (minimalPrimes (U.obj.scheme.presheaf.stalk U.obj.point)).encard ≤ n) ∧
        ∃ U : EtaleNeighborhood.Elementary X x,
          (minimalPrimes (U.obj.scheme.presheaf.stalk U.obj.point)).encard = n :=
  sorry

/-- The henselian local ring of a decent algebraic space has exactly `n` minimal primes,
for positive `n`, if and only if every elementary étale neighbourhood has at most `n`
irreducible components through its selected point and some neighbourhood attains `n`. -/
theorem henselianLocalRing.encard_minimalPrimes_iff_elementary_irreducibleComponents
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X)
    (n : ℕ) (hn : 0 < n) :
    (minimalPrimes (henselianLocalRing X x)).encard = n ↔
      (∀ U : EtaleNeighborhood.Elementary X x,
          (irreducibleComponentsAt U.obj.point).encard ≤ n) ∧
        ∃ U : EtaleNeighborhood.Elementary X x,
          (irreducibleComponentsAt U.obj.point).encard = n :=
  sorry

/-- The henselian local ring of a decent algebraic space has exactly `n` minimal primes,
for positive `n`, if and only if the branch numbers of all elementary étale
neighbourhoods are at most `n` and some neighbourhood has branch number `n`,
independently of the chosen henselization of its stalk. -/
theorem henselianLocalRing.encard_minimalPrimes_iff_elementary_branchNumber
    {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X)
    (n : ℕ) (hn : 0 < n) :
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
          U.obj.scheme.branchNumberAt U.obj.point Ah = n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
