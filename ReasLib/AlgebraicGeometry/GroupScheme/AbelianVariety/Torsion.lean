/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Etale
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Surjective
public import ReasLib.AlgebraicGeometry.GroupScheme.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PointsOver

/-!
# Torsion of abelian varieties

This module records finiteness, étaleness, and rational-point classification
results for torsion on abelian varieties.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj AbelianVariety

universe u

namespace AlgebraicGeometry.AbelianVariety

/-- Over a field of characteristic `p`, the set-theoretic fibre of multiplication by the
prime `p` on an abelian variety over the identity point has extended cardinality at most
`p ^ dimension A`. -/
theorem mulBy_fiber_zero_encard_le {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (A : SchemeOverField k) [GrpObj A] [AbelianVariety A] :
    (([p]ₐ A).pointsOver (η[A].left (IsLocalRing.closedPoint k))).encard ≤
      p ^ dimension A := sorry

variable {k : Type u} [Field k] (A : SchemeOverField k) [GrpObj A] [AbelianVariety A]

/-- The `n`-torsion group scheme of an abelian variety is finite locally free of rank
`n ^ (2 * dimension A)` when `n` is nonzero. -/
instance instTorsionFiniteLocallyFreeOfRank (n : ℕ) [NeZero n] :
    IsFiniteLocallyFreeOfRank (SchemeOverField.torsionGroupScheme A n).X.hom
      (n ^ (2 * dimension A)) := sorry

/-- For a positive-dimensional abelian variety, its `n`-torsion group scheme is étale over
the base field exactly when `n` is a unit in that field. -/
theorem torsion_etale_iff (hA : 0 < dimension A) (n : ℕ) [NeZero n] :
    Etale (SchemeOverField.torsionGroupScheme A n).X.hom ↔ IsUnit (n : k) := sorry

/-- Over an algebraically closed field, the prime-to-characteristic rational `n`-torsion of
an abelian variety is additively equivalent to `2 * dimension A` copies of `ZMod n`. -/
theorem rationalTorsion_equiv [IsAlgClosed k] (n : ℕ) [NeZero n] (hunit : IsUnit (n : k)) :
    Nonempty
      (AddSubgroup.torsionBy (SchemeOverField.rationalPoints A) (n : ℤ) ≃+
        (Fin (2 * dimension A) → ZMod n)) := sorry

/-- In characteristic `p`, the rational `p ^ m`-torsion of an abelian variety has one fixed
rank at most its dimension for every positive exponent `m`. -/
theorem exists_pRank [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∃ f : ℕ, f ≤ dimension A ∧ ∀ m : ℕ, 1 ≤ m →
      Nonempty
        (AddSubgroup.torsionBy (SchemeOverField.rationalPoints A) ((p ^ m : ℕ) : ℤ) ≃+
          (Fin f → ZMod (p ^ m))) := sorry

end AlgebraicGeometry.AbelianVariety
