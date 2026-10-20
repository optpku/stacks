/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.Determinant.EulerFactor
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.FiniteField
public import ReasLib.AlgebraicGeometry.Scheme.Etale.ClosedPointFrobenius

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u v

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]

/-- The product of the ground-field rank with the residue degree at a closed point
is the prime-field degree of its residue field. -/
theorem residueDegree_mul_finiteFieldRank [Fintype k]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] (x : closedPoints X.left) :
    finiteFieldRank k p * X.hom.residueDegree x.1 =
      Module.finrank (ZMod p) (X.left.residueField x.1) := sorry

/-- Expanding a closed-point Euler factor by the prime-field degree of the ground
field replaces its relative residue degree by its prime-field residue degree. -/
@[stacks 03UW]
theorem expand_eulerFactor_residueDegree
    {Λ : Type u} {M : Type v} [CommRing Λ] [AddCommGroup M] [Module Λ M]
    [Module.Finite Λ M] [Module.Projective Λ M] [Fintype k]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] (x : closedPoints X.left)
    (φ : M →ₗ[Λ] M) :
    PowerSeries.expand (finiteFieldRank k p) (Module.finrank_pos (R := ZMod p) (M := k)).ne'
        (LinearMap.eulerFactor φ (X.hom.residueDegree x.1)) =
      LinearMap.eulerFactor φ (Module.finrank (ZMod p) (X.left.residueField x.1)) := sorry

end AlgebraicGeometry.SchemeOverField
