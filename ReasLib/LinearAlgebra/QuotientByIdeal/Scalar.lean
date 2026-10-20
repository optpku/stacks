/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Scalar descent for modules over a quotient ring

This leaf owns the noncommutative bridge used whenever an `R`-module is already equipped with an
`R ⧸ I`-module structure compatible with the quotient map.  For commutative base rings, Mathlib's
`LinearEquiv.extendScalarsOfSurjective` is the preferred API; the declarations here retain the
two-sided quotient-ring form needed when that commutative interface is unavailable.
-/

@[expose] public section

noncomputable section

universe u v w

namespace Ideal.Quotient.Scalar

variable {R : Type u} [Ring R]

/-! The quotient action on `M ⧸ (I • ⊤)` is canonical once `I` is two-sided.  Keeping this
instance here, rather than in a construction-specific leaf, lets associated graded pieces,
homogeneous quotient pieces, and ordinary module quotients share the same scalar tower. -/

/-- The original `R`-action and the quotient-ring action on a module quotient form a scalar tower. -/
@[stacks 0523 "canonical scalar tower on an ideal module quotient", instance 100]
instance moduleTower (I : Ideal R) [I.IsTwoSided]
    (M : Type v) [AddCommGroup M] [Module R M] :
    IsScalarTower R (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) :=
  Module.IsTorsionBySet.isScalarTower
    (Module.isTorsionBySet_quotient_ideal_smul M I)

variable {I : Ideal R} [I.IsTwoSided]

/-- The original `R`-action agrees with the action through the quotient map `R → R ⧸ I`. -/
@[stacks 0523 "quotient-ring scalar action"]
theorem smul_eq_mk_smul
    {M : Type v} [AddCommGroup M] [Module (R ⧸ I) M] [Module R M]
    [IsScalarTower R (R ⧸ I) M] (r : R) (x : M) :
    r • x = (Ideal.Quotient.mk I r : R ⧸ I) • x := by
  calc
    r • x = r • ((1 : R ⧸ I) • x) := by rw [one_smul]
    _ = (r • (1 : R ⧸ I)) • x := (IsScalarTower.smul_assoc r 1 x).symm
    _ = (Ideal.Quotient.mk I r : R ⧸ I) • x := by
      congr 1
      change Ideal.Quotient.mk I (r * 1) = Ideal.Quotient.mk I r
      rw [mul_one]

end Ideal.Quotient.Scalar

namespace LinearMap

variable {R : Type u} [Ring R] {I : Ideal R} [I.IsTwoSided]

/-- An `R`-linear map between modules over a two-sided quotient respects quotient-ring scalars. -/
@[stacks 0523 "quotient-ring scalar compatibility for maps"]
theorem map_smul_of_quotient
    {M : Type v} {N : Type w} [AddCommGroup M] [Module (R ⧸ I) M] [Module R M]
    [IsScalarTower R (R ⧸ I) M] [AddCommGroup N] [Module (R ⧸ I) N] [Module R N]
    [IsScalarTower R (R ⧸ I) N] (f : M →ₗ[R] N) (c : R ⧸ I) (x : M) :
    f (c • x) = c • f x := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← Ideal.Quotient.Scalar.smul_eq_mk_smul (I := I) r x,
    f.map_smul, Ideal.Quotient.Scalar.smul_eq_mk_smul (I := I) r (f x)]

/-- Promote an `R`-linear map between modules over a two-sided quotient to a quotient-ring-linear
map. -/
@[stacks 0523 "quotient-ring linear map"]
abbrev extendScalarsOfQuotient
    {M : Type v} {N : Type w} [AddCommGroup M] [Module (R ⧸ I) M] [Module R M]
    [IsScalarTower R (R ⧸ I) M] [AddCommGroup N] [Module (R ⧸ I) N] [Module R N]
    [IsScalarTower R (R ⧸ I) N] (f : M →ₗ[R] N) : M →ₗ[R ⧸ I] N where
  toFun := f
  map_add' := f.map_add
  map_smul' := f.map_smul_of_quotient

end LinearMap

namespace LinearEquiv

variable {R : Type u} [Ring R] {I : Ideal R} [I.IsTwoSided]

/-! The commutative specialization is Mathlib's `LinearEquiv.extendScalarsOfSurjective`; this
owner retains the corresponding two-sided quotient construction over an arbitrary ring. -/
/-- Promote an `R`-linear equivalence between modules over a two-sided quotient to an
`(R ⧸ I)`-linear equivalence. -/
@[stacks 0523 "quotient-ring linear equivalence"]
noncomputable def extendScalarsOfQuotient
    {M : Type v} {N : Type w} [AddCommGroup M] [Module (R ⧸ I) M] [Module R M]
    [IsScalarTower R (R ⧸ I) M] [AddCommGroup N] [Module (R ⧸ I) N] [Module R N]
    [IsScalarTower R (R ⧸ I) N] (e : M ≃ₗ[R] N) : M ≃ₗ[R ⧸ I] N where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' := e.toLinearMap.map_smul_of_quotient

end LinearEquiv
