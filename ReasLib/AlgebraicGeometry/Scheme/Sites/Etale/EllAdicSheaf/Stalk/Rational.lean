/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Stalk.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Constructible
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

variable {X : Scheme.{u}} [IsNoetherian X] {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- Constructible geometric stalks become finite-dimensional after extending
scalars from `ℤ_[ℓ]` to `ℚ_[ℓ]`. -/
theorem finiteDimensional_qellStalk
    (F : ZEllSheaf X ℓ) (hF : F.IsConstructible) (x : GeometricPoint X) :
    FiniteDimensional ℚ_[ℓ] (F.qellStalk x) := sorry

/-- Rational geometric stalks of integral ℓ-adic sheaves are finite-dimensional. -/
instance instFiniteDimensionalQellStalk (F : ZEllSheaf X ℓ) (x : GeometricPoint X) :
    FiniteDimensional ℚ_[ℓ] (F.qellStalk x) :=
  finiteDimensional_qellStalk F F.constructible x

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
