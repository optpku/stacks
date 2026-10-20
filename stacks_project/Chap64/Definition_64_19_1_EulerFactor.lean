/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Determinant.EulerFactor

@[expose] public section

noncomputable section

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [Module.Projective R M]

#check (LinearMap.eulerFactor : (M →ₗ[R] M) → ℕ → PowerSeries R)
