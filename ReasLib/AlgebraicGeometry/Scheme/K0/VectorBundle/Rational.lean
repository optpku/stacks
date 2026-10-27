/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.Pullback
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators DirectSum TensorProduct Topology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.VectorBundleK0

/-- Rational pullback of vector-bundle `K₀` classes along a scheme morphism. -/
noncomputable def pullbackRational {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TensorProduct ℤ (VectorBundleK0 Y) ℚ →+ TensorProduct ℤ (VectorBundleK0 X) ℚ :=
  (LinearMap.rTensor ℚ
    (@AddMonoidHom.toIntLinearMap (VectorBundleK0 Y) (VectorBundleK0 X)
      (instCommRing Y).toAddCommGroup (instCommRing X).toAddCommGroup
      (pullback f).toAddMonoidHom)).toAddMonoidHom

/-- Rational pullback on a pure tensor is scalar extension of vector-bundle pullback. -/
theorem pullbackRational_tmul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : VectorBundleK0 Y) (q : ℚ) :
    pullbackRational f (a ⊗ₜ[ℤ] q) = pullback f a ⊗ₜ[ℤ] q :=
  sorry

/-- Rational vector-bundle pullback preserves `K₀ ⊗ Q` multiplication. -/
theorem pullbackRational_map_mul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (α β : TensorProduct ℤ (VectorBundleK0 Y) ℚ) :
    pullbackRational f (α * β) = pullbackRational f α * pullbackRational f β :=
  sorry

end AlgebraicGeometry.Scheme.VectorBundleK0
