/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Trace.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Finite

@[expose] public section

universe u v w

namespace LinearMap.FiniteProjective

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]
  [Module.Finite A M] [Module.Projective A M]
variable {N : Type w} [AddCommGroup N] [Module A N]
  [Module.Finite A N] [Module.Projective A N]

/-- The trace of finite-projective endomorphisms is cyclic for rectangular composites. -/
theorem trace_comp_comm (φ : M →ₗ[A] N) (ψ : N →ₗ[A] M) :
    trace (φ ∘ₗ ψ) = trace (ψ ∘ₗ φ) := sorry

/-- The trace of a finite-projective endomorphism commutes with extension of scalars. -/
theorem trace_baseChange {A' : Type w} [CommRing A'] [Algebra A A']
    (φ : M →ₗ[A] M) :
    trace (φ.baseChange A') = algebraMap A A' (trace φ) := sorry

end LinearMap.FiniteProjective
