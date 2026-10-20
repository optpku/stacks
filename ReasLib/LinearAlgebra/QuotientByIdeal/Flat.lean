/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.QuotientByIdeal.Tensor

@[expose] public section

/-!
# Flatness and injectivity after ideal quotients

This leaf records the universe-polymorphic exactness consequence used by both
adic-completion and localization arguments. The quotient map itself remains
the canonical `LinearMap.quotientMapByIdeal` construction.
-/

universe u v w x

namespace LinearMap

variable {R : Type u} [CommRing R]

/-- If `0 → P → Q → T → 0` is exact and `T` is flat, then the induced map on
quotients by any ideal of `R` is injective. -/
@[stacks 0315 "flat exactness after an ideal quotient"]
theorem quotientMapByIdeal_injective_of_exact_of_flat
    {P : Type v} {Q : Type w} {T : Type x}
    [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup T] [Module R T] [Module.Flat R T]
    (J : Ideal R) (φ : P →ₗ[R] Q) (ψ : Q →ₗ[R] T)
    (hφ : Function.Injective φ) (hψ : Function.Surjective ψ)
    (hExact : Function.Exact φ ψ) :
    Function.Injective (φ.quotientMapByIdeal J) := by
  rw [quotientMapByIdeal_injective_iff_lTensor_injective]
  exact LinearMap.lTensor_injective_of_exact_of_flat ψ hψ φ hφ hExact (R ⧸ J)

end LinearMap
