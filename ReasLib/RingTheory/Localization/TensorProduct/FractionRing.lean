/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fraction-ring base change of modules

The canonical localization of an `S`-module at the image of the non-zero-divisors of `R` agrees
with the textbook right-tensor model over any chosen fraction ring of `R`.

@stack 05C1
-/

@[expose] public section

open scoped TensorProduct nonZeroDivisors

universe u v w x

namespace LocalizedModule

variable {R : Type u} {S : Type v} {N : Type w} {K : Type x}
variable [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]
variable [CommRing S] [Algebra R S]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- The canonical localization model for fraction-ring base change is linearly equivalent to the
textbook right-tensor model. -/
@[stacks 05C1 "canonical/textbook fraction-ring base-change comparison"]
noncomputable def fractionRingBaseChangeEquiv :
    LocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) N ≃ₗ[S]
      N ⊗[R] K :=
  IsLocalizedModule.iso (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))
      (TensorProduct.mk S (S ⊗[R] K) N 1) ≪≫ₗ
    TensorProduct.comm S (S ⊗[R] K) N ≪≫ₗ
      TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N K

/-- The comparison sends a module element with denominator one to its textbook pure tensor. -/
@[simp, stacks 05C1 "fraction-ring base-change comparison on denominator-one elements"]
theorem fractionRingBaseChangeEquiv_mk_one (n : N) :
    fractionRingBaseChangeEquiv (R := R) (S := S) (N := N) (K := K)
        (LocalizedModule.mk n 1) =
      n ⊗ₜ[R] (1 : K) := by
  simp [fractionRingBaseChangeEquiv, Algebra.TensorProduct.one_def]

end LocalizedModule
