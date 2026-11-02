/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Pair
public import ReasLib.LinearAlgebra.QuotientByIdeal.Projective

/-!
# Finite-projective visible power modules

For a nonzerodivisor `f`, multiplication by the visible powers of `f` identifies the relevant
power submodules with the original finite free terms.  Their reductions modulo `(f)` are therefore
finite projective over `A / (f)`.
-/

@[expose] public section

open scoped nonZeroDivisors

universe u v

namespace CochainComplex.BerthelotOgus.Nat.Pair

variable {A : Type u} [CommRing A]

/-- A visible power submodule of a free term is free. -/
theorem powerSubmodule_free_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Free A (K.X n)] (hf : f ∈ nonZeroDivisors A) :
    Module.Free A (powerSubmodule f K n) := by
  rw [powerSubmodule, principalIdeal, Submodule.ideal_span_singleton_smul,
    Submodule.pointwise_smul_def, Submodule.map_top]
  exact Module.Free.of_equiv
    (LinearEquiv.ofInjective (DistribSMul.toLinearMap A (K.X n) (f ^ n))
      ((isRegular_iff_mem_nonZeroDivisors.mpr
        ((nonZeroDivisors A).pow_mem hf n)).smul_right_injective (K.X n)))

/-- A visible power submodule of a finite term is finite. -/
theorem powerSubmodule_finite_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Finite A (K.X n)] (hf : f ∈ nonZeroDivisors A) :
    Module.Finite A (powerSubmodule f K n) := by
  rw [powerSubmodule, principalIdeal, Submodule.ideal_span_singleton_smul,
    Submodule.pointwise_smul_def, Submodule.map_top]
  infer_instance

/-- The next visible power submodule of a free term is free. -/
theorem nextPowerSubmodule_free_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Free A (K.X (n + 1))] (hf : f ∈ nonZeroDivisors A) :
    Module.Free A (nextPowerSubmodule f K n) := by
  exact powerSubmodule_free_of_nonZeroDivisor f K (n + 1) hf

/-- The next visible power submodule of a finite term is finite. -/
theorem nextPowerSubmodule_finite_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Finite A (K.X (n + 1))] (hf : f ∈ nonZeroDivisors A) :
    Module.Finite A (nextPowerSubmodule f K n) := by
  exact powerSubmodule_finite_of_nonZeroDivisor f K (n + 1) hf

end CochainComplex.BerthelotOgus.Nat.Pair

namespace CochainComplex.BerthelotOgus.Nat.Reduction.Pair

open CochainComplex.BerthelotOgus.Nat.Pair

variable {A : Type u} [CommRing A]

/-- The first reduced visible power module is finite over `A / (f)`. -/
theorem powerQuotient_finite_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Finite A (K.X n)] (hf : f ∈ nonZeroDivisors A) :
    Module.Finite (A ⧸ principalIdeal f) (powerQuotient f K n) := by
  letI := powerSubmodule_finite_of_nonZeroDivisor f K n hf
  exact Module.instFiniteQuotientByIdeal (principalIdeal f)

/-- The first reduced visible power module is projective over `A / (f)`. -/
theorem powerQuotient_projective_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Free A (K.X n)] (hf : f ∈ nonZeroDivisors A) :
    Module.Projective (A ⧸ principalIdeal f) (powerQuotient f K n) := by
  letI := powerSubmodule_free_of_nonZeroDivisor f K n hf
  exact Module.instProjectiveQuotientByIdeal (principalIdeal f)

/-- The second reduced visible power module is finite over `A / (f)`. -/
theorem nextPowerQuotient_finite_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Finite A (K.X (n + 1))] (hf : f ∈ nonZeroDivisors A) :
    Module.Finite (A ⧸ principalIdeal f) (nextPowerQuotient f K n) := by
  letI := nextPowerSubmodule_finite_of_nonZeroDivisor f K n hf
  exact Module.instFiniteQuotientByIdeal (principalIdeal f)

/-- The second reduced visible power module is projective over `A / (f)`. -/
theorem nextPowerQuotient_projective_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    [Module.Free A (K.X (n + 1))] (hf : f ∈ nonZeroDivisors A) :
    Module.Projective (A ⧸ principalIdeal f) (nextPowerQuotient f K n) := by
  letI := nextPowerSubmodule_free_of_nonZeroDivisor f K n hf
  exact Module.instProjectiveQuotientByIdeal (principalIdeal f)

end CochainComplex.BerthelotOgus.Nat.Reduction.Pair
