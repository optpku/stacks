/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import ReasLib.Algebra.Module.Graded.NatToInt

/-!
# Integer extensions of naturally graded algebras

An internally `ℕ`-graded algebra has a canonical `ℤ`-grading obtained by putting every
negative-degree component equal to `⊥`.
-/

@[expose] public section

noncomputable section

universe uR uA

namespace DirectSum.Decomposition

variable {R : Type uR} {A : Type uA} [CommSemiring R] [Semiring A] [Algebra R A]

/-- The unit of a naturally graded algebra lies in degree zero after extension of the grading
from `ℕ` to `ℤ`. -/
theorem natToIntGrading_one_mem (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
    (1 : A) ∈ natToIntGrading 𝒜 (0 : ℤ) := sorry

/-- Products of homogeneous elements remain homogeneous after extension of an algebra grading
from `ℕ` to `ℤ`. -/
theorem natToIntGrading_mul_mem (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (i j : ℤ) (x y : A) (hx : x ∈ natToIntGrading 𝒜 i)
    (hy : y ∈ natToIntGrading 𝒜 j) :
    x * y ∈ natToIntGrading 𝒜 (i + j) := sorry

/-- Extending an internal natural-number grading by zero in negative degrees gives an internal
integer grading of the same algebra. -/
@[reducible, instance 100]
noncomputable instance instGradedAlgebraNatToIntGrading
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
    GradedAlgebra (natToIntGrading 𝒜) where
  one_mem := natToIntGrading_one_mem 𝒜
  mul_mem := natToIntGrading_mul_mem 𝒜
  decompose' := natToIntDecompose 𝒜
  left_inv := DFunLike.congr_fun (natToIntDecompose_left_inv 𝒜)
  right_inv := DFunLike.congr_fun (natToIntDecompose_right_inv 𝒜)

end DirectSum.Decomposition

end
