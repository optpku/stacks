/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Graded.Shift
public import ReasLib.Algebra.Module.Graded.NatToInt
import Mathlib.Tactic.CrossRefAttribute

/-!
# Integer shifts under nonnegative graded actions

Translation of an integer-indexed module grading preserves the action of a
nonnegatively graded algebra.
-/

@[expose] public section

namespace GradedModule

universe uR uA uM

variable {R : Type uR} {A : Type uA} {M : Type uM}
variable [Semiring R] [AddCommMonoid A] [Module R A]
variable [AddCommMonoid M] [Module R M] [SMul A M]

/-- A homogeneous scalar sends a translated homogeneous component to the translated component
whose degree is shifted by the scalar degree. -/
@[stacks 0B5R "homogeneous scalar membership in a translated grading"]
theorem smul_mem_shiftGrading
    (𝒜 : ℕ → Submodule R A) (ℳ : ℤ → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ]
    (k : ℤ) {i : ℕ} {j : ℤ} {a : A} {x : M}
    (ha : a ∈ 𝒜 i) (hx : x ∈ shiftGrading ℳ k j) :
    a • x ∈ shiftGrading ℳ k (i +ᵥ j) := sorry

/-- A nonnegative graded action on an integer-indexed module grading remains graded after
translating the module degrees. -/
@[stacks 0B5R "graded scalar action on a translated grading"]
instance instShiftGradingGradedSMul
    (𝒜 : ℕ → Submodule R A) (ℳ : ℤ → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ]
    (k : ℤ) : SetLike.GradedSMul 𝒜 (shiftGrading ℳ k) where
  smul_mem := fun {i} {j} {a} {x} ha hx ↦
    smul_mem_shiftGrading 𝒜 ℳ k (i := i) (j := j) (a := a) (x := x) ha hx

end GradedModule
