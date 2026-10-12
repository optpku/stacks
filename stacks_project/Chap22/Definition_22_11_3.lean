/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Graded.Shift
import StacksCheckRecall

@[expose] public section

open GradedModule

universe w v u

section

variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]

/- Definition 22.11.3 (1) (0FQ1): for a right graded `A`-module `M`, the shift `M[k]`
has degree-`n` piece `M.grading (n + k)` and retains the right action. -/
@[stacks 0FQ1]
#check (Right.shift : Right.{0, w, v, u} 𝒜 → ℤ → Right.{0, w, v, u} 𝒜)

/- Definition 22.11.3 (2) (0FQ1): for a left graded `A`-module `M`, the shift `M[k]`
has degree-`n` piece `M.grading (n + k)` and twists the action of degree `i` by
`((i * k).negOnePow : R)`. -/
#check (Left.shift : Left.{0, w, v, u} 𝒜 → ℤ → Left.{0, w, v, u} 𝒜)

/- The reusable API exposes both translated gradings and the homogeneous left-action formula. -/
#check @Right.shift_grading
#check @Right.shift_action
#check @Right.shiftFunctor
#check @Left.shift_grading
#check @Left.shift_action_of_mem

/- The sign twist is an algebra automorphism, not an ad hoc shifted action. -/
#check @GradedAlgebra.koszulSign
#check @GradedAlgebra.koszulSign_apply_of_mem

/- The induced bimodule shifts remain available as compatibility constructions. -/
#check @Bimodule.rightShift
#check @Bimodule.rightShiftFunctor
#check @Bimodule.leftShift
#check @Bimodule.leftShiftFunctor

end
