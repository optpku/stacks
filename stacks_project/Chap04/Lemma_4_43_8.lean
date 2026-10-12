/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {X₁ X₂ Y₁ Y₂ : C}
variable [ExactPairing X₁ Y₁] [ExactPairing X₂ Y₂]

/- Lemma 4.43.8: from `ExactPairing X₁ Y₁` and `ExactPairing X₂ Y₂`, so that `Y₁` and
`Y₂` are left duals of `X₁` and `X₂`, the reversed tensor product `Y₂ ⊗ Y₁` is a left dual
of `X₁ ⊗ X₂`. -/
@[stacks 0FFS "tensor product of specified left duals in reverse order"]
#check (ExactPairing.tensor : ExactPairing (X₁ ⊗ X₂) (Y₂ ⊗ Y₁))

end CategoryTheory
