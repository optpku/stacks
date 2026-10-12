/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import StacksCheckRecall

@[expose] public section

/-!
Theorem 9.10.4 (Tag 09GT): every field has the canonical algebraic closure
`AlgebraicClosure F`.
-/

universe u

section

variable (F : Type u) [Field F]

@[stacks 09GT]
#check AlgebraicClosure
#synth IsAlgClosure F (AlgebraicClosure F)

end
