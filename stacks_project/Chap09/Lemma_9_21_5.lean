/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Normal.Closure
import StacksCheckRecall

@[expose] public section

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
variable [Algebra.IsSeparable K L]

/- Lemma 9.21.5 (Tag 0EXM): the normal closure of a separable extension `L/K` inside
`AlgebraicClosure L` is Galois over `K`; this is the algebraic-closure specialization of the
normal-ambient owner theorem. -/
@[stacks 0EXM]
#check (IntermediateField.normalClosure.isGalois_of_isSeparable :
  IsGalois K (IntermediateField.normalClosure K L (AlgebraicClosure L)))
