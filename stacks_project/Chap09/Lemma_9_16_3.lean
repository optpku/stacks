/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Normal.Closure
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open IntermediateField

universe u

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

variable [Algebra.IsAlgebraic F E]

/- Lemma 9.16.3: the canonical field `normalClosure F E (AlgebraicClosure E)` is the normal
closure of `E/F` inside `AlgebraicClosure E`; this is exactly the mathlib theorem
`isNormalClosure_normalClosure`. -/
@[stacks 09DT]
#check isNormalClosure_normalClosure

/- Companion check: in `AlgebraicClosure E`, the field
`normalClosure F E (AlgebraicClosure E)` is normal over `F`. -/
#check normalClosure.normal

/- Companion check: the minimality statement for the normal closure inside `AlgebraicClosure E`
is the canonical theorem `normalClosure_le_iff_of_normal`; applied to the
distinguished copy `(⊥ : IntermediateField E (AlgebraicClosure E)).restrictScalars F`, it says
that a normal intermediate field contains the normal closure exactly when it contains `E`. -/
#check normalClosure_le_iff_of_normal

/- Companion check: when `E/F` is finite, its normal closure in `AlgebraicClosure E` is finite
over `F`. -/
section

variable [FiniteDimensional F E]

#check normalClosure.is_finiteDimensional

end
