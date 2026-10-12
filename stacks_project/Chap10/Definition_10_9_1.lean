/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Submonoid.Defs
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.9.1

@stack 00CN
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [MulOneClass R]

/- Definition 10.9.1 (Tag 00CN) is recalled canonically by `Submonoid R`: a multiplicative subset
of `R` is exactly a subset containing `1` and closed under multiplication. -/
@[stacks 00CN "multiplicative subset owner"]
#check @Submonoid

/- Primitive data of the owner structure are its carrier together with `one_mem'` and `mul_mem'`.
Downstream API should use the canonical coercion to `Set R` and the derived theorems below. -/
@[stacks 00CN "multiplicative subset carrier"]
#check (SetLike.coe : Submonoid R → Set R)

/- Companion recall: the textbook condition `1 ∈ S` is the canonical theorem `Submonoid.one_mem`. -/
@[stacks 00CN "one belongs to a multiplicative subset"]
#check @Submonoid.one_mem

/- Companion recall: the textbook closure condition is the canonical theorem `Submonoid.mul_mem`. -/
@[stacks 00CN "multiplicative closure"]
#check @Submonoid.mul_mem

end
