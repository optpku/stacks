/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Idempotents.Basic
import StacksCheckRecall

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

variable (C : Type u) [Category.{v} C] [Preadditive C]

/- Definition 12.4.1 [09SG]: Mathlib models a Karoubian category by the more general canonical
class `IsIdempotentComplete`; in a preadditive category its kernel characterization is exactly the
source definition. -/
@[stacks 09SG]
#check (CategoryTheory.Idempotents.isIdempotentComplete_iff_idempotents_have_kernels C :
  IsIdempotentComplete C ↔
    ∀ (Z : C) (p : Z ⟶ Z), p ≫ p = p → HasKernel p)
