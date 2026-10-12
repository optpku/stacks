/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

/- Remark 12.3.6 (1): for a binary direct-sum diagram, the inclusions are uniquely determined by
the projections. -/
@[stacks 0103] #check inl_of_isLimit

@[stacks 0103] #check inr_of_isLimit

/- Remark 12.3.6 (2): dually, the projections are uniquely determined by the inclusions. -/
@[stacks 0103] #check fst_of_isColimit

@[stacks 0103] #check snd_of_isColimit

/- Remark 12.3.6 (3): any binary biproduct satisfies the total relation, and conversely that
relation already forces the bicone to be a binary biproduct. -/
@[stacks 0103] #check IsBilimit.binary_total

@[stacks 0103] #check isBinaryBilimitOfTotal

end

end CategoryTheory
