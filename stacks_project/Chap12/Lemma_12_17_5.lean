/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.GradedObject.Duality
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

namespace CategoryTheory.GradedObject

variable {F : Type u} [Field F]
variable {V W : GradedObject ℤ (ModuleCat F)}

/- Lemma 12.17.5 (1): the right member of an exact pairing of graded vector spaces has finite
total dimension. -/
@[stacks 0FFV] #check
  (ExactPairing.right_finiteTotalDimension :
    CategoryTheory.ExactPairing W V → FiniteTotalDimension V)

/- Lemma 12.17.5 (2): the induced pairings `W (-n) × V n → F` are nondegenerate in every
degree. -/
#check (ExactPairing.degreewiseEvaluation_nondegenerate :
  ∀ (p : CategoryTheory.ExactPairing W V) (n : ℤ),
    (ExactPairing.degreewiseEvaluation p n).Nondegenerate)

end CategoryTheory.GradedObject
