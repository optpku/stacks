/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Category.CommAlgCat.FiniteEtale
import StacksCheckRecall

universe u

/- Example 58.5.1 -/
@[stacks 0BN8] #check (CommAlgCat.FiniteEtale.equivToFintypeOfIsSepClosed :
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω],
    (CommAlgCat.FiniteEtale Ω)ᵒᵖ ≌ FintypeCat)
