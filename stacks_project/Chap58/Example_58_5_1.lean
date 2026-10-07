module

import ReasLib.Algebra.Category.CommAlgCat.FiniteEtale
import StacksCheckRecall

universe u

/- Example 58.5.1 -/
@[stacks 0BN8] #check (CommAlgCat.FiniteEtale.equivToFintypeOfIsSepClosed :
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω],
    (CommAlgCat.FiniteEtale Ω)ᵒᵖ ≌ FintypeCat)
