module

import Mathlib.RingTheory.Etale.Finite
import StacksCheckRecall

universe u

/- Example 58.5.1 -/
@[stacks 0BN8] #check (CommAlgCat.FiniteEtale.equivOfIsSepClosed :
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω],
    (CommAlgCat.FiniteEtale Ω)ᵒᵖ ≌ FintypeCat)
