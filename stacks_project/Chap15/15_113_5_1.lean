module

public import ReasLib.FieldTheory.Galois.IntegralClosure.Tame
import StacksCheckRecall

@[expose] public section

/-! # 15.113.5.1 (0BU3)

@stack 0BU3
-/

/-!
# 15.113.5.1

For a chosen uniformizer `π` of the localized branch, the source writes the tame character as
`σ ↦ θ_σ` modulo the branch ideal, where `σ(π) = θ_σ π`.  The reusable owner is the canonical
determinant character on inertia; its explicit quotient map is checked alongside it.  No chosen
uniformizer or representative is stored in the public API.
-/

namespace Section_15_113_5_1

/- 15.113.5.1: the tame inertia character induced by the branch action. -/
@[stacks 0BU3 "15.113.5.1: tame inertia character"]
#check (@integralClosure.Tame.character)

end Section_15_113_5_1
