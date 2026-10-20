module

public import ReasLib.Algebra.Amitsur.Complex
import StacksCheckRecall

@[expose] public section

universe u

/- 35.3.4.1: The augmented Amitsur complex
`0 → M → A ⊗[R] M → A ⊗[R] A ⊗[R] M → ⋯`. -/
@[stacks 023K] #check (@Algebra.Amitsur.extended :
  (R A M : Type u) → [CommRing R] → [CommRing A] → [Algebra R A] →
    [AddCommGroup M] → [Module R M] → CochainComplex (ModuleCat R) ℕ)
