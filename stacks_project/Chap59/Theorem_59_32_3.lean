module

public import ReasLib.RingTheory.Completion.Henselian
import StacksCheckRecall

@[expose] public section

universe u

/- Theorem 59.32.3: Complete local rings are henselian. -/
@[stacks 03QG] #check (IsCompleteLocalRing.henselianLocalRing :
    ∀ {R : Type u} [CommRing R] [IsCompleteLocalRing R], HenselianLocalRing R)
