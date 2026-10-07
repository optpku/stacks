module

public import ReasLib.RingTheory.AdicCompletion.Noetherian
import StacksCheckRecall

@[expose] public section

/-!
@stack 0316

# Noetherianity of adic completion
-/

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (I : Ideal R)

/- Lemma 10.97.6: the completion of a Noetherian ring along any ideal is Noetherian. -/
@[stacks 0316]
#check (AdicCompletion.instIsNoetherianRing I :
  IsNoetherianRing (AdicCompletion I R))

#check (inferInstance : IsNoetherianRing (AdicCompletion I R))
#check @adicCompletion_isNoetherianRing
