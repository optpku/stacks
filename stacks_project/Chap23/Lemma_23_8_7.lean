module

public import ReasLib.RingTheory.CompleteIntersection.Localization
import StacksCheckRecall

@[expose] public section

/- Lemma 23.8.7 (tag `09Q5`): a Noetherian ring is a local complete intersection exactly when
its localizations at maximal ideals are complete-intersection local rings. -/
universe u

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

@[stacks 09Q5]
#check (IsLocalCompleteIntersectionRing.iff_forall_maximal (A := A) :
  IsLocalCompleteIntersectionRing A ↔
    ∀ m : MaximalSpectrum A,
      IsCompleteIntersectionLocalRing (Localization.AtPrime m.asIdeal))

end
