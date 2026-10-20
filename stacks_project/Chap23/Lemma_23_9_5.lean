module

public import ReasLib.RingTheory.CompleteIntersection.Local.AtPrime
import StacksCheckRecall

@[expose] public section

/- Lemma 23.9.5 (tag `09QE`): a finite-type map from a Noetherian ring is a local complete
intersection exactly when every induced map on completed local rings is one. -/
universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsNoetherianRing A]
variable (f : A →+* B) (hfinite : f.FiniteType)

@[stacks 09QE]
#check (RingHom.isLocalCompleteIntersection_iff_completedLocalMap f hfinite :
  f.IsLocalCompleteIntersection ↔
    ∀ q : PrimeSpectrum B, (f.completedLocalMap q).IsLocalCompleteIntersection)

end

#check @RingHom.completedLocalMap
