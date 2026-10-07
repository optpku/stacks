module

public import ReasLib.RingTheory.Gorenstein.CompleteIntersection
import StacksCheckRecall

@[expose] public section

universe u v

namespace RingHom.IsLocalCompleteIntersection

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/- Lemma 47.21.7 -/
@[stacks 0DWA] #check
  (RingHom.IsLocalCompleteIntersection.isGorensteinRing :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsGorensteinRing A]
      {f : A →+* B}, f.IsLocalCompleteIntersection → IsGorensteinRing B)

end RingHom.IsLocalCompleteIntersection
