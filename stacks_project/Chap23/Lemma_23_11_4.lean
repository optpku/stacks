module

import StacksCheckRecall
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.TorAmplitude

@[expose] public section

open CategoryTheory.DerivedCategory.DerivedTensor

/- Lemma 23.11.4 (0FJT): for a perfect map of Noetherian rings, Tor amplitude `[-1, 0]` of the
naive cotangent object is equivalent both to perfectness with that amplitude and to the map being
a local complete intersection. -/
universe u v

section

variable {A : Type u} {B : Type (max u v)} [CommRing A] [CommRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable {f : A →+* B}
variable (hperfect : f.IsPerfectRingMap)

@[stacks 0FJT "(1) iff (2)"]
#check (RingHom.IsPerfectRingMap.NaiveCotangent.hasTorAmplitudeIn_iff_isPerfect_and hperfect :
  HasTorAmplitudeIn f.naiveCotangentObject (-1) 0 ↔
    DerivedCategory.IsPerfect f.naiveCotangentObject ∧
      HasTorAmplitudeIn f.naiveCotangentObject (-1) 0)

@[stacks 0FJT "(1) iff (3)"]
#check (RingHom.IsPerfectRingMap.NaiveCotangent.hasTorAmplitudeIn_iff_lci hperfect :
  HasTorAmplitudeIn f.naiveCotangentObject (-1) 0 ↔
    f.IsLocalCompleteIntersection)

end

#check @RingHom.IsPerfectRingMap.NaiveCotangent.isPerfect_and_hasTorAmplitudeIn_iff_lci
