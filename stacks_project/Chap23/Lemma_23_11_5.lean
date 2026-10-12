/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.TorAmplitude

@[expose] public section

open CategoryTheory.DerivedCategory.DerivedTensor

/- Lemma 23.11.5 (0FJV): for a flat finitely presented ring map, Tor amplitude `[-1, 0]` of the
naive cotangent object is equivalent to perfectness with that amplitude, syntomicity, and the
local-complete-intersection property. -/
universe u v

section

variable {A : Type u} {B : Type (max u v)} [CommRing A] [CommRing B]
variable {f : A →+* B}
variable (hflat : f.Flat) (hfp : f.FinitePresentation)

@[stacks 0FJV "(1) iff (2)"]
#check (RingHom.Flat.NaiveCotangent.hasTorAmplitudeIn_iff_isPerfect_and hflat hfp :
  HasTorAmplitudeIn f.naiveCotangentObject (-1) 0 ↔
    DerivedCategory.IsPerfect f.naiveCotangentObject ∧
      HasTorAmplitudeIn f.naiveCotangentObject (-1) 0)

@[stacks 0FJV "(1) iff (3)"]
#check (RingHom.Flat.NaiveCotangent.hasTorAmplitudeIn_iff_syntomic hflat hfp :
  HasTorAmplitudeIn f.naiveCotangentObject (-1) 0 ↔ f.Syntomic)

@[stacks 0FJV "(1) iff (4)"]
#check (RingHom.Flat.NaiveCotangent.hasTorAmplitudeIn_iff_lci hflat hfp :
  HasTorAmplitudeIn f.naiveCotangentObject (-1) 0 ↔
    f.IsLocalCompleteIntersection)

@[stacks 0FJV "(2) iff (4)"]
#check (RingHom.Flat.NaiveCotangent.isPerfect_and_hasTorAmplitudeIn_iff_lci hflat hfp :
  (DerivedCategory.IsPerfect f.naiveCotangentObject ∧
      HasTorAmplitudeIn f.naiveCotangentObject (-1) 0) ↔
    f.IsLocalCompleteIntersection)

end

#check @RingHom.Syntomic.iff_isLocalCompleteIntersection_of_flat
#check @RingHom.Flat.NaiveCotangent.isPerfect_and_hasTorAmplitudeIn_iff_syntomic
