/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Basic
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude

/-!
# Cotangent complex of a local complete intersection

The full cotangent complex of a local complete intersection ring map is perfect
with Tor-amplitude in `[-1, 0]`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory.DerivedTensor

universe u

namespace RingHom.CotangentComplex

/-- The full cotangent complex of a local complete intersection ring map is perfect
in the derived category of modules over the codomain, with Tor-amplitude in `[-1, 0]`. -/
theorem isPerfect_and_hasTorAmplitudeIn_of_lci {A B : Type u}
    [CommRing A] [CommRing B] {f : A →+* B} (hf : f.IsLocalCompleteIntersection) :
    DerivedCategory.IsPerfect (DerivedCategory.Q.obj (RingHom.cotangentComplex f)) ∧
      HasTorAmplitudeIn (DerivedCategory.Q.obj (RingHom.cotangentComplex f)) (-1) 0 :=
  sorry

end RingHom.CotangentComplex

namespace Algebra.CotangentComplex

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The full cotangent complex of a local complete intersection algebra is perfect
in the derived category of modules over the algebra, with Tor-amplitude in `[-1, 0]`. -/
@[stacks 08SL]
theorem isPerfect_and_hasTorAmplitudeIn_of_lci
    (hf : (algebraMap A B).IsLocalCompleteIntersection) :
    DerivedCategory.IsPerfect (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)) ∧
      HasTorAmplitudeIn (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)) (-1) 0 :=
  RingHom.CotangentComplex.isPerfect_and_hasTorAmplitudeIn_of_lci hf

/-- The full cotangent complex of a local complete intersection algebra is perfect
in the derived category of modules over the algebra. -/
theorem isPerfect_of_lci (hf : (algebraMap A B).IsLocalCompleteIntersection) :
    DerivedCategory.IsPerfect (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)) :=
  (isPerfect_and_hasTorAmplitudeIn_of_lci hf).1

/-- The full cotangent complex of a local complete intersection algebra has
Tor-amplitude in `[-1, 0]`. -/
theorem hasTorAmplitudeIn_of_lci (hf : (algebraMap A B).IsLocalCompleteIntersection) :
    HasTorAmplitudeIn (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)) (-1) 0 :=
  (isPerfect_and_hasTorAmplitudeIn_of_lci hf).2

end Algebra.CotangentComplex
