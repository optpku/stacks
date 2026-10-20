/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.TorAmplitude
import StacksCheckRecall

/-!
# Lemma 15.86.4

@stack 0FV0
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.DerivedCategory.DerivedTensor

universe u v

/- Lemma 15.86.4 (0FV0): for a local complete intersection map `A → B`, the canonical naive
cotangent object `NL{B⁄A}` is perfect and has Tor-amplitude in `[-1, 0]`. -/
@[stacks 0FV0 "perfectness and Tor-amplitude of the naive cotangent complex"]
#check fun {A : Type u} {B : Type (max u v)} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : f.IsLocalCompleteIntersection) =>
  (RingHom.NaiveCotangent.isPerfect_and_hasTorAmplitudeIn_of_lci hf :
    DerivedCategory.IsPerfect f.naiveCotangentObject ∧
      HasTorAmplitudeIn f.naiveCotangentObject (-1) 0)

/- The perfectness component is available independently. -/
@[stacks 0FV0 "perfectness component"]
#check fun {A : Type u} {B : Type (max u v)} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : f.IsLocalCompleteIntersection) =>
  (RingHom.NaiveCotangent.isPerfect_of_lci hf :
    DerivedCategory.IsPerfect f.naiveCotangentObject)

/- The Tor-amplitude component is available independently. -/
@[stacks 0FV0 "Tor-amplitude component"]
#check fun {A : Type u} {B : Type (max u v)} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : f.IsLocalCompleteIntersection) =>
  (RingHom.NaiveCotangent.hasTorAmplitudeIn_of_lci hf :
    HasTorAmplitudeIn f.naiveCotangentObject (-1) 0)

end
