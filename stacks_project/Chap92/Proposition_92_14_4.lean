/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.LocalCompleteIntersection
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Proposition 92.14.4. The full cotangent complex of a local complete intersection
ring map is perfect with Tor-amplitude in `[-1, 0]`. -/
@[stacks 08SL] #check
  (Algebra.CotangentComplex.isPerfect_and_hasTorAmplitudeIn_of_lci :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B],
      (algebraMap A B).IsLocalCompleteIntersection →
        DerivedCategory.IsPerfect (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)) ∧
          CategoryTheory.DerivedCategory.DerivedTensor.HasTorAmplitudeIn
            (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)) (-1) 0)
