/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CompleteIntersection.CompleteLocal
import StacksCheckRecall

@[expose] public section

universe u

variable (R : Type u) [CommRing R]

/- The complete-local component of Definition 23.8.5 is represented by regular-local
presentations and their regular-sequence kernel condition. -/
@[stacks 09Q3 "complete local"] #check (IsCompleteIntersectionCompleteLocalRing R : Prop)

#check @RingHom.IsLocalSurjection
#check @RingHom.RegularLocalPresentation
#check @isCompleteIntersectionCompleteLocalRing_iff
