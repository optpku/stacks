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
