module

public import ReasLib.RingTheory.CompleteIntersection.Local
import StacksCheckRecall

@[expose] public section

universe u

variable (R : Type u) [CommRing R]

/- Definition 23.8.5 (1) (09Q3): a Noetherian local ring is a complete intersection when its
completion is a complete-intersection complete local ring. -/
@[stacks 09Q3 "(1)"] #check (IsCompleteIntersectionLocalRing R : Prop)

/- Definition 23.8.5 (2) (09Q3): a Noetherian ring is a local complete intersection when every
prime localization is a complete-intersection local ring. -/
@[stacks 09Q3 "(2)"] #check (IsLocalCompleteIntersectionRing R : Prop)

#check @isCompleteIntersectionLocalRing_iff
#check @isLocalCompleteIntersectionRing_iff
