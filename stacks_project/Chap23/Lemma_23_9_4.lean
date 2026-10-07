module

public import ReasLib.RingTheory.CompleteIntersection.Local.Completion
import StacksCheckRecall

@[expose] public section

/- Lemma 23.9.4 (tag `09QD`): the regular-sequence kernel condition for a good factorization is
equivalent to the local-complete-intersection condition on the induced completion map. -/
universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]
variable {f : A →+* B}
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable (P : RingHom.GoodFactorization f)

@[stacks 09QD]
#check (RingHom.GoodFactorization.isCompleteIntersection_iff_completionMap P :
  P.IsCompleteIntersection ↔ P.completionMap.IsLocalCompleteIntersection)

end

#check @RingHom.GoodFactorization
#check @RingHom.GoodFactorization.completionMap
#check @RingHom.GoodFactorization.completionMap_eq_mapLocal
#check @RingHom.GoodFactorization.completionMap_eq
#check @RingHom.GoodFactorization.completionMap_isLocalCompleteIntersection
#check @RingHom.GoodFactorization.isCompleteIntersection_of_completionMap
