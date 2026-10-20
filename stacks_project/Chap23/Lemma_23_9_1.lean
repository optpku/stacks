module

public import ReasLib.RingTheory.CompleteIntersection.Local.GoodFactorization
import StacksCheckRecall

@[expose] public section

/- Lemma 23.9.1 (09QA): for a local homomorphism of complete Noetherian
local rings, the regular-sequence kernel condition holds for some good
factorization if and only if it holds for every good factorization. -/
universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsCompleteLocalRing A] [IsCompleteLocalRing B]
variable (f : A →+* B) [IsLocalHom f]
variable [IsNoetherianRing A] [IsNoetherianRing B]

@[stacks 09QA]
#check (RingHom.GoodFactorization.exists_isCompleteIntersection_iff_forall f :
  (∃ P : RingHom.GoodFactorization.{u, v, max u v} f, P.IsCompleteIntersection) ↔
    ∀ P : RingHom.GoodFactorization.{u, v, max u v} f, P.IsCompleteIntersection)

end

#check @RingHom.GoodFactorization
#check @RingHom.GoodFactorization.ClosedFiber
#check @RingHom.GoodFactorization.IsCompleteIntersection
#check @RingHom.GoodFactorization.isCompleteIntersection_iff_of_complete
#check @RingHom.GoodFactorization.nonempty
