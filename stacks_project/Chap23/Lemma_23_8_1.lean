module

public import ReasLib.RingTheory.CompleteIntersection.CompleteLocal
import StacksCheckRecall

@[expose] public section

/- Lemma 23.8.1 (09PZ): for a Noetherian complete local ring, one regular-local presentation has
regular-sequence kernel if and only if every regular-local presentation does. -/
universe u

section

variable {A : Type u} [CommRing A] [IsCompleteLocalRing A] [IsNoetherianRing A]

@[stacks 09PZ]
#check (RingHom.RegularLocalPresentation.exists_regularSequenceKernel_iff_forall (A := A) :
  (∃ P : RingHom.RegularLocalPresentation.{u, u} A, P.IsCompleteIntersection) ↔
    ∀ P : RingHom.RegularLocalPresentation.{u, u} A, P.IsCompleteIntersection)

end

#check @RingHom.RegularLocalPresentation.nonempty
#check @RingHom.RegularLocalPresentation.regularSequenceKernel_iff_completeIntersection
#check @RingHom.RegularLocalPresentation.regularSequenceKernel
#check @RingHom.RegularLocalPresentation.regularSequenceKernel_iff
