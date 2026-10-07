module

public import ReasLib.RingTheory.CompleteIntersection.FormalFiber
import StacksCheckRecall

@[expose] public section

/- Remark 23.9.3 (09QC): a Noetherian local ring need not have local
complete-intersection formal fibers. -/
universe u

@[stacks 09QC]
#check (IsLocalRing.exists_noetherian_not_hasLciFormalFibers :
  ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsNoetherianRing A),
    ¬ IsLocalRing.HasLciFormalFibers A)

#check @IsLocalRing.HasLciFormalFibers
#check @IsLocalRing.not_forall_noetherian_hasLciFormalFibers
