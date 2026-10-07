module

import StacksCheckRecall
public import ReasLib.RingTheory.CompleteIntersection.Local.Flat

@[expose] public section

/- Proposition 23.8.4 (09Q2): for a flat local map of Noetherian local rings,
the target completion is a complete intersection exactly when the source and
closed-fiber completions are complete intersections. -/
universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable (f : A →+* B) [IsLocalHom f] (h_flat : f.Flat)

@[stacks 09Q2]
#check (RingHom.CompleteIntersection.completion_target_iff_source_and_closedFiber f h_flat :
  IsCompleteIntersectionCompleteLocalRing
      (AdicCompletion (IsLocalRing.maximalIdeal B) B) ↔
    IsCompleteIntersectionCompleteLocalRing
        (AdicCompletion (IsLocalRing.maximalIdeal A) A) ∧
      IsCompleteIntersectionCompleteLocalRing
        (AdicCompletion (IsLocalRing.maximalIdeal (f.Fiber (IsLocalRing.maximalIdeal A)))
          (f.Fiber (IsLocalRing.maximalIdeal A))))

end

#check @IsCompleteIntersectionLocalRing.target_iff_source_and_closedFiber
