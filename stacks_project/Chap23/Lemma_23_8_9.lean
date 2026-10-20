/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.CompleteIntersection.Local.Flat

@[expose] public section

/- Lemma 23.8.9 (09Q7): for a flat local map of Noetherian local rings, the
target is a complete intersection exactly when the source and closed fiber
are complete intersections. -/
universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable (f : A →+* B) [IsLocalHom f] (h_flat : f.Flat)

@[stacks 09Q7]
#check (RingHom.CompleteIntersection.target_iff_source_and_closedFiber f h_flat :
  IsCompleteIntersectionLocalRing B ↔
    IsCompleteIntersectionLocalRing A ∧
      IsCompleteIntersectionLocalRing (f.Fiber (IsLocalRing.maximalIdeal A)))

end

#check @IsCompleteIntersectionLocalRing.target_iff_source_and_closedFiber
