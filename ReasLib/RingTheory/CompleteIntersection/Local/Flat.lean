/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.CompleteIntersection.Local
public import ReasLib.RingTheory.RegularLocalRing.Fiber
public import ReasLib.RingTheory.RingHom.Fiber.Map

/-!
# Complete intersections under flat local maps

This leaf owns the source-and-closed-fiber criterion for a flat local map of
Noetherian local rings.
-/

@[expose] public section

open IsLocalRing

universe u v

namespace RingHom.CompleteIntersection

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- Proposition 23.8.4 (09Q2): for a flat local map, the completion of the
target is a complete intersection exactly when the completions of the source
and closed fiber are complete intersections. -/
@[stacks 09Q2]
theorem completion_target_iff_source_and_closedFiber (f : A →+* B)
    [IsLocalHom f] (h_flat : f.Flat) :
    IsCompleteIntersectionCompleteLocalRing
        (AdicCompletion (maximalIdeal B) B) ↔
      IsCompleteIntersectionCompleteLocalRing
          (AdicCompletion (maximalIdeal A) A) ∧
        IsCompleteIntersectionCompleteLocalRing
          (AdicCompletion (maximalIdeal (f.Fiber (maximalIdeal A)))
            (f.Fiber (maximalIdeal A))) := sorry

namespace Completion

/-- Under a flat local map, complete-intersection completion of the target implies the same for
the source. -/
theorem source_of_target (f : A →+* B) [IsLocalHom f] (h_flat : f.Flat)
    (hB : IsCompleteIntersectionCompleteLocalRing
      (AdicCompletion (maximalIdeal B) B)) :
    IsCompleteIntersectionCompleteLocalRing
      (AdicCompletion (maximalIdeal A) A) := sorry

/-- Under a flat local map, complete-intersection completion of the target implies the same for
the closed fiber. -/
theorem closedFiber_of_target (f : A →+* B) [IsLocalHom f] (h_flat : f.Flat)
    (hB : IsCompleteIntersectionCompleteLocalRing
      (AdicCompletion (maximalIdeal B) B)) :
    IsCompleteIntersectionCompleteLocalRing
      (AdicCompletion (maximalIdeal (f.Fiber (maximalIdeal A)))
        (f.Fiber (maximalIdeal A))) := sorry

/-- Under a flat local map, complete-intersection completions of the source and closed fiber imply
the same for the target. -/
theorem target_of_source_of_closedFiber (f : A →+* B) [IsLocalHom f]
    (h_flat : f.Flat)
    (hA : IsCompleteIntersectionCompleteLocalRing
      (AdicCompletion (maximalIdeal A) A))
    (hFiber : IsCompleteIntersectionCompleteLocalRing
      (AdicCompletion (maximalIdeal (f.Fiber (maximalIdeal A)))
        (f.Fiber (maximalIdeal A)))) :
    IsCompleteIntersectionCompleteLocalRing
      (AdicCompletion (maximalIdeal B) B) := sorry

end Completion

/-- Lemma 23.8.9 (09Q7): a flat local target is a complete intersection
exactly when the source and the closed fiber are complete intersections. -/
@[stacks 09Q7]
theorem target_iff_source_and_closedFiber (f : A →+* B)
    [IsLocalHom f] (h_flat : f.Flat) :
    IsCompleteIntersectionLocalRing B ↔
      IsCompleteIntersectionLocalRing A ∧
        IsCompleteIntersectionLocalRing (f.Fiber (maximalIdeal A)) := sorry

namespace FlatLocal

/-- A flat local map with complete-intersection target has complete-intersection source. -/
theorem source_of_target (f : A →+* B) [IsLocalHom f] (h_flat : f.Flat)
    (hB : IsCompleteIntersectionLocalRing B) :
    IsCompleteIntersectionLocalRing A := sorry

/-- A flat local map with complete-intersection target has complete-intersection closed fiber. -/
theorem closedFiber_of_target (f : A →+* B) [IsLocalHom f] (h_flat : f.Flat)
    (hB : IsCompleteIntersectionLocalRing B) :
    IsCompleteIntersectionLocalRing (f.Fiber (maximalIdeal A)) := sorry

/-- A flat local map with complete-intersection source and closed fiber has complete-intersection
target. -/
theorem target_of_source_of_closedFiber (f : A →+* B) [IsLocalHom f]
    (h_flat : f.Flat) (hA : IsCompleteIntersectionLocalRing A)
    (hFiber : IsCompleteIntersectionLocalRing (f.Fiber (maximalIdeal A))) :
    IsCompleteIntersectionLocalRing B := sorry

end FlatLocal

end RingHom.CompleteIntersection

namespace IsCompleteIntersectionLocalRing

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]

/-- The algebra-structured quotient presentation of the flat local
source-and-closed-fiber criterion. -/
theorem target_iff_source_and_closedFiber :
    IsCompleteIntersectionLocalRing B ↔
      IsCompleteIntersectionLocalRing A ∧
        IsCompleteIntersectionLocalRing
          (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) := sorry

end IsCompleteIntersectionLocalRing
