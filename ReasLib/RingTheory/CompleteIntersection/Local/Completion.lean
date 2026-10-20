/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.LocalMap
public import ReasLib.RingTheory.CompleteIntersection.Local.GoodFactorization
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom

@[expose] public section

/-!
# Complete Intersections and Completion Maps

This leaf compares the presentation condition carried by a good factorization with the local
complete-intersection condition on the induced map between maximal-ideal completions.
-/

universe u v

open IsLocalRing

namespace RingHom.GoodFactorization

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]
variable {f : A →+* B}

/-- The map on maximal-ideal completions canonically determined by a good factorization. -/
@[stacks 09QD "completion map of a good factorization"]
noncomputable def completionMap (P : RingHom.GoodFactorization f) :
    AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B :=
  @AdicCompletion.mapLocal A B _ _ _ _ f P.isLocalHom

/-- With an ambient local-hom instance, the completion map of a good factorization is the usual
map on completions. -/
theorem completionMap_eq_mapLocal (P : RingHom.GoodFactorization f) [IsLocalHom f] :
    P.completionMap = AdicCompletion.mapLocal f := sorry

/-- The completion map depends only on the original local ring homomorphism, not on the chosen
good factorization used to supply its local-hom proof. -/
theorem completionMap_eq (P Q : RingHom.GoodFactorization f) :
    P.completionMap = Q.completionMap := sorry

section Noetherian

variable [IsNoetherianRing A] [IsNoetherianRing B]

/-- Lemma 23.9.4 (Tag 09QD): a good factorization has regular-sequence kernel if and only if
the induced map on maximal-ideal completions is a local complete intersection. -/
@[stacks 09QD]
theorem isCompleteIntersection_iff_completionMap (P : RingHom.GoodFactorization f) :
    P.IsCompleteIntersection ↔
      P.completionMap.IsLocalCompleteIntersection := sorry

/-- A complete-intersection good factorization makes the induced completion map a local complete
intersection. -/
theorem completionMap_isLocalCompleteIntersection (P : RingHom.GoodFactorization f)
    (hP : P.IsCompleteIntersection) :
    P.completionMap.IsLocalCompleteIntersection := sorry

/-- A local-complete-intersection completion map makes every good factorization a
complete-intersection factorization. -/
theorem isCompleteIntersection_of_completionMap (P : RingHom.GoodFactorization f)
    (hCompletion : P.completionMap.IsLocalCompleteIntersection) :
    P.IsCompleteIntersection := sorry

end Noetherian

end RingHom.GoodFactorization
