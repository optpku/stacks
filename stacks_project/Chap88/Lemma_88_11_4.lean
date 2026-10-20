/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.AdicStar.FiniteType
import StacksCheckRecall

/-!
# Adic topologically finite type arrows of WAdm^{adic*} are stable under composition
-/

@[expose] public section

universe u

open TopologicalRing RingHom

/- Lemma 88.11.4: Consider the property `P` on arrows of `WAdm^{adic*}` defined
in Lemma 88.11.1. Then `P` is stable under composition as defined in Formal
Spaces, Remark 87.21.13. -/
@[stacks 0GBZ] #check
  (TopologicalRing.IsAdicStarRing.isStableUnderComposition_isAdicHom_and_topologicallyOfFiniteType :
    TopologicalRing.IsAdicStarRing.IsStableUnderComposition
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
        (φ : B →+* A) ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType)

#check (RingHom.isAdicHom_and_topologicallyOfFiniteType_comp :
  ∀ {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
    [CommRing C] [TopologicalSpace C] [IsAdicStarRing C]
    {φ : B →+* A} {ψ : C →+* B},
    Continuous φ → Continuous ψ →
    (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) →
    (ψ.IsAdicHom ∧ ψ.TopologicallyOfFiniteType) →
    (φ.comp ψ).IsAdicHom ∧ (φ.comp ψ).TopologicallyOfFiniteType)
