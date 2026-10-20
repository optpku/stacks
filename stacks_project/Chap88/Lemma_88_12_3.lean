/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.FiniteType.Reduction.Composition
import StacksCheckRecall

/-!
# Finite type on reductions is stable under composition
-/

@[expose] public section

universe u

open TopologicalRing RingHom

/- Lemma 88.12.3: Consider the property `P` on arrows of `WAdm^count` defined
in Lemma 88.12.1. Then `P` is stable under composition in the sense of
Situation 87.21.11. -/
@[stacks 0GC4] #check (TopologicalRing.isStableUnderComposition_isFiniteTypeOnReduction :
    TopologicalRing.IsStableUnderComposition
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        (φ : B →+* A) ↦ φ.IsFiniteTypeOnReduction)

variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
variable [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
variable [CommRing C] [TopologicalSpace C] [IsWeaklyAdmissibleRing C] [IsCountablyIndexed C]

#check (RingHom.IsFiniteTypeOnReduction.comp :
  ∀ {φ : B →+* A} {ψ : C →+* B} (hφcont : Continuous φ) (hψcont : Continuous ψ)
    (hφ : φ.IsFiniteTypeOnReduction) (hψ : ψ.IsFiniteTypeOnReduction),
    (φ.comp ψ).IsFiniteTypeOnReduction)
