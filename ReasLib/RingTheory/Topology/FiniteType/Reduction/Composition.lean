/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.FiniteType.Reduction
public import ReasLib.RingTheory.Topology.WeaklyAdmissible.Composition

/-!
# Finite type on reductions is stable under composition
-/

@[expose] public section

universe u

open TopologicalRing RingHom

namespace RingHom.IsFiniteTypeOnReduction

variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
variable [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
variable [CommRing C] [TopologicalSpace C] [IsWeaklyAdmissibleRing C] [IsCountablyIndexed C]

/-- Finite type on reduction is preserved by composition of continuous morphisms
of countably indexed weakly admissible rings. -/
theorem comp {φ : B →+* A} {ψ : C →+* B} (hφcont : Continuous φ) (hψcont : Continuous ψ)
    (hφ : φ.IsFiniteTypeOnReduction) (hψ : ψ.IsFiniteTypeOnReduction) :
    (φ.comp ψ).IsFiniteTypeOnReduction :=
  sorry

end RingHom.IsFiniteTypeOnReduction

namespace TopologicalRing

/-- Finite type on reduction is a property of morphisms of countably indexed
weakly admissible rings that is stable under composition. -/
theorem isStableUnderComposition_isFiniteTypeOnReduction :
    IsStableUnderComposition
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        (φ : B →+* A) ↦ φ.IsFiniteTypeOnReduction :=
  sorry

end TopologicalRing
