/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.Topology.Noetherian.BaseChange
public import ReasLib.RingTheory.Topology.FiniteType.Reduction
public import ReasLib.RingTheory.Topology.Adic.Hom
public import ReasLib.RingTheory.Topology.FiniteType

/-!
# Flatness under completed base change for Noetherian adic rings
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/-- Flatness of continuous homomorphisms of Noetherian adic rings is stable
under completed base change by homomorphisms of finite type on reduction,
including adicity and Noetherianity of the completed tensor product. -/
@[stacks 0GCA]
theorem isStableUnderBaseChangeBy_flat_isFiniteTypeOnReduction :
    IsLocalMorphismProperty.IsStableUnderBaseChangeBy
      (fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.Flat)
      (fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.IsFiniteTypeOnReduction) :=
  sorry

/-- Flat adic homomorphisms of Noetherian adic rings that are topologically
of finite type are stable under completed base change, including adicity and
Noetherianity of the completed tensor product. -/
@[stacks 0GCA]
theorem isStableUnderBaseChange_flat_and_isAdicHom_and_topologicallyOfFiniteType :
    IsLocalMorphismProperty.IsStableUnderBaseChange
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.Flat ∧ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType :=
  sorry

end TopologicalRing.Noetherian
