/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.Topology.Noetherian.Composition
public import ReasLib.RingTheory.Topology.Noetherian.LocalMorphismProperty

/-!
# Locality and composition stability of flatness for Noetherian adic rings
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/-- Flatness is a local property of continuous ring homomorphisms between
Noetherian adic rings: it ascends along étale completion squares, descends along
such squares with faithfully flat target extension, and is stable under finite
products of targets. -/
@[stacks 0GC9]
theorem isLocalMorphismProperty_flat :
    IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.Flat :=
  sorry

/-- Flatness is stable under composition of continuous ring homomorphisms
between Noetherian adic rings. -/
@[stacks 0GCB]
theorem isStableUnderComposition_flat :
    IsStableUnderComposition
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.Flat :=
  sorry

end TopologicalRing.Noetherian
