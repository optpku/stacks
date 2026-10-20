/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.LocalMorphismProperty
public import ReasLib.RingTheory.Topology.WeaklyAdmissible.BaseChange

/-!
# Stability of morphism properties under completed base change

A property of morphisms of countably indexed weakly admissible rings is stable
under base change when it passes from `algebraMap B A` to
`includeRight B A C : C →+* Completed B A C`.
-/

@[expose] public section

universe u

open Algebra.TensorProduct.Completed

namespace TopologicalRing

variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop)

namespace IsLocalMorphismProperty

#check (TopologicalRing.IsLocalMorphismProperty.IsStableUnderBaseChange :
    (∀ {A B : Type u}
      [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
      [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
      (B →+* A) → Prop) → Prop)

namespace IsStableUnderBaseChange

#check (TopologicalRing.IsLocalMorphismProperty.IsStableUnderBaseChange.iff P :
    IsStableUnderBaseChange P ↔
      ∀ {A B C : Type u}
        [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
        [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
        [CommRing C] [TopologicalSpace C] [IsWeaklyAdmissibleRing C] [IsCountablyIndexed C]
        [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C],
        P (algebraMap B A) → P (includeRight B A C))

variable {P}
variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
variable [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
variable [CommRing C] [TopologicalSpace C] [IsWeaklyAdmissibleRing C] [IsCountablyIndexed C]
variable [Algebra B A] [Algebra B C] [ContinuousSMul B A] [ContinuousSMul B C]

#check (TopologicalRing.IsLocalMorphismProperty.IsStableUnderBaseChange.of_includeRight :
    IsStableUnderBaseChange P → P (algebraMap B A) → P (includeRight B A C))

end IsStableUnderBaseChange

end IsLocalMorphismProperty

end TopologicalRing
