/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigSmooth.ContinuousBaseChange
import StacksCheckRecall

/-!
# Rig-smoothness is stable under completed base change by adic maps
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/- Lemma 88.17.4: On arrows of `WAdm^Noeth`, the morphism property
`P φ` = "`φ` is rig-smooth" (`RingHom.RigSmooth`) is stable under base
change by `Q φ` = "`φ` is adic" (`RingHom.IsAdicHom`), in the sense of
Formal Spaces, Remark 87.21.10: if `B → A` is rig-smooth and `B → C` is
adic, then `Completed B A C` is adic Noetherian and `includeRight B A C`
is rig-smooth. -/
@[stacks 0GCL] #check
  (TopologicalRing.Noetherian.isStableUnderBaseChangeBy_rigSmooth_isAdicHom :
    IsLocalMorphismProperty.IsStableUnderBaseChangeBy
      (fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigSmooth)
      (fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.IsAdicHom))

end TopologicalRing.Noetherian
