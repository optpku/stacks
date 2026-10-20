/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigEtale.Locality
import StacksCheckRecall

/-!
# Rig-étaleness is a local morphism property of Noetherian adic rings
-/

@[expose] public section

universe u

/- Lemma 88.19.3: The property `P φ` = "`φ` is rig-étale" on arrows of
`WAdm^Noeth` is a local property as defined in Formal Spaces, Remark 87.21.5. -/
@[stacks 0AQL] #check (TopologicalRing.Noetherian.isLocalMorphismProperty_rigEtale :
  TopologicalRing.Noetherian.IsLocalMorphismProperty
    (fun {A B : Type u}
      [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
      [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicRing B] [IsNoetherianRing B]
      (φ : B →+* A) ↦ φ.RigEtale))
