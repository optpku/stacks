/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigFlat
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 88.15.4: let `φ : A →+* B` be a continuous ring homomorphism
between adic Noetherian topological rings, i.e., `φ` is an arrow of
`WAdm^{Noeth}`. We say `φ` is rig-flat if `φ` is adic, topologically of finite
type, and for all `f ∈ A` the induced map of completed principal localizations
`completedPrincipalLocalization I f ⟶ completedPrincipalLocalization (I.map φ) (φ f)`
is naively rig-flat (Definition 88.15.2). -/
@[stacks 0GGP] #check (RingHom.RigFlat :
  ∀ {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B], (A →+* B) → Prop)
