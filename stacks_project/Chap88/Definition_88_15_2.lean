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

/- Definition 88.15.2: let `φ : A →+* B` be a continuous ring homomorphism
between adic Noetherian topological rings, i.e., `φ` is an arrow of
`WAdm^{Noeth}`. We say `φ` is naively rig-flat if `φ` is adic, topologically
of finite type, and satisfies the equivalent conditions of Lemma 88.15.1. -/
@[stacks 0GGM] #check (RingHom.NaiveRigFlat :
  ∀ {A B : Type u} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B], (A →+* B) → Prop)
