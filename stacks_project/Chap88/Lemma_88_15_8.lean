/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.RingTheory.AdicCompletion.RigFlat
import StacksCheckRecall

/-!
# Descent of rig-flatness along a faithfully flat square
-/

@[expose] public section

universe u

/- Lemma 88.15.8 In a commutative square of adic Noetherian topological rings
whose arrows are adic and topologically of finite type, flatness of A →+* A',
faithful flatness of B →+* B', and rig-flatness of A' →+* B' imply rig-flatness
of A →+* B. -/
@[stacks 0GGT]
#check (RingHom.RigFlat.of_faithfullyFlat_square :
    ∀ {A B A' B' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace A'] [TopologicalSpace B']
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [TopologicalRing.IsAdicRing A'] [TopologicalRing.IsAdicRing B']
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing A'] [IsNoetherianRing B']
    (φ : A →+* B) (φ' : A' →+* B') (fA : A →+* A') (fB : B →+* B'),
    φ'.comp fA = fB.comp φ →
    φ.IsAdicHom → φ'.IsAdicHom → fA.IsAdicHom → fB.IsAdicHom →
    φ.TopologicallyFiniteType → φ'.TopologicallyFiniteType →
    fA.TopologicallyFiniteType → fB.TopologicallyFiniteType →
    fA.Flat → fB.FaithfullyFlat → RingHom.RigFlat φ' → RingHom.RigFlat φ)
