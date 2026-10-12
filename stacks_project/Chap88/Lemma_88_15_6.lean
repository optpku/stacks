/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Lemma_88_15_6_Completed

/-!
# Rig-flatness is stable under completed base change
-/

@[expose] public section

universe u

open Algebra.TensorProduct.Completed

namespace RingHom.RigFlat

/-- Lemma 88.15.6: let `φ = algebraMap A B` and `algebraMap A C` be arrows of
`WAdm^{Noeth}`. If `φ` is rig-flat and `algebraMap A C` is adic and
topologically of finite type, then `includeRight A B C : C →+* Completed A B C`
(the canonical map `C → B ⊗̂_A C`) is rig-flat. -/
@[stacks 0GGR]
theorem completedBaseChange {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [TopologicalRing.IsAdicRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [RigFlat (algebraMap A B)]
    [h_adic : Fact ((algebraMap A C).IsAdicHom)]
    [h_tft : Fact ((algebraMap A C).TopologicallyFiniteType)] :
    RigFlat (includeRight A B C) :=
  sorry

end RingHom.RigFlat
