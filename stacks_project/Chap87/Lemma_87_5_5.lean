/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Algebra.Ring.Taut
import StacksCheckRecall

/-!
# Lemma 87.5.5

If a composite of continuous homomorphisms of linearly topologized rings is taut, then
the second homomorphism is taut.
-/

@[expose] public section

universe u v w

/- Lemma 87.5.5: Let `A → B` and `B → C` be continuous homomorphisms of linearly
topologized rings. If `A → C` is taut, then `B → C` is taut. -/
@[stacks 0GX4]
#check
  (RingHom.IsTaut.of_comp :
    ∀ {A : Type u} {B : Type v} {C : Type w}
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
      {φ : A →+* B} {ψ : B →+* C},
      Continuous φ → Continuous ψ → (ψ.comp φ).IsTaut → ψ.IsTaut)
