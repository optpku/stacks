/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall
public import ReasLib.RingTheory.Topology.Adic.Hom

/-!
# Lemma 87.6.3

If a composite of continuous homomorphisms of pre-adic rings is adic, then
the second homomorphism is adic.
-/

@[expose] public section

universe u v w

/- Lemma 87.6.3: Let `A → B` and `B → C` be continuous homomorphisms of pre-adic rings.
If `A → C` is adic, then `B → C` is adic. -/
@[stacks 0GXB]
#check
  (RingHom.IsAdicHom.of_comp :
    ∀ {A : Type u} {B : Type v} {C : Type w} [CommRing A] [TopologicalSpace A]
      [TopologicalRing.IsPreadicRing A] [CommRing B] [TopologicalSpace B]
      [TopologicalRing.IsPreadicRing B] [CommRing C] [TopologicalSpace C]
      [TopologicalRing.IsPreadicRing C] {φ : A →+* B} {ψ : B →+* C},
      Continuous φ → Continuous ψ → (ψ.comp φ).IsAdicHom → ψ.IsAdicHom)
