/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Topology.Adic.Hom

/-!
# Lemma 87.6.2

Composition of adic homomorphisms of pre-adic rings is adic.
-/

@[expose] public section

universe u v w

/- Lemma 87.6.2: Let `A → B` and `B → C` be continuous homomorphisms of pre-adic rings.
If `A → B` and `B → C` are adic, then `A → C` is adic. -/
@[stacks 0GXA] #check
  (RingHom.IsAdicHom.comp :
    ∀ {A : Type u} {B : Type v} {C : Type w}
      [CommRing A] [TopologicalSpace A] [TopologicalRing.IsPreadicRing A]
      [CommRing B] [TopologicalSpace B] [TopologicalRing.IsPreadicRing B]
      [CommRing C] [TopologicalSpace C] [TopologicalRing.IsPreadicRing C]
      {φ : A →+* B} {ψ : B →+* C},
      Continuous φ → Continuous ψ → φ.IsAdicHom → ψ.IsAdicHom →
        (ψ.comp φ).IsAdicHom)
