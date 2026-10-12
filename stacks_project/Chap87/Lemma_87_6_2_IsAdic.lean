/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Topology.Adic.Hom

/-!
# Adic homomorphisms of pre-adic rings

A ring homomorphism of pre-adic rings is adic when some ideal of definition of the source
induces the ambient topology on the target.
-/

@[expose] public section

universe u v

/-! This compatibility module exposes the shared adic homomorphism predicate. -/
#check
  (RingHom.IsAdicHom :
    ∀ {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A]
      [TopologicalRing.IsPreadicRing A] [CommRing B] [TopologicalSpace B]
      [TopologicalRing.IsPreadicRing B], (A →+* B) → Prop)
