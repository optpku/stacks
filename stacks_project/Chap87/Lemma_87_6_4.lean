module

import StacksCheckRecall
public import ReasLib.RingTheory.Topology.Adic.Hom.Taut

/-!
# Lemma 87.6.4

A continuous adic homomorphism of pre-adic rings is taut.
-/

@[expose] public section

universe u v

/- Lemma 87.6.4: Let `φ : A →+* B` be a continuous homomorphism between pre-adic
topological rings. If `φ` is adic, then `φ` is taut. -/
@[stacks 0GXC] #check
  (RingHom.IsAdicHom.isTaut :
    ∀ {A : Type u} {B : Type v}
      [CommRing A] [TopologicalSpace A] [TopologicalRing.IsPreadicRing A]
      [CommRing B] [TopologicalSpace B] [TopologicalRing.IsPreadicRing B]
      {φ : A →+* B}, Continuous φ → φ.IsAdicHom → φ.IsTaut)
