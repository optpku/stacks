module

public import ReasLib.Topology.Algebra.Ring.Taut
import StacksCheckRecall

/-!
# Lemma 87.5.4

Composition of taut homomorphisms of linearly topologized rings is taut.
-/

@[expose] public section

universe u v w

namespace RingHom

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
variable [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]

/- Lemma 87.5.4: Let `A → B` and `B → C` be continuous homomorphisms of linearly
topologized rings. If `A → B` and `B → C` are taut, then `A → C` is taut. -/
@[stacks 0GX3] #check (RingHom.IsTaut.comp :
  ∀ {φ : A →+* B} {ψ : B →+* C}, Continuous φ → Continuous ψ →
    φ.IsTaut → ψ.IsTaut → (ψ.comp φ).IsTaut)

end RingHom
