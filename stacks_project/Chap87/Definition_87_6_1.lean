module

public import ReasLib.RingTheory.Topology.Adic.Hom
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 87.6.1: a ring homomorphism `φ : A →+* B` of pre-adic topological
rings is adic if there exists an ideal of definition `I` of `A` such that the
topology on `B` is the `I`-adic topology. -/
@[stacks 0GBR] #check
  (RingHom.IsAdicHom :
    ∀ {A : Type u} {B : Type v} [CommRing A] [TopologicalSpace A]
      [TopologicalRing.IsPreadicRing A] [CommRing B] [TopologicalSpace B]
      [TopologicalRing.IsPreadicRing B], (A →+* B) → Prop)
