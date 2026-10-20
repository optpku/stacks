module

public import ReasLib.RingTheory.AdicCompletion.RigEtale
public import ReasLib.RingTheory.Topology.Noetherian.LocalMorphismProperty

/-!
# Locality of rig-étale homomorphisms
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/-- Rig-étale homomorphisms of Noetherian adic topological rings ascend along
étale-completion squares, descend along such squares with faithfully flat
target-side étale maps, and are stable under finite products of targets. -/
theorem isLocalMorphismProperty_rigEtale :
    IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigEtale :=
  sorry

end TopologicalRing.Noetherian
