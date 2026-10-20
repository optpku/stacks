module

public import ReasLib.RingTheory.AdicCompletion.RigFlat
public import ReasLib.RingTheory.Topology.Noetherian.LocalMorphismProperty

/-!
# Locality of rig-flat homomorphisms
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/-- Rig-flat homomorphisms of Noetherian adic topological rings ascend along
étale-completion squares, descend along such squares with faithfully flat
target-side étale maps, and are stable under finite products of targets. -/
theorem isLocalMorphismProperty_rigFlat :
    IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigFlat :=
  sorry

end TopologicalRing.Noetherian
