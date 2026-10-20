module

public import ReasLib.RingTheory.AdicCompletion.RigSmooth
public import ReasLib.RingTheory.Topology.Noetherian.BaseChange

/-!
# Rig-smoothness under completed base change by adic homomorphisms
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/-- Rig-smoothness of homomorphisms of adic Noetherian topological rings is
stable under completed base change by adic homomorphisms: if `B → A` is
rig-smooth and `B → C` is adic, then `Completed B A C` is adic Noetherian
and the canonical homomorphism `includeRight B A C` is rig-smooth. -/
@[stacks 0GCL]
theorem isStableUnderBaseChangeBy_rigSmooth_isAdicHom :
    IsLocalMorphismProperty.IsStableUnderBaseChangeBy
      (fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigSmooth)
      (fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.IsAdicHom) :=
  sorry

end TopologicalRing.Noetherian
