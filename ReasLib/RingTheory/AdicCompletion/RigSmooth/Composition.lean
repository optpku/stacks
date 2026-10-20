module

public import ReasLib.RingTheory.AdicCompletion.RigSmooth
public import ReasLib.RingTheory.Topology.Noetherian.Composition

/-!
# Composition of rig-smooth homomorphisms
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/-- Rig-smoothness of homomorphisms of adic Noetherian topological rings is
stable under composition. -/
theorem isStableUnderComposition_rigSmooth :
    IsStableUnderComposition
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigSmooth :=
  sorry

end TopologicalRing.Noetherian

namespace RingHom.RigSmooth

variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
variable [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicRing B] [IsNoetherianRing B]
variable [CommRing C] [TopologicalSpace C] [TopologicalRing.IsAdicRing C] [IsNoetherianRing C]

/-- The composite of rig-smooth homomorphisms of adic Noetherian topological rings
is rig-smooth. -/
instance comp {φ : A →+* B} {ψ : B →+* C} [hφ : RigSmooth φ] [hψ : RigSmooth ψ] :
    RigSmooth (ψ.comp φ) :=
  TopologicalRing.Noetherian.isStableUnderComposition_rigSmooth ψ φ
    (RingHom.RigSmooth.spec ψ).1 (RingHom.RigSmooth.spec φ).1 hψ hφ

end RingHom.RigSmooth
