module

public import ReasLib.RingTheory.AdicCompletion.RigFlat
public import ReasLib.RingTheory.Topology.Noetherian.Composition

/-!
# Composition of rig-flat homomorphisms
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/-- Rig-flatness of homomorphisms of adic Noetherian topological rings is
stable under composition. -/
theorem isStableUnderComposition_rigFlat :
    IsStableUnderComposition
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigFlat :=
  sorry

end TopologicalRing.Noetherian

namespace RingHom.RigFlat

variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
variable [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicRing B] [IsNoetherianRing B]
variable [CommRing C] [TopologicalSpace C] [TopologicalRing.IsAdicRing C] [IsNoetherianRing C]

/-- The composite of rig-flat homomorphisms of adic Noetherian topological rings
is rig-flat. -/
instance comp {φ : A →+* B} {ψ : B →+* C} [hφ : RigFlat φ] [hψ : RigFlat ψ] :
    RigFlat (ψ.comp φ) :=
  TopologicalRing.Noetherian.isStableUnderComposition_rigFlat ψ φ
    (RingHom.RigFlat.spec ψ).1 (RingHom.RigFlat.spec φ).1 hψ hφ

end RingHom.RigFlat
