module

public import ReasLib.RingTheory.AdicCompletion.RigEtale
public import ReasLib.RingTheory.Topology.Noetherian.Composition

/-!
# Composition of rig-étale homomorphisms
-/

@[expose] public section

universe u

open TopologicalRing.Noetherian RingHom

namespace TopologicalRing.Noetherian

/-- Rig-étaleness of homomorphisms of adic Noetherian topological rings is
stable under composition. -/
theorem isStableUnderComposition_rigEtale :
    IsStableUnderComposition
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigEtale :=
  sorry

end TopologicalRing.Noetherian

namespace RingHom.RigEtale

variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
variable [CommRing B] [TopologicalSpace B] [TopologicalRing.IsAdicRing B] [IsNoetherianRing B]
variable [CommRing C] [TopologicalSpace C] [TopologicalRing.IsAdicRing C] [IsNoetherianRing C]

/-- The composite of rig-étale homomorphisms of adic Noetherian topological rings
is rig-étale. -/
instance comp {φ : A →+* B} {ψ : B →+* C} [RigEtale φ] [RigEtale ψ] :
    RigEtale (ψ.comp φ) :=
  TopologicalRing.Noetherian.isStableUnderComposition_rigEtale ψ φ
    (RingHom.RigEtale.spec ψ).1 (RingHom.RigEtale.spec φ).1
    inferInstance inferInstance

end RingHom.RigEtale
