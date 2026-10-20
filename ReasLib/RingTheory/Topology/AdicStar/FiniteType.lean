module

public import ReasLib.RingTheory.Topology.AdicStar.Composition
public import ReasLib.RingTheory.Topology.Adic.Hom
public import ReasLib.RingTheory.Topology.FiniteType

/-!
# Composition of adic topologically finite-type homomorphisms of adic-star rings
-/

@[expose] public section

universe u

open TopologicalRing RingHom

namespace TopologicalRing.IsAdicStarRing

/-- The property of being adic and topologically of finite type is stable under
composition of continuous homomorphisms of adic-star rings. -/
theorem isStableUnderComposition_isAdicHom_and_topologicallyOfFiniteType :
    IsStableUnderComposition
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
        (φ : B →+* A) ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType :=
  sorry

end TopologicalRing.IsAdicStarRing

namespace RingHom

variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
variable [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
variable [CommRing C] [TopologicalSpace C] [IsAdicStarRing C]

/-- The composite of two continuous adic, topologically finite-type homomorphisms
of adic-star rings is adic and topologically of finite type. -/
theorem isAdicHom_and_topologicallyOfFiniteType_comp {φ : B →+* A} {ψ : C →+* B}
    (hφcont : Continuous φ) (hψcont : Continuous ψ)
    (hφ : φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType)
    (hψ : ψ.IsAdicHom ∧ ψ.TopologicallyOfFiniteType) :
    (φ.comp ψ).IsAdicHom ∧ (φ.comp ψ).TopologicallyOfFiniteType :=
  sorry

end RingHom
