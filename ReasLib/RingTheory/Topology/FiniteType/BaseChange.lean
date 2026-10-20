module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Topology.FiniteType
public import ReasLib.RingTheory.Topology.Adic.Hom
public import ReasLib.RingTheory.Topology.AdicStar.BaseChange

/-!
# Completed base change of adic topologically finite type homomorphisms
-/

@[expose] public section

universe u

open TopologicalRing RingHom

namespace TopologicalRing.IsAdicStarRing

/-- Adic topologically finite type homomorphisms between adic-star rings are
stable under completed base change. -/
@[stacks 0GBY]
theorem isStableUnderBaseChange_isAdicHom_and_topologicallyOfFiniteType :
    IsLocalMorphismProperty.IsStableUnderBaseChange
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
        (φ : B →+* A) ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType :=
  sorry

end TopologicalRing.IsAdicStarRing
