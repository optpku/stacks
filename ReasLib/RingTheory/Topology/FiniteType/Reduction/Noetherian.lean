module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.Topology.Adic.Hom
public import ReasLib.RingTheory.Topology.FiniteType
public import ReasLib.RingTheory.Topology.FiniteType.Reduction

@[expose] public section

universe u

open TopologicalRing

namespace RingHom

/-- A continuous homomorphism between Noetherian adic rings that is of finite
type on reduction is topologically of finite type. -/
theorem topologicallyOfFiniteType_of_isFiniteTypeOnReduction {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    (φ : A →+* B) (hφ : Continuous φ) (h : φ.IsFiniteTypeOnReduction) :
    φ.TopologicallyOfFiniteType :=
  sorry

/-- An adic homomorphism between Noetherian adic rings is of finite type on
reduction if and only if it is topologically of finite type. -/
@[stacks 0GG6]
theorem isFiniteTypeOnReduction_iff_topologicallyOfFiniteType {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) :
    φ.IsFiniteTypeOnReduction ↔ φ.TopologicallyOfFiniteType :=
  sorry

end RingHom

namespace RingHom.IsFiniteTypeOnReduction

/-- An adic, topologically finite type homomorphism of Noetherian adic rings is
of finite type on reduction. -/
theorem of_isAdicHom_topologicallyOfFiniteType {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType) :
    φ.IsFiniteTypeOnReduction :=
  sorry

end RingHom.IsFiniteTypeOnReduction

namespace Algebra.TopologicallyOfFiniteType

/-- For an adic algebra map of Noetherian adic rings, finite type on reduction
is equivalent to the algebra being topologically of finite type. -/
theorem iff_isFiniteTypeOnReduction {R A : Type u}
    [CommRing R] [TopologicalSpace R] [IsAdicRing R] [IsNoetherianRing R]
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [Algebra R A] (h_adic : (algebraMap R A).IsAdicHom) :
    (algebraMap R A).IsFiniteTypeOnReduction ↔ TopologicallyOfFiniteType R A :=
  sorry

end Algebra.TopologicallyOfFiniteType
