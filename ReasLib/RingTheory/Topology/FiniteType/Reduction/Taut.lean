module

public import ReasLib.Topology.Algebra.Ring.Taut
public import ReasLib.RingTheory.Topology.FiniteType
public import ReasLib.RingTheory.Topology.FiniteType.Reduction

/-!
# Taut topologically finite type maps are finite type on reductions
-/

@[expose] public section

universe u

open TopologicalRing

namespace RingHom.IsFiniteTypeOnReduction

/-- A continuous taut homomorphism between countably indexed weakly admissible
commutative topological rings that is topologically of finite type is of finite
type on reduction. -/
@[stacks 0GC5]
theorem of_isTaut_topologicallyOfFiniteType {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B]
    {φ : A →+* B} (hφ : Continuous φ) (h_taut : φ.IsTaut)
    (h_tft : φ.TopologicallyOfFiniteType) :
    φ.IsFiniteTypeOnReduction :=
  sorry

end RingHom.IsFiniteTypeOnReduction
