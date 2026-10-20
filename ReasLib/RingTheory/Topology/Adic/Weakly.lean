module

public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Ring.Ideal
public import ReasLib.RingTheory.Topology.Adic.Complete

/-!
# Weakly pre-adic and weakly adic rings
-/

@[expose] public section

universe u

namespace TopologicalRing

section

variable {R : Type u} [CommRing R] [TopologicalSpace R]

namespace Ideal

/-- An ideal is weakly adic when the closures of its powers are open and form a
fundamental system of neighborhoods of `0`. -/
def IsWeaklyAdic [IsTopologicalRing R] (I : Ideal R) : Prop :=
  (∀ n : ℕ, IsOpen ((I ^ n).closure : Set R)) ∧
    (nhds (0 : R)).HasBasis (fun _ : ℕ ↦ True) (fun n ↦ ((I ^ n).closure : Set R))

/-- An ideal is weakly adic if and only if the closures of its powers are open and
cofinal among neighborhoods of `0`. -/
theorem isWeaklyAdic_iff [IsTopologicalRing R] (I : Ideal R) :
    IsWeaklyAdic I ↔
      (∀ n : ℕ, IsOpen ((I ^ n).closure : Set R)) ∧
        ∀ U ∈ nhds (0 : R), ∃ n : ℕ, ((I ^ n).closure : Set R) ⊆ U :=
  sorry

/-- An ideal inducing the ambient adic topology is weakly adic. -/
theorem isWeaklyAdic_of_isAdic [IsTopologicalRing R] {I : Ideal R} (hI : IsAdic I) :
    IsWeaklyAdic I :=
  sorry

end Ideal

/-- A weakly pre-adic ring is a linearly topologized topological ring for which some
ideal is weakly adic. -/
class IsWeaklyPreadicRing (R : Type u) [CommRing R] [TopologicalSpace R] : Prop
    extends IsTopologicalRing R, IsLinearTopology R R where
  /-- A weakly pre-adic ring has a weakly adic ideal. -/
  exists_ideal_isWeaklyAdic : ∃ I : Ideal R, Ideal.IsWeaklyAdic I

/-- A pre-adic ring is weakly pre-adic. -/
instance instIsWeaklyPreadicRing [IsPreadicRing R] : IsWeaklyPreadicRing R := sorry

/-- A linearly topologized topological ring is weakly pre-adic exactly when some
ideal is weakly adic. -/
theorem isWeaklyPreadicRing_iff [IsTopologicalRing R] [IsLinearTopology R R] :
    IsWeaklyPreadicRing R ↔ ∃ I : Ideal R, Ideal.IsWeaklyAdic I := sorry

/-- A linearly topologized ring is weakly pre-adic if and only if some ideal has the
closures of its powers open and cofinal among open ideals. -/
theorem isWeaklyPreadicRing_iff_exists_closure_pow
    [IsTopologicalRing R] [IsLinearTopology R R] :
    IsWeaklyPreadicRing R ↔
      ∃ I : Ideal R,
        (∀ n : ℕ, IsOpen ((I ^ n).closure : Set R)) ∧
          ∀ J : Ideal R, IsOpen (J : Set R) → ∃ n : ℕ, (I ^ n).closure ≤ J :=
  sorry

/-- A weakly adic ring is a complete separated weakly pre-adic ring. -/
class IsWeaklyAdicRing (R : Type u) [CommRing R] [TopologicalSpace R] : Prop
    extends IsWeaklyPreadicRing R where
  /-- The ambient topology is separated. -/
  isT2 : T2Space R
  /-- The ambient additive uniformity is complete. -/
  isComplete : @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R)

/-- An adic ring is weakly adic. -/
instance instIsWeaklyAdicRing [IsAdicRing R] : IsWeaklyAdicRing R := sorry

/-- A weakly adic ring is separated. -/
instance instT2SpaceOfIsWeaklyAdicRing [h : IsWeaklyAdicRing R] : T2Space R :=
  h.isT2

/-- A weakly adic ring is complete for its additive uniformity. -/
instance instCompleteSpaceOfIsWeaklyAdicRing [h : IsWeaklyAdicRing R] :
    @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R) := h.isComplete

/-- A weakly pre-adic ring is weakly adic exactly when it is separated and complete
for the additive uniformity. -/
theorem isWeaklyAdicRing_iff [IsWeaklyPreadicRing R] :
    IsWeaklyAdicRing R ↔
      T2Space R ∧ @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R) :=
  sorry

end

end TopologicalRing
