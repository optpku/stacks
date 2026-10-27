/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.AssociatedCycle

/-!
# Associated cycles in dimension subgroups

Associated cycles belong to their prescribed dimension subgroup for any
integer-valued degree function. Relative associated cycles are bundled as
elements of the corresponding cycle group.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

/-- The degree-`k` associated cycle of a closed subspace is supported at points
of degree `k`, for any integer-valued degree function. -/
theorem associatedCycle_mem_cycleDimensionSubgroup {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (Y : ClosedSubspace X) (d : Points X → ℤ) (k : ℤ) :
    associatedCycle Y d k ∈ cycleDimensionSubgroup d k := by
  apply (mem_cycleDimensionSubgroup d k (associatedCycle Y d k)).mpr
  intro x hx
  by_contra h
  exact hx (associatedCycle_eq_zero_of_dimension_ne Y d k h)

end ClosedSubspace

namespace Hom

/-- The multiplicity-weighted degree-`k` associated cycle of a closed subspace,
bundled in the cycle group for the relative dimension function. -/
def closedSubspaceCycleInDegree {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsLocallyNoetherian B] (f : X ⟶ B) [LocallyOfFiniteType f]
    (δ : Points B → ℤ) (Y : ClosedSubspace X) (k : ℤ) : cycleGroup f δ k :=
  ⟨@ClosedSubspace.associatedCycle S X (LocallyOfFiniteType.isLocallyNoetherian f)
      Y (relativeDimensionFunction f δ) k,
    @ClosedSubspace.associatedCycle_mem_cycleDimensionSubgroup S X
      (LocallyOfFiniteType.isLocallyNoetherian f) Y (relativeDimensionFunction f δ) k⟩

/-- The underlying locally finite function of the bundled relative associated
cycle is the canonical associated cycle with the relative dimension function. -/
theorem closedSubspaceCycleInDegree_coe {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsLocallyNoetherian B] (f : X ⟶ B) [LocallyOfFiniteType f]
    (δ : Points B → ℤ) (Y : ClosedSubspace X) (k : ℤ) :
    (closedSubspaceCycleInDegree f δ Y k : Function.locallyFinsupp (Points X) ℤ) =
      @ClosedSubspace.associatedCycle S X (LocallyOfFiniteType.isLocallyNoetherian f)
        Y (relativeDimensionFunction f δ) k :=
  rfl

end Hom

end AlgebraicGeometry.AlgebraicSpace
