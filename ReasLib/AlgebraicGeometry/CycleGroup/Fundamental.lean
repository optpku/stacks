module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Fundamental
public import ReasLib.AlgebraicGeometry.CycleGroup

/-!
# Fundamental cycles of fixed dimension

This file regards the fundamental algebraic cycle of a locally Noetherian scheme as a cycle
supported in its specified dimension.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

namespace AlgebraicCycle

/-- The fundamental cycle is supported in its specified dimension. -/
theorem fundamental_mem_dimensionSubgroup {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) (k : ℤ) :
    fundamental d k ∈ dimensionSubgroup d k := sorry

end AlgebraicCycle

namespace CycleGroup

/-- The fundamental cycle, regarded as an element of the cycle group in its dimension. -/
noncomputable def fundamental {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) (k : ℤ) : CycleGroup X d k :=
  ⟨AlgebraicCycle.fundamental d k,
    AlgebraicCycle.fundamental_mem_dimensionSubgroup d k⟩

/-- Forgetting the degree of the fundamental cycle recovers the underlying algebraic cycle. -/
theorem toAlgebraicCycle_fundamental {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) (k : ℤ) :
    toAlgebraicCycle d k (fundamental d k) = AlgebraicCycle.fundamental d k := sorry

end CycleGroup

end AlgebraicGeometry
