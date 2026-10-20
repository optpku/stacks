module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! # Finite-dimensional first group cohomology -/

@[expose] public section

universe u

namespace groupCohomology

/-- The first cohomology of a finitely generated group with finite-dimensional
coefficients is finite-dimensional. -/
instance finiteDimensional_h1 {k Γ : Type u} [Field k] [Group Γ] [Group.FG Γ]
    (X : Rep.{u} k Γ) [FiniteDimensional k X.V] :
    FiniteDimensional k (groupCohomology.H1 X) := sorry

end groupCohomology
