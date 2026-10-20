module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.Topology.KrullDimension.IrreducibleComponents

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The dimension of a Noetherian scheme is the indexed supremum of the dimensions of its
irreducible components. -/
theorem topologicalKrullDim_eq_iSup_irreducibleComponents
    (X : Scheme.{u}) [IsNoetherian X] :
    topologicalKrullDim X =
      ⨆ Z : irreducibleComponents X, topologicalKrullDim (Z : Set X) := sorry

/-- The dimension of a nonempty Noetherian scheme is attained as the maximum of the
dimensions of its irreducible components. -/
theorem isGreatest_topologicalKrullDim_irreducibleComponents
    (X : Scheme.{u}) [IsNoetherian X] [Nonempty X] :
    IsGreatest
      {d : WithBot ℕ∞ |
        ∃ Z : irreducibleComponents X, d = topologicalKrullDim (Z : Set X)}
      (topologicalKrullDim X) := sorry

end AlgebraicGeometry.Scheme
