module

public import ReasLib.AlgebraicGeometry.Scheme.AffineOpen.DimensionOne
public import ReasLib.AlgebraicGeometry.Scheme.AffineOpen.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.AffineOpen.DimensionOne

/-- A finite set of points with Noetherian stalks of Krull dimension at most one in a separated
scheme with finitely many irreducible components on compact opens is contained in an affine
open. -/
theorem exists_containing_finiteSet
    {X : Scheme.{u}} [X.IsSeparated] [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (S : Set X) (hS : S.Finite)
    (hNoeth : ∀ x : X, x ∈ S → IsNoetherianRing (X.presheaf.stalk x))
    (hDim : ∀ x : X, x ∈ S → ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    ∃ U : X.affineOpens, S ⊆ ((U : X.Opens) : Set X) := sorry

end AlgebraicGeometry.Scheme.AffineOpen.DimensionOne
