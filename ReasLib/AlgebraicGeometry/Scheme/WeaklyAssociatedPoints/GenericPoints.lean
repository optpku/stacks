module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Support
public import ReasLib.AlgebraicGeometry.Scheme.WeaklyAssociatedPoints

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Every generic point of an irreducible component of a scheme is weakly associated to its
structure sheaf. -/
theorem genericPoints_subset_weakAss (X : Scheme.{u}) :
    genericPoints X ⊆ X.weakAss := sorry

/-- The weakly associated points of a reduced scheme are exactly its generic points. -/
theorem weakAss_eq_genericPoints (X : Scheme.{u}) [IsReduced X] :
    X.weakAss = genericPoints X := sorry

/-- A point of a reduced scheme is weakly associated exactly when it is a generic point. -/
theorem mem_weakAss_iff_mem_genericPoints (X : Scheme.{u}) [IsReduced X] (x : X) :
    x ∈ X.weakAss ↔ x ∈ genericPoints X := sorry

end AlgebraicGeometry.Scheme
