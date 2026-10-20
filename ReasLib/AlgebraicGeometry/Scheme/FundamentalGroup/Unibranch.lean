module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.GenericPoint
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch

@[expose] public section
open AlgebraicGeometry CategoryTheory
universe u

namespace AlgebraicGeometry.Scheme


/-- The actual generic-point morphism induces a surjection on fundamental
groups when the scheme is irreducible and geometrically unibranch. -/
theorem genericPointInclusion_surjective
    {X : Scheme.{u}} [IrreducibleSpace X] (huni : X.isGeometricallyUnibranch) :
    Function.Surjective (genericPointFundamentalMap X) := sorry

end AlgebraicGeometry.Scheme
