/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
